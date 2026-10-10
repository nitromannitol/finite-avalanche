import FiniteAvalanches.Electrical.Geometry.BSST
import FiniteAvalanches.Electrical.Plane.Incidences
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Finite.Lemmas
import Lean

namespace FiniteAvalanches.Electrical.PhysicalVertexRange13
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open scoped Classical BigOperators
noncomputable section

private theorem walk_value_bound {W I : Type*} (a b : I → W)
    (f : W → ℝ) (s : ℝ) (hstep : ∀ e, |f (a e)-f (b e)| ≤ s)
    {u v : W} (p : (supportGraph a b).Walk u v) :
    |f u-f v| ≤ p.length*s := by
  induction p with
  | nil => simp
  | @cons u w v h p ih =>
    change |f u-f v| ≤ ((p.length+1 : ℕ) : ℝ)*s
    obtain ⟨_,e,he⟩ := h
    have hlocal : |f u-f w| ≤ s := by
      rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hstep e
      · rw [abs_sub_comm]; exact hstep e
    calc
      _ = |(f u-f w)+(f w-f v)| := by congr 1; ring
      _ ≤ |f u-f w|+|f w-f v| := abs_add_le _ _
      _ ≤ s+p.length*s := add_le_add hlocal ih
      _ = ((p.length+1 : ℕ) : ℝ)*s := by
        rw [Nat.cast_add,Nat.cast_one]; ring

/-- An actual simple path uses at most one link per original copied ID.
Parallel copies and loops remain in the original finite budget. -/
theorem linked_values_le_copy_card {W I : Type*} [Fintype I]
    (a b : I → W) (f : W → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hstep : ∀ e, |f (a e)-f (b e)| ≤ s) (u v : W)
    (hlink : Relation.ReflTransGen
      (fun z w => ∃ e : I, z ∈ ({a e,b e} : Set W) ∧ w ∈ ({a e,b e} : Set W)) u v) :
    |f u-f v| ≤ (Fintype.card I : ℝ)*s := by
  have hr : (supportGraph a b).Reachable u v := by
    induction hlink with
    | refl => rfl
    | @tail w z h hz ih =>
      obtain ⟨e,hw,hz⟩ := hz
      by_cases heq : w=z
      · simpa only [heq] using ih
      · apply ih.trans
        apply SimpleGraph.Adj.reachable
        refine ⟨heq,e,?_⟩
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw hz
        rcases hw with hw | hw <;> rcases hz with hz | hz
        · exact (heq (hw.trans hz.symm)).elim
        · exact Or.inl ⟨hw.symm,hz.symm⟩
        · exact Or.inr ⟨hw.symm,hz.symm⟩
        · exact (heq (hw.trans hz.symm)).elim
  obtain ⟨p⟩ := hr
  let q := p.toPath.val
  have hq : q.IsPath := p.toPath.property
  let copies : Finset (Sym2 W) := Finset.univ.image (fun e : I => s(a e,b e))
  have hsub : q.edges.toFinset ⊆ copies := by
    intro z hz
    induction z using Sym2.ind with
    | h x y =>
      have hadj := q.adj_of_mem_edges (List.mem_toFinset.mp hz)
      obtain ⟨_,e,he⟩ := hadj
      apply Finset.mem_image.mpr
      rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨e,Finset.mem_univ _,rfl⟩
      · exact ⟨e,Finset.mem_univ _,Sym2.eq_swap⟩
  have hlength : q.length ≤ Fintype.card I := by
    calc
      q.length = q.edges.toFinset.card := by
        rw [List.toFinset_card_of_nodup hq.isTrail.edges_nodup,SimpleGraph.Walk.length_edges]
      _ ≤ copies.card := Finset.card_le_card hsub
      _ ≤ Fintype.card I := (Finset.card_image_le).trans (by simp)
  exact (walk_value_bound a b f s hstep q).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hlength) hs)

/-- The number of incident original IDs is bounded by the literal incidence degree.
A loop is one copied ID and two incidences. -/
theorem incident_copy_card_le_degree {V E : Type} [Fintype E]
    (J : CopiedGraph V E) (x : V) :
    (Fintype.card {e : E // J.left e=x ∨ J.right e=x} : ℝ) ≤
      Geometry.degree J.left J.right x := by
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum,Finset.sum_filter]
  unfold Geometry.degree
  apply Finset.sum_le_sum
  intro e _
  by_cases ha : J.left e=x <;> by_cases hb : J.right e=x <;> norm_num [ha,hb]

/-- INTERNAL numerical application on the actual physical faces. The only link premise
is actual original-edge face-star reachability, not a range estimate or cyclic order. -/
theorem internal_physical_pair_le_degree {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J) (alpha beta : V)
    (A : Source.OuterArc D alpha beta) (phi : V → ℝ) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A phi psi) (x : V)
    (hfaces : ∀ e : E, edgeFaces A.embedding.drawing (.inl e) =
      {A.embedding.leftFace (.inl e),A.embedding.rightFace (.inl e)})
    (s : ℝ) (hs : 0 ≤ s)
    (hcurrent : ∀ e : E, J.left e=x ∨ J.right e=x →
      |phi (J.left e)-phi (J.right e)| ≤ s)
    (F G : A.embedding.Face)
    (hlink : Relation.ReflTransGen
      (fun B C : A.embedding.Face => ∃ e : E, (J.left e=x ∨ J.right e=x) ∧
        B ∈ edgeFaces A.embedding.drawing (.inl e) ∧ C ∈ edgeFaces A.embedding.drawing (.inl e)) F G) :
    |psi F-psi G| ≤ Geometry.degree J.left J.right x*s := by
  let I := {e : E // J.left e=x ∨ J.right e=x}
  let a : I → A.embedding.Face := fun e => A.embedding.leftFace (.inl e.val)
  let b : I → A.embedding.Face := fun e => A.embedding.rightFace (.inl e.val)
  have hstep (e : I) : |psi (a e)-psi (b e)| ≤ s := by
    rw [show psi (a e)-psi (b e)=phi (J.left e.val)-phi (J.right e.val) from hpsi.1 e.val]
    exact hcurrent e.val e.property
  have hl : Relation.ReflTransGen
      (fun B C => ∃ e : I, B ∈ ({a e,b e} : Set A.embedding.Face) ∧ C ∈ ({a e,b e} : Set A.embedding.Face)) F G := by
    exact Relation.ReflTransGen.mono (r := fun B C : A.embedding.Face => ∃ e : E,
      (J.left e=x ∨ J.right e=x) ∧ B ∈ edgeFaces A.embedding.drawing (.inl e) ∧
        C ∈ edgeFaces A.embedding.drawing (.inl e))
      (p := fun B C : A.embedding.Face => ∃ e : I,
        B ∈ ({a e,b e} : Set A.embedding.Face) ∧ C ∈ ({a e,b e} : Set A.embedding.Face)) (by
      intro B C h
      obtain ⟨e,he,hB,hC⟩ := h
      exact ⟨⟨e,he⟩,by simpa only [a,b,hfaces e] using hB,by simpa only [a,b,hfaces e] using hC⟩) F G hlink
  exact (linked_values_le_copy_card a b psi s hs hstep F G hl).trans
    (mul_le_mul_of_nonneg_right (incident_copy_card_le_degree J x) hs)

/-- INTERNAL exact physical range bound, after the finite connected incident star is supplied.
No minimum, maximum, range bound or drawing-to-Euler conclusion is a premise. -/
theorem internal_physical_span_le_four_largest {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J) (alpha beta : V)
    (A : Source.OuterArc D alpha beta) (phi : V → ℝ) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A phi psi) (x : V)
    (hx : (Plane.incidenceDarts J.left J.right x).Nonempty)
    (hdeg : Geometry.degree J.left J.right x ≤ 4)
    (hfaces : ∀ e : E, edgeFaces A.embedding.drawing (.inl e) =
      {A.embedding.leftFace (.inl e),A.embedding.rightFace (.inl e)})
    (hfinite : {F : A.embedding.Face | incident A.embedding.drawing x F}.Finite)
    (hne : {F : A.embedding.Face | incident A.embedding.drawing x F}.Nonempty)
    (hstar : ∀ F G : A.embedding.Face, incident A.embedding.drawing x F →
      incident A.embedding.drawing x G → Relation.ReflTransGen
        (fun B C : A.embedding.Face => ∃ e : E, (J.left e=x ∨ J.right e=x) ∧
          B ∈ edgeFaces A.embedding.drawing (.inl e) ∧ C ∈ edgeFaces A.embedding.drawing (.inl e)) F G) :
    sSup (incidentValues A.embedding.drawing psi x)-sInf (incidentValues A.embedding.drawing psi x) ≤
      4*Plane.largestCurrent J.left J.right phi x hx := by
  let s := Plane.largestCurrent J.left J.right phi x hx
  have hs : 0 ≤ s := Plane.largestCurrent_nonneg J.left J.right phi x hx
  have hcurrent (e : E) (he : J.left e=x ∨ J.right e=x) :
      |phi (J.left e)-phi (J.right e)| ≤ s := by
    rcases he with he | he
    · exact Plane.current_le_largestCurrent J.left J.right phi x hx (e,false) he
    · have hbnd := Plane.current_le_largestCurrent J.left J.right phi x hx (e,true) he
      change |phi (J.right e)-phi (J.left e)| ≤ s at hbnd
      rwa [abs_sub_comm] at hbnd
  obtain ⟨F,hF,hmin⟩ := Set.exists_min_image _ psi hfinite hne
  obtain ⟨G,hG,hmax⟩ := Set.exists_max_image _ psi hfinite hne
  have hlo : sInf (incidentValues A.embedding.drawing psi x)=psi F := by
    apply IsLeast.csInf_eq
    refine ⟨⟨F,hF,rfl⟩,?_⟩
    rintro y ⟨H,hH,rfl⟩
    exact hmin H hH
  have hhi : sSup (incidentValues A.embedding.drawing psi x)=psi G := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨G,hG,rfl⟩,?_⟩
    rintro y ⟨H,hH,rfl⟩
    exact hmax H hH
  rw [hhi,hlo]
  have hpair := internal_physical_pair_le_degree J D alpha beta A phi psi hpsi x hfaces s hs
    hcurrent G F (hstar G F hG hF)
  exact ((le_abs_self _).trans hpair).trans
    (mul_le_mul_of_nonneg_right hdeg hs)

end
end FiniteAvalanches.Electrical.PhysicalVertexRange13

set_option pp.proofs false in
#print FiniteAvalanches.Electrical.PhysicalVertexRange13.internal_physical_span_le_four_largest

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,_) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "UNEXPECTED_CLOSURE {name}: {ax}"
      logInfo m!"OWNED_CLOSURE {name}: {axs.toList}"
      count := count+1
  logInfo m!"RANGE13_ALL_OWNED_CLOSURES={count}"
