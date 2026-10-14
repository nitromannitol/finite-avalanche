import FiniteAvalanches.Electrical.Geometry.PolarDual
import FiniteAvalanches.Electrical.Plane.VoltageCuts
import FiniteAvalanches.External.PlaneDualBondCycle
import FiniteAvalanches.External.PlaneDualConnected

/-! Voltage cuts on actual augmented complement faces, retaining original edge IDs. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LovaszPhysical
open StatementGeometry Source BSST
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- Induced connectedness yields copied walks in the augmented drawing without using the battery. -/
theorem augmented_reaches_of_induce (J : CopiedGraph V E) (alpha beta : V)
    (U : Set V) (hc : ((supportGraph J.left J.right).induce U).Preconnected)
    (x y : V) (hx : x ∈ U) (hy : y ∈ U) :
    (augmentedGraph J alpha beta).reaches
      (Finset.univ.filter fun z =>
        (augmentedGraph J alpha beta).left z ∈ U ∧
        (augmentedGraph J alpha beta).right z ∈ U) x y := by
  have walks {u v : U} (p : ((supportGraph J.left J.right).induce U).Walk u v) :
      (augmentedGraph J alpha beta).reaches
        (Finset.univ.filter fun z =>
          (augmentedGraph J alpha beta).left z ∈ U ∧
          (augmentedGraph J alpha beta).right z ∈ U) u.val v.val := by
    induction p with
    | nil => exact Relation.ReflTransGen.refl
    | @cons u v w huv p ih =>
      obtain ⟨_,e,he⟩ := huv
      have hmem : (.inl e : E ⊕ Unit) ∈ Finset.univ.filter (fun z =>
          (augmentedGraph J alpha beta).left z ∈ U ∧
          (augmentedGraph J alpha beta).right z ∈ U) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        rcases he with ⟨hl,hr⟩ | ⟨hr,hl⟩
        · exact ⟨hl ▸ u.property,hr ▸ v.property⟩
        · exact ⟨hl ▸ v.property,hr ▸ u.property⟩
      exact (Relation.ReflTransGen.single ⟨.inl e,hmem,he⟩).trans ih
  obtain ⟨p⟩ := hc ⟨x,hx⟩ ⟨y,hy⟩
  exact walks p

/-- Removing the battery from an augmented cut leaves exactly the original crossing IDs. -/
def originalCutEquiv (J : CopiedGraph V E) (alpha beta : V) (phi : V → ℝ) (t : ℝ) :
    {z : E ⊕ Unit // z ≠ .inr () ∧
      (((augmentedGraph J alpha beta).left z ∈ Finset.univ.filter (fun x => phi x < t) ∧
        (augmentedGraph J alpha beta).right z ∉ Finset.univ.filter (fun x => phi x < t)) ∨
       ((augmentedGraph J alpha beta).right z ∈ Finset.univ.filter (fun x => phi x < t) ∧
        (augmentedGraph J alpha beta).left z ∉ Finset.univ.filter (fun x => phi x < t)))} ≃
      {e : E // e ∈ Plane.crossingEdges J.left J.right phi t} where
  toFun z := by
    rcases z with ⟨e,he⟩
    cases e with
    | inl e =>
      refine ⟨e,?_⟩
      simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_lt,
        augmentedGraph,Sum.elim_inl,Plane.mem_crossingEdges] using he.2
    | inr u => cases u; exact (he.1 rfl).elim
  invFun e := ⟨.inl e.val,Sum.inl_ne_inr,by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_lt,
      augmentedGraph,Sum.elim_inl,Plane.mem_crossingEdges] using e.property⟩
  left_inv z := by
    rcases z with ⟨e,he⟩
    cases e with
    | inl e => rfl
    | inr u => cases u; exact (he.1 rfl).elim
  right_inv e := rfl

/-- Each entry of the original-ID equivalence is the very same augmented edge copy. -/
theorem originalCutEquiv_symm_val (J : CopiedGraph V E) (alpha beta : V)
    (phi : V → ℝ) (t : ℝ) (e : {e : E // e ∈ Plane.crossingEdges J.left J.right phi t}) :
    ((originalCutEquiv J alpha beta phi t).symm e).val = .inl e.val := rfl

/-- A generic voltage slice gives a simple path of actual faces through all original crossing copies.
The endpoint and row orientations are stated exactly as supplied by the bond-cycle input. -/
theorem physical_voltage_cut_path (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hgeneric : ∀ x, phi x ≠ t) :
    ∃ m : ℕ, ∃ vertices : Fin (m+1) → A.embedding.Face,
      Function.Injective vertices ∧
      ∃ copies : Fin m ≃ {e : E // e ∈ Plane.crossingEdges J.left J.right phi t},
        (∀ i : Fin m,
          (A.embedding.rightFace (.inl (copies i).val) = vertices i.castSucc ∧
            A.embedding.leftFace (.inl (copies i).val) = vertices i.succ) ∨
          (A.embedding.leftFace (.inl (copies i).val) = vertices i.castSucc ∧
            A.embedding.rightFace (.inl (copies i).val) = vertices i.succ)) ∧
        ((polarGround A = vertices 0 ∧ polarSource A = vertices (Fin.last m)) ∨
          (polarSource A = vertices 0 ∧ polarGround A = vertices (Fin.last m))) := by
  let S : Finset V := Finset.univ.filter fun x => phi x < t
  have hS (x : V) : x ∈ S ↔ phi x < t := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
  have hnS (x : V) : x ∉ S ↔ t < phi x := by
    rw [hS,not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (hgeneric x).symm,fun h => h.le⟩
  obtain ⟨hl,hu⟩ := (Plane.voltage_range_and_levels J.left J.right alpha beta hc phi hp0 hp1 hh).2 t ht0 ht1
  have inside : ∀ x y : V, x ∈ S → y ∈ S →
      (augmentedGraph J alpha beta).reaches
        (Finset.univ.filter fun z => (augmentedGraph J alpha beta).left z ∈ S ∧
          (augmentedGraph J alpha beta).right z ∈ S) x y := by
    intro x y hx hy
    simpa only [hS,Set.mem_setOf_eq] using augmented_reaches_of_induce J alpha beta
      {x | phi x < t} hl.preconnected x y ((hS x).mp hx) ((hS y).mp hy)
  have outside : ∀ x y : V, x ∉ S → y ∉ S →
      (augmentedGraph J alpha beta).reaches
        (Finset.univ.filter fun z => (augmentedGraph J alpha beta).left z ∉ S ∧
          (augmentedGraph J alpha beta).right z ∉ S) x y := by
    intro x y hx hy
    simpa only [hnS,Set.mem_setOf_eq] using augmented_reaches_of_induce J alpha beta
      {x | t < phi x} hu.preconnected x y ((hnS x).mp hx) ((hnS y).mp hy)
  have hbattery :
      ((augmentedGraph J alpha beta).left (.inr ()) ∈ S ∧
        (augmentedGraph J alpha beta).right (.inr ()) ∉ S) ∨
      ((augmentedGraph J alpha beta).right (.inr ()) ∈ S ∧
        (augmentedGraph J alpha beta).left (.inr ()) ∉ S) := by
    apply Or.inl
    constructor
    · exact (hS alpha).mpr (hp0 ▸ ht0)
    · exact (hnS beta).mpr (hp1 ▸ ht1)
  obtain ⟨m,vertices,hinj,copies,_hcard,hrows,hends⟩ :=
    FiniteAvalanches.External.finite_plane_dual_bond_cycle (augmentedGraph J alpha beta)
      A.embedding.drawing A.embedding.edgeChart S inside outside (.inr ()) hbattery
  let originals := copies.trans (originalCutEquiv J alpha beta phi t)
  have hcopy (i : Fin m) : (copies i).val = .inl (originals i).val := by
    have h := originalCutEquiv_symm_val J alpha beta phi t (originals i)
    simpa only [originals,Equiv.trans_apply,Equiv.symm_apply_apply] using h
  refine ⟨m,vertices,hinj,originals,?_,hends⟩
  intro i
  have hi := hrows i
  change (A.embedding.rightFace (copies i).val = vertices i.castSucc ∧
      A.embedding.leftFace (copies i).val = vertices i.succ) ∨
    (A.embedding.leftFace (copies i).val = vertices i.castSucc ∧
      A.embedding.rightFace (copies i).val = vertices i.succ) at hi
  rw [hcopy i] at hi
  exact hi

/-- The physical normalization determines at most one stream, independently of square packing. -/
theorem physical_stream_unique (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (A : OuterArc D alpha beta) (phi : V → ℝ) (psi chi : A.embedding.Face → ℝ)
    (hpsi : stream_spec D alpha beta A phi psi) (hchi : stream_spec D alpha beta A phi chi) :
    psi = chi := by
  letI : Nonempty (E ⊕ Unit) := ⟨.inr ()⟩
  have haug : (supportGraph (augmentedGraph J alpha beta).left
      (augmentedGraph J alpha beta).right).Preconnected :=
    hc.mono (by
      intro x y h
      obtain ⟨hne,e,he⟩ := h
      exact ⟨hne,.inl e,he⟩)
  have hd := FiniteAvalanches.External.finite_plane_dual_connected
    (augmentedGraph J alpha beta) A.embedding.drawing A.embedding.edgeChart haug
  have hedge (z : E ⊕ Unit) :
      (psi-chi) (A.embedding.rightFace z) = (psi-chi) (A.embedding.leftFace z) := by
    cases z with
    | inl e =>
      have hp := hpsi.1 e
      have hq := hchi.1 e
      simp only [Pi.sub_apply]
      linarith only [hp,hq]
    | inr u =>
      cases u
      have hp := hpsi.2.1
      have hq := hchi.2.1
      simp only [Pi.sub_apply]
      linarith only [hp,hq]
  funext F
  have he := eq_of_reachable A.embedding.rightFace A.embedding.leftFace (psi-chi)
    hedge (hd F (polarGround A))
  have hz : (psi-chi) (polarGround A) = 0 := by
    simp only [polarGround,Pi.sub_apply,hpsi.2.2.1,hchi.2.2.1,sub_self]
  rw [hz] at he
  exact sub_eq_zero.mp he

end
end FiniteAvalanches.Electrical.LovaszPhysical

#print axioms FiniteAvalanches.Electrical.LovaszPhysical.physical_voltage_cut_path
#print axioms FiniteAvalanches.Electrical.LovaszPhysical.physical_stream_unique
