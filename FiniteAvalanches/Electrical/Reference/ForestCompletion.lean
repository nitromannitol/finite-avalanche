import FiniteAvalanches.Electrical.Reference.CopyTransport
import FiniteAvalanches.Electrical.Reference.ColorMarginal
import FiniteAvalanches.Electrical.Geometry.SourceHDual
import FiniteAvalanches.Trees.ConnectorCompletion

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open StatementGeometry
open Plane.SourceLattice
open scoped Classical
noncomputable section
local instance primalCopyDecidable (D : Finset (Site 2)) (P : OneSet D) :
    DecidableEq (PrimalCopy D P) := Classical.decEq _
local instance sourceCopyDecidable (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) := Classical.decEq _

/-- Joining the roots by the actual marked copy completes precisely the original H0 forests. -/
theorem source_forest_completion_iff (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : Finset (Copy D P marked)) :
    (StatementTypes.graph D P marked).is_rooted_forest
      ({alpha D P, beta D P} : Set (Vertex D P)) F ↔
    ((Set.univ : Set (Vertex D P)).Nonempty ∧
      (∀ x y, (primalGraph D P).reaches
        (insert (markedPrimal D P marked) (F.image (retainedPrimal D P marked))) x y) ∧
      ∀ e ∈ insert (markedPrimal D P marked) (F.image (retainedPrimal D P marked)),
        ¬(primalGraph D P).reaches
          ((insert (markedPrimal D P marked) (F.image (retainedPrimal D P marked))).erase e)
          ((primalGraph D P).left e) ((primalGraph D P).right e)) := by
  let G : Trees.Multigraph (Vertex D P) (PrimalCopy D P) :=
    ⟨(primalGraph D P).left, (primalGraph D P).right, primal_loopless D P⟩
  let K : CopiedGraph (Vertex D P) (Copy D P marked) :=
    ⟨copyA D P marked, copyB D P marked⟩
  let f := retainedPrimal D P marked
  have hf : Function.Injective f := retainedPrimal_injective D P marked
  let z := markedPrimal D P marked
  let R : Set (Vertex D P) := {alpha D P, beta D P}
  have reach := CopiedGraph.reaches_image_iff (primalGraph D P) K f
    (fun _ => rfl) (fun _ => rfl)
  have lift : (StatementTypes.graph D P marked).is_rooted_forest R F ↔
      G.is_rooted_forest R (F.image f) := by
    unfold Trees.Multigraph.is_rooted_forest Trees.Multigraph.is_forest
    dsimp only [Trees.Multigraph.reaches, Trees.Multigraph.adjacent]
    constructor
    · rintro ⟨ht, hc⟩
      refine ⟨?_, ?_⟩
      · intro e he h
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
        apply ht a ha
        rw [← Finset.image_erase hf] at h
        change K.reaches (F.erase a) (K.left a) (K.right a)
        exact (reach (F.erase a) (K.left a) (K.right a)).mp h
      · intro x
        obtain ⟨r, hr, hx, hu⟩ := hc x
        exact ⟨r, hr, (reach F x r).mpr hx,
          fun r' hr' hx' => hu r' hr' ((reach F x r').mp hx')⟩
    · rintro ⟨ht, hc⟩
      refine ⟨?_, ?_⟩
      · intro a ha h
        apply ht (f a) (Finset.mem_image_of_mem f ha)
        rw [← Finset.image_erase hf]
        apply (reach (F.erase a) (K.left a) (K.right a)).mpr
        change K.reaches (F.erase a) (K.left a) (K.right a) at h
        exact h
      · intro x
        obtain ⟨r, hr, hx, hu⟩ := hc x
        exact ⟨r, hr, (reach F x r).mp hx,
          fun r' hr' hx' => hu r' hr' ((reach F x r').mpr hx')⟩
  have hends : (G.left z = alpha D P ∧ G.right z = beta D P) ∨
      (G.right z = alpha D P ∧ G.left z = beta D P) := by
    rcases marked.property with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  have hH : G.is_tree R {z} := by
    refine ⟨⟨alpha D P, Or.inl rfl⟩, ?_, ?_, ?_⟩
    · intro e he
      have hez := Finset.mem_singleton.mp he
      subst e
      rcases hends with h | h
      · exact ⟨Or.inl h.1, Or.inr h.2⟩
      · exact ⟨Or.inr h.2, Or.inl h.1⟩
    · intro x hx y hy
      have step : G.reaches {z} (alpha D P) (beta D P) :=
        .single ⟨z, Finset.mem_singleton_self _, hends⟩
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact .refl
      · exact step
      · exact G.reaches_symm step
      · exact .refl
    · intro e he h
      have hez := Finset.mem_singleton.mp he
      subst e
      have hh : G.left z = G.right z := by
        rw [Finset.erase_singleton] at h
        have emptyEq {x y : Vertex D P} (hp : G.reaches ∅ x y) : x = y := by
          induction hp with
          | refl => rfl
          | tail _ hadj _ => exact (Finset.notMem_empty _ hadj.choose_spec.1).elim
        exact emptyEq h
      exact G.loopless z hh
  have hdis : Disjoint ({z} : Finset (PrimalCopy D P)) (F.image f) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hf
    exact retainedPrimal_ne_marked D P marked a
      (ha.trans (Finset.mem_singleton.mp he))
  have h := lift.trans (G.rootedForest_iff_connector_union_tree R {z} (F.image f)
    (by simpa only [] using hH) (by simpa only [] using hdis))
  have tree : G.is_tree Set.univ ({z} ∪ F.image f) ↔
      ((Set.univ : Set (Vertex D P)).Nonempty ∧
        (∀ x y, (primalGraph D P).reaches (insert z (F.image f)) x y) ∧
        ∀ e ∈ insert z (F.image f), ¬(primalGraph D P).reaches
          ((insert z (F.image f)).erase e) ((primalGraph D P).left e)
          ((primalGraph D P).right e)) := by
    rw [Finset.singleton_union]
    constructor
    · intro ht
      exact ⟨ht.1, fun x y => ht.2.2.1 x (Set.mem_univ _) y (Set.mem_univ _), ht.2.2.2⟩
    · rintro ⟨hn, hc, ht⟩
      exact ⟨hn, fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩,
        fun x _ y _ => hc x y, ht⟩
  exact h.trans tree

/-- Complementation retains exactly the absent original nonmarked IDs. -/
theorem source_completion_complement (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : Finset (Copy D P marked)) :
    (insert (markedPrimal D P marked) (F.image (retainedPrimal D P marked)))ᶜ =
      Fᶜ.image (retainedPrimal D P marked) := by
  ext e
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro he
    have hem : e ≠ markedPrimal D P marked := fun h => he (Or.inl h)
    obtain ⟨a, rfl⟩ := (retainedPrimal_covers D P marked e).mpr hem
    exact ⟨a, fun ha => he (Or.inr ⟨a, ha, rfl⟩), rfl⟩
  · rintro ⟨a, ha, rfl⟩ (he | ⟨b, hb, hba⟩)
    · exact retainedPrimal_ne_marked D P marked a he
    · exact ha ((retainedPrimal_injective D P marked hba) ▸ hb)

/-- The source beta component is the complement of the alpha component on every actual forest. -/
theorem source_forest_beta_iff (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceMoment.Forest D P marked) (x : Vertex D P) :
    (StatementTypes.graph D P marked).reaches F.val x (beta D P) ↔
      ¬(StatementTypes.graph D P marked).reaches F.val (alpha D P) x := by
  let G := StatementTypes.graph D P marked
  have hn : alpha D P ≠ beta D P := by intro h; cases h
  have hsep : ¬G.reaches F.val (alpha D P) (beta D P) := by
    intro h
    obtain ⟨r, _, _, hu⟩ := F.property.2 (alpha D P)
    exact hn ((hu (alpha D P) (Or.inl rfl) .refl).trans
      (hu (beta D P) (Or.inr rfl) h).symm)
  constructor
  · intro hx ha
    exact hsep (ha.trans hx)
  · intro ha
    obtain ⟨r, hr, hx, _⟩ := F.property.2 x
    rcases hr with rfl | rfl
    · exact (ha (G.reaches_symm hx)).elim
    · exact hx
end
end FiniteAvalanches.Electrical.LatticeDrawing
