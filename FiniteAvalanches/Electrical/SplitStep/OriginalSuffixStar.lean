import FiniteAvalanches.Electrical.SplitStep.ActualEnergy

/-! The entire alpha1 star is exactly the original suffix-copy family. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ChordSplit
open Source
open scoped Classical
noncomputable section
variable {V E : Type}

theorem groundMap_eq_true (alpha beta : V) (x : SplitVertex alpha) :
    groundMap alpha beta x = Sum.inr true ↔ x = Sum.inr true := by
  cases x with
  | inl v =>
    by_cases h : v.val = beta
    · simp only [groundMap, dif_pos h, Sum.inr.injEq, Sum.inl_ne_inr]
      decide
    · simp only [groundMap, dif_neg h, Sum.inl_ne_inr]
  | inr b => simp only [groundMap, Sum.inr.injEq]

theorem groundedEndpoint_eq_true (alpha beta : V) (side : E → Bool) (x : V) (e : E) :
    groundMap alpha beta (splitEndpoint alpha side x e) = Sum.inr true ↔
      x = alpha ∧ side e = true :=
  (groundMap_eq_true alpha beta _).trans
    (SplitStep.splitEndpoint_eq_true alpha side x e)

end
end FiniteAvalanches.Electrical.ChordSplit

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Plane.SourceLattice ChordSplit
open scoped Classical
noncomputable section

local instance originalSuffixStarCopyDec (D : Finset (Site 2))
    (P : OneSet D) (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) :=
  Classical.decEq _

local instance originalSuffixStarVertexDec (D : Finset (Site 2)) (P : OneSet D) :
    DecidableEq (Vertex D P) := Classical.decEq _

/-- Incidence at alpha1 characterizes precisely the same original suffix IDs. -/
theorem original_grounded_star_iff (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (i : ℕ) (e : Copy D P marked) :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    (K.left e = Sum.inr true ∨ K.right e = Sum.inr true) ↔
      ∃ k : Fin m, i ≤ k.val ∧ (copies k).val = e := by
  intro K
  have hl : K.left e = Sum.inr true ↔
      copyA D P marked e = alpha D P ∧ boundarySide _ _ _ copies i e = true :=
    groundedEndpoint_eq_true _ _ _ _ _
  have hr : K.right e = Sum.inr true ↔
      copyB D P marked e = alpha D P ∧ boundarySide _ _ _ copies i e = true :=
    groundedEndpoint_eq_true _ _ _ _ _
  rw [hl, hr]
  constructor
  · intro h
    have ha : copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P :=
      h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    have hs : boundarySide _ _ _ copies i e = true := h.elim And.right And.right
    let k := copies.symm ⟨e, ha⟩
    have he : (copies k).val = e := congrArg Subtype.val (copies.apply_symm_apply ⟨e, ha⟩)
    rw [← he, boundarySide_copy, decide_eq_true_eq] at hs
    exact ⟨k, hs, he⟩
  · rintro ⟨k, hk, rfl⟩
    have hs := boundarySide_suffix _ _ _ copies i k hk
    exact (copies k).property.elim
      (fun ha => Or.inl ⟨ha, hs⟩) (fun hb => Or.inr ⟨hb, hs⟩)

/-- Alpha1 has no loop, including when an original suffix copy goes directly to beta. -/
theorem original_grounded_no_loop_at_true (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (i : ℕ) (e : Copy D P marked) :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    ¬(K.left e = Sum.inr true ∧ K.right e = Sum.inr true) := by
  intro K h
  have ha := (groundedEndpoint_eq_true (alpha D P) (beta D P)
    (boundarySide _ _ _ copies i) (copyA D P marked e) e).mp h.1
  have hb := (groundedEndpoint_eq_true (alpha D P) (beta D P)
    (boundarySide _ _ _ copies i) (copyB D P marked e) e).mp h.2
  exact copy_loopless D P marked e (ha.1.trans hb.1.symm)

/-- Equality of the full incident-copy set with the complete suffix-image set. -/
theorem original_grounded_star_eq_suffix (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    Finset.univ.filter (fun e => K.left e = Sum.inr true ∨ K.right e = Sum.inr true) =
      ((Finset.univ : Finset (Fin m)).filter (fun k => i ≤ k.val)).image
        (fun k => (copies k).val) := by
  intro K
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  exact original_grounded_star_iff D P marked copies i e

end
end FiniteAvalanches.Electrical.SplitStep
