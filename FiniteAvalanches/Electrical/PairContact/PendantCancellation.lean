import FiniteAvalanches.Electrical.PairContact.SignedLaw

/-! Crossing cancellation on the actual all-six extension returns original copied-grove counts. -/
namespace FiniteAvalanches.Electrical.PairFormula.Complete
open FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- The actual extended disk drawing cancels crossing groves; every count returns to original IDs. -/
theorem signed_difference_eq_original_grove (x : Fin 6 → V)
    (D : Drawing (J.withPendants x))
    (hvertices : ∀ v, D.point v ∈ disk) (hedges : ∀ e t, D.curve e t ∈ disk)
    (horder : cyclic_order D (Sum.inr : Fin 6 → V ⊕ Fin 6)) :
    signedGroveSum J x triple124 triple356 - signedGroveSum J x triple123 triple456 =
      (Nat.card (J.PairingGrove (x ∘ triple124) (x ∘ triple356) matching162345) : ℝ) := by
  let y : Fin 6 → V ⊕ Fin 6 := Sum.inr
  have h := signed_grove_difference (J.withPendants x) D y hvertices hedges horder
  have hs (first : Bool) :
      let U := if first then triple124 else triple123
      let W := if first then triple356 else triple456
      signedGroveSum (J.withPendants x) y U W = signedGroveSum J x U W := by
    intro U W
    apply Finset.sum_congr rfl
    intro π _
    rw [show Nat.card ((J.withPendants x).PairingGrove (y ∘ U) (y ∘ W) π) =
      Nat.card (J.PairingGrove (x ∘ U) (x ∘ W) π) from all_six_grove_count J x first π]
  have hp : Nat.card ((J.withPendants x).PairingGrove
      (y ∘ triple124) (y ∘ triple356) matching162345) =
      Nat.card (J.PairingGrove (x ∘ triple124) (x ∘ triple356) matching162345) :=
    all_six_grove_count J x true matching162345
  rw [show signedGroveSum (J.withPendants x) y triple124 triple356 = _ from hs true,
    show signedGroveSum (J.withPendants x) y triple123 triple456 = _ from hs false,hp] at h
  exact h

end
end FiniteAvalanches.Electrical.PairFormula.Complete
