import FiniteAvalanches.Sandpile.Burning.SourceFields

/-! Heights inside the held-burning stopping set are uniform on the inner allowed
fields. By the two-phase bijection `heldFieldEquiv`, the allowed fields whose held
burning stops at `A` are the pairs of an inner allowed field on `A` and an outer allowed
field off `A`, so prescribing heights on the held set `B ⊆ A` constrains only the inner
factor. -/

set_option autoImplicit false

namespace FiniteAvalanches.Sandpile.Burning

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (U : Finset V)

/-- Allowed fields stopping at `A` with prescribed heights on `B`, as pairs with free
outer factor. -/
def heldValueEquiv (B A : Finset (InducedVertex U)) (hBA : B ⊆ A)
    (ξ : InducedVertex U → ℕ) :
    {h : Heights G U // noForbidden G U h ∧ heldBurning G U h B = A ∧
        ∀ x ∈ B, (h x).val = ξ x} ≃
      {a : {a : InnerField G U B A // InnerAllowed G U B A a} //
          ∀ x (hx : x ∈ B), (a.val ⟨x, hBA hx⟩).val = ξ x} ×
        {d : OuterField G U A // OuterAllowed G U A d} :=
  ((Equiv.subtypeEquivRight (fun _ => and_assoc.symm)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun h : Heights G U => noForbidden G U h ∧ heldBurning G U h B = A)
      (fun h : Heights G U => ∀ x ∈ B, (h x).val = ξ x)).symm).trans
    (((heldFieldEquiv G U B A hBA).subtypeEquiv
      (q := fun p => ∀ x (hx : x ∈ B), (p.1.val ⟨x, hBA hx⟩).val = ξ x)
      (fun _ => ⟨fun h x hx => h x hx, fun h x hx => h x hx⟩)).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun a : {a : InnerField G U B A // InnerAllowed G U B A a} =>
          ∀ x (hx : x ∈ B), (a.val ⟨x, hBA hx⟩).val = ξ x)))

theorem card_held_values (B A : Finset (InducedVertex U)) (hBA : B ⊆ A)
    (ξ : InducedVertex U → ℕ) :
    Nat.card {h : Heights G U // noForbidden G U h ∧ heldBurning G U h B = A ∧
        ∀ x ∈ B, (h x).val = ξ x} =
      Nat.card {a : {a : InnerField G U B A // InnerAllowed G U B A a} //
          ∀ x (hx : x ∈ B), (a.val ⟨x, hBA hx⟩).val = ξ x} *
        Nat.card {d : OuterField G U A // OuterAllowed G U A d} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (heldValueEquiv G U B A hBA ξ)

theorem card_held (B A : Finset (InducedVertex U)) (hBA : B ⊆ A) :
    Nat.card {h : Heights G U // noForbidden G U h ∧ heldBurning G U h B = A} =
      Nat.card {a : InnerField G U B A // InnerAllowed G U B A a} *
        Nat.card {d : OuterField G U A // OuterAllowed G U A d} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (heldFieldEquiv G U B A hBA)

/-- Conditional uniformity of the inner heights, as a product identity of counts. -/
theorem card_held_values_mul (B A : Finset (InducedVertex U)) (hBA : B ⊆ A)
    (ξ : InducedVertex U → ℕ) :
    Nat.card {h : Heights G U // noForbidden G U h ∧ heldBurning G U h B = A ∧
        ∀ x ∈ B, (h x).val = ξ x} *
      Nat.card {a : InnerField G U B A // InnerAllowed G U B A a} =
    Nat.card {h : Heights G U // noForbidden G U h ∧ heldBurning G U h B = A} *
      Nat.card {a : {a : InnerField G U B A // InnerAllowed G U B A a} //
          ∀ x (hx : x ∈ B), (a.val ⟨x, hBA hx⟩).val = ξ x} := by
  rw [card_held_values G U B A hBA ξ, card_held G U B A hBA]
  ring

end

end FiniteAvalanches.Sandpile.Burning
