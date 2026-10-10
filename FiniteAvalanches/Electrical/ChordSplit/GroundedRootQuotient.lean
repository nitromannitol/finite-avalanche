import FiniteAvalanches.Electrical.ChordSplit.AllEdgeQuotient
import Mathlib.Logic.Equiv.Option

/-! The two grounded-terminal root quotient fixes every original free vertex. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ChordSplit
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section
variable {V : Type}

/-- The free vertices of both root quotients are the same original vertices. -/
def groundedRootFreeEquiv (alpha beta : V) :
    {x : GroundedSplitVertex alpha beta //
      x ∉ (pairRoots (Sum.inr false) (Sum.inr true)).val} ≃
    {x : V // x ∉ (pairRoots alpha beta).val} where
  toFun x := match x with
    | ⟨Sum.inl v, _⟩ => ⟨v.val, by
        simpa only [pairRoots, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          using v.property⟩
    | ⟨Sum.inr false, h⟩ => False.elim (h (Or.inl rfl))
    | ⟨Sum.inr true, h⟩ => False.elim (h (Or.inr rfl))
  invFun v :=
    ⟨Sum.inl ⟨v.val, by
      simpa only [pairRoots, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        using v.property⟩, by
      rintro (h | h) <;> cases h⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl v => rfl
    | inr b =>
      cases b
      · exact (hx (Or.inl rfl)).elim
      · exact (hx (Or.inr rfl)).elim
  right_inv _ := rfl

/-- The only collapsed point is the identified root; every free value stays fixed. -/
def groundedRootVertexEquiv (alpha beta : V) :
    NonemptyQuotient.Vertex
      (pairRoots (Sum.inr false : GroundedSplitVertex alpha beta) (Sum.inr true)) ≃
    NonemptyQuotient.Vertex (pairRoots alpha beta) :=
  Equiv.optionCongr (groundedRootFreeEquiv alpha beta)

theorem groundedRootVertexEquiv_project (alpha beta : V) (x : GroundedSplitVertex alpha beta) :
    groundedRootVertexEquiv alpha beta
      (NonemptyQuotient.project (pairRoots (Sum.inr false) (Sum.inr true)) x) =
        identifyGroundedTerminals alpha beta x := by
  cases x with
  | inl v =>
    have hx : (Sum.inl v : GroundedSplitVertex alpha beta) ∉
        (pairRoots (Sum.inr false) (Sum.inr true)).val := by
      rintro (h | h) <;> cases h
    rw [NonemptyQuotient.project, dif_neg hx]
    rfl
  | inr b =>
    have hx : (Sum.inr b : GroundedSplitVertex alpha beta) ∈
        (pairRoots (Sum.inr false) (Sum.inr true)).val := by
      cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
    rw [(NonemptyQuotient.project_eq_none _ _).mpr hx]
    rfl

end
end FiniteAvalanches.Electrical.ChordSplit
