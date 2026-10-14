import FiniteAvalanches.Paper.Current.GlobalContactMonotonicity
import FiniteAvalanches.Paper.Revision480.LatticeColorMonotonicity

/-! Exact root operations in df176f2c main.tex:230. The retained roots, new
roots and recolored old roots are identified before using the reviewed law. -/
set_option autoImplicit false
namespace FiniteAvalanches.Paper.CurrentDF176
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- Literal removal, addition and recoloring sets in the current proof. -/
theorem root_operations_dictionary
    (A A' Γ Γ' : Set (Site 2)) (hzero : A ⊆ A') (hone : Γ' ⊆ Γ)
    (hdR : Disjoint A Γ) (hdQ : Disjoint A' Γ') :
    let C := Γ ∩ (A' ∪ Γ')
    Γ \ (Γ \ (A' ∪ Γ')) = C ∧
    A' \ C = A ∪ (A' \ (A ∪ Γ)) ∧
    C \ Γ' = Γ ∩ A' ∧
    (A' \ C) ∪ C = A' ∪ Γ' := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    ext x
    have hz : x ∈ A → x ∈ A' := fun hx => hzero hx
    have ho : x ∈ Γ' → x ∈ Γ := fun hx => hone hx
    have hr : x ∈ A → x ∉ Γ := fun hx => Set.disjoint_left.mp hdR hx
    have hq : x ∈ A' → x ∉ Γ' := fun hx => Set.disjoint_left.mp hdQ hx
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union]
    tauto

/-- Each actual intermediate union is cofinite; the sparse naive pair is unused. -/
theorem root_operations_cofinite
    (A A' Γ Γ' : Set (Site 2))
    (hR : (A ∪ Γ)ᶜ.Finite) (hQ : (A' ∪ Γ')ᶜ.Finite) (hone : Γ' ⊆ Γ) :
    let C := Γ ∩ (A' ∪ Γ')
    (A ∪ C)ᶜ.Finite ∧ ((A' \ C) ∪ C)ᶜ.Finite := by
  dsimp only
  have hm : (A ∪ Γ ∩ (A' ∪ Γ'))ᶜ.Finite := by
    apply (hR.union hQ).subset
    intro x hx
    by_cases hxr : x ∈ A ∪ Γ
    · right
      intro hxq
      apply hx
      rcases hxr with hxa | hxg
      · exact Or.inl hxa
      · exact Or.inr ⟨hxg, hxq⟩
    · exact Or.inl hxr
  refine ⟨hm, ?_⟩
  apply hQ.subset
  intro x hx hq
  apply hx
  rcases hq with ha | hg
  · by_cases hc : x ∈ Γ ∩ (A' ∪ Γ')
    · exact Or.inr hc
    · exact Or.inl ⟨ha, hc⟩
  · exact Or.inr ⟨hone hg, Or.inr hg⟩

/-- The immutable actual-source type, supplied by the cofinite remove/add/recolor proof. -/
theorem source_four_sets_global_mono
    (A A' Γ Γ' : Set (Site 2)) (hA : A.Nonempty) (hΓ' : Γ'.Nonempty)
    (hzero : A ⊆ A') (hone : Γ' ⊆ Γ)
    (hdR : Disjoint A Γ) (hdQ : Disjoint A' Γ')
    (hR : (A ∪ Γ)ᶜ.Finite) (hQ : (A' ∪ Γ')ᶜ.Finite)
    (E : Set ColorField) (hE : MeasurableSet E)
    (hup : ∀ p ∈ E, ∀ q : ColorField,
      (∀ x, p x = true → q x = true) → q ∈ E) :
    let R : RootPair := ⟨A, Γ, hdR, hA, hΓ'.mono hone⟩
    let Q : RootPair := ⟨A', Γ', hdQ, hA.mono hzero, hΓ'⟩
    (wilsonColorLaw Q).real E ≤ (wilsonColorLaw R).real E := by
  exact FiniteAvalanches.Paper.Current.source_four_sets_global_mono
    A A' Γ Γ' hA hΓ' hzero hone hdR hdQ hR hQ E hE hup

end
end FiniteAvalanches.Paper.CurrentDF176

open Lean Elab Command in
run_cmd do
  let frozen ← getConstInfo
    `FiniteAvalanches.Paper.Revision480.ActualSource.source_four_sets_global_mono
  let provider ← getConstInfo
    `FiniteAvalanches.Paper.CurrentDF176.source_four_sets_global_mono
  unless frozen.type == provider.type do
    throwError "Exact actual-source/provider type mismatch"
  logInfo "EXACT_ACTUAL_SOURCE_TYPE: structurally identical elaborated expressions"

#print axioms FiniteAvalanches.Paper.CurrentDF176.root_operations_dictionary
#print axioms FiniteAvalanches.Paper.CurrentDF176.root_operations_cofinite
#print axioms FiniteAvalanches.Paper.CurrentDF176.source_four_sets_global_mono
