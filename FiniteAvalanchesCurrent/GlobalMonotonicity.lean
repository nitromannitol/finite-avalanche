import FiniteAvalanches.Paper.Current.GlobalContactMonotonicity

set_option autoImplicit false
namespace FiniteAvalanches.Paper.CurrentSource
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- The color law and every unordered extended contact law have the same order. -/
theorem global_monotonicity
    (A A' Γ Γ' : Set (Site 2)) (hA : A.Nonempty) (hΓ' : Γ'.Nonempty)
    (hzero : A ⊆ A') (hone : Γ' ⊆ Γ)
    (hdR : Disjoint A Γ) (hdQ : Disjoint A' Γ')
    (hR : (A ∪ Γ)ᶜ.Finite) (hQ : (A' ∪ Γ')ᶜ.Finite) :
    let R : RootPair := ⟨A, Γ, hdR, hA, hΓ'.mono hone⟩
    let Q : RootPair := ⟨A', Γ', hdQ, hA.mono hzero, hΓ'⟩
    (∀ (E : Set ColorField), MeasurableSet E →
      (∀ p ∈ E, ∀ q : ColorField, (∀ x, p x = true → q x = true) → q ∈ E) →
      (wilsonColorLaw Q).real E ≤ (wilsonColorLaw R).real E) ∧
    (∀ (V : Set (Site 2)) (D : Set ℝ≥0∞), MeasurableSet D →
      (∀ n ∈ D, ∀ m : ℝ≥0∞, n ≤ m → m ∈ D) →
      (wilsonColorLaw Q).real {σ | unorderedContacts V σ ∈ D} ≤
        (wilsonColorLaw R).real {σ | unorderedContacts V σ ∈ D}) := by
  constructor
  · exact Current.source_four_sets_global_mono A A' Γ Γ' hA hΓ' hzero hone hdR hdQ hR hQ
  · exact Current.source_unordered_contact_event_mono A A' Γ Γ' hA hΓ' hzero hone hdR hdQ hR hQ

end
end FiniteAvalanches.Paper.CurrentSource
