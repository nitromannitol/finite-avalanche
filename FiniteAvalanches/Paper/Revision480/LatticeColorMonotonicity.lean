import FiniteAvalanches.Paper.Revision480.GlobalColorMonotonicity

set_option autoImplicit false
namespace FiniteAvalanches.Paper.Revision480.ActualSource
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- The four sets and minimal nonempty assumptions in the current source statement. -/
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
  dsimp only
  exact color_event_mono_cofinite _ _ hR hQ hzero hone E hE hup

end
end FiniteAvalanches.Paper.Revision480.ActualSource
