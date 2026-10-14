import FiniteAvalanches.Wilson.Lattice.ObservedInverseContact
import FiniteAvalanches.Wilson.Lattice.NestedPrefixContacts

/-! Exact expectation transfer from completed finite observations to the genuine color law. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentObservedInverse

open LatticeProb Sandpile MeasureTheory Filter
open CurrentInverseContact CurrentNestedPrefix BatchRestart ConditionalIteration7
open scoped Classical
noncomputable section

/-- The probability of a finite observed pattern equals its genuine color-law probability. -/
theorem observed_pattern_mass (R : RootPair) (L : List (Site 2)) (F : Finset (Site 2))
    (p : contactSites F → Bool) (hD : ∀ d ∈ contactSites F, d ∈ L) :
    wilsonRows (observedPattern (initialSampler R) L F p) =
      wilsonColorLaw R (fieldPatternEvent F p) := by
  let pc : Site 2 → Bool := fun d => if hd : d ∈ contactSites F then p ⟨d, hd⟩ else false
  have hp : ∀ d : contactSites F, pc d.val = p d := by
    intro d
    exact dif_pos d.property
  rw [observedPattern_eq _ _ F p pc hp, fieldPatternEvent_eq F p pc hp]
  exact (wilsonColorLaw_apply_sampler R L (contactSites F) pc hD).symm

/-- The row-space expectation is the exact reciprocal moment of the original color law. -/
theorem integral_observedInverseContacts_eq (R : RootPair) (L : List (Site 2))
    (F : Finset (Site 2)) (hD : ∀ d ∈ contactSites F, d ∈ L) :
    (∫ ξ, observedInverseContacts R L F ξ ∂wilsonRows) =
      ∫ σ, (contacts F σ : ℝ)⁻¹ ∂wilsonColorLaw R := by
  rw [inverse_contacts_integral_partition F R]
  unfold observedInverseContacts
  rw [integral_finsetSum Finset.univ (fun p _ =>
    ((integrable_const (1 : ℝ)).indicator
      (measurable_observedPattern (initialSampler R) L F p)).const_mul _)]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [integral_const_mul, integral_indicator_const (1 : ℝ)
    (measurable_observedPattern (initialSampler R) L F p), smul_eq_mul, mul_one]
  have hm := observed_pattern_mass R L F p hD
  rw [Measure.real, hm]
  rfl

/-- Actual source query coverage supplies the expectation dictionary at every positive scale. -/
theorem integral_source_observed_inverse_eq (R : RootPair) (K : Finset (Site 2))
    (b : ℕ) (hb : 6 ≤ b) (i : ℕ) (hi : 1 ≤ i) :
    (∫ ξ, observedInverseContacts R (stagePrefix b i) (sourceWindow K b i) ξ ∂wilsonRows) =
      ∫ σ, (contacts (sourceWindow K b i) σ : ℝ)⁻¹ ∂wilsonColorLaw R :=
  integral_observedInverseContacts_eq R (stagePrefix b i) (sourceWindow K b i)
    (fun d hd => source_and_contact_queried K b hb i hi d (Finset.mem_union_right _ hd))

end
end FiniteAvalanches.Wilson.Lattice.CurrentObservedInverse
