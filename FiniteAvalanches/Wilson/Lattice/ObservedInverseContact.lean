import FiniteAvalanches.Wilson.Lattice.InverseContactMoment

/-! The finite observed-pattern inverse moment as a genuine conditional expectation. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentObservedInverse

open LatticeProb Sandpile MeasureTheory Filter
open CurrentInverseContact BatchRestart ConditionalIteration7
open scoped Classical
noncomputable section

/-- The finite weighted observation of the literal completed contact pattern. -/
def observedInverseContacts (R : RootPair) (L : List (Site 2)) (F : Finset (Site 2)) : Rows → ℝ :=
  fun ξ => ∑ p : contactSites F → Bool, (patternContacts F p : ℝ)⁻¹ *
    (observedPattern (initialSampler R) L F p).indicator (fun _ => (1 : ℝ)) ξ

theorem integrable_observedInverseContacts (R : RootPair) (L : List (Site 2))
    (F : Finset (Site 2)) : Integrable (observedInverseContacts R L F) wilsonRows := by
  apply integrable_finsetSum
  intro p _hp
  exact ((integrable_const (1 : ℝ)).indicator
    (measurable_observedPattern (initialSampler R) L F p)).const_mul _

/-- On a genuine observed pattern, the finite weighted observation is its actual inverse count. -/
theorem observedInverseContacts_of_pattern (R : RootPair) (L : List (Site 2))
    (F : Finset (Site 2)) (p : contactSites F → Bool) (ξ : Rows)
    (hp : ξ ∈ observedPattern (initialSampler R) L F p) :
    observedInverseContacts R L F ξ = (patternContacts F p : ℝ)⁻¹ := by
  unfold observedInverseContacts
  rw [Finset.sum_eq_single p]
  · rw [Set.indicator_of_mem hp, mul_one]
  · intro q _hq hqp
    have hnot : ξ ∉ observedPattern (initialSampler R) L F q := by
      intro hq
      exact Set.disjoint_left.mp (observed_patterns_disjoint (initialSampler R) L F p q
        (Ne.symm hqp)) hp hq
    rw [Set.indicator_of_notMem hnot, mul_zero]
  · intro h
    exact (h (Finset.mem_univ p)).elim

/-- Linearity converts the existing finite conditional moment to one real conditional expectation. -/
theorem conditional_observedInverseContacts (R : RootPair) (L Q : List (Site 2))
    (ξ₀ : Rows) (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (F : Finset (Site 2))
    (hD : ∀ d ∈ contactSites F, d ∈ out.covered ∨ d ∈ Q) :
    ∀ᵐ ξ ∂wilsonRows, ξ ∈ historyAtom R L out →
      (wilsonRows[observedInverseContacts R (L ++ Q) F | fullHistory R L]) ξ =
        ∫ σ, (contacts F σ : ℝ)⁻¹ ∂wilsonColorLaw (restartedRoots R L ξ₀ out hs) := by
  have hlin := condExp_finsetSum (μ := wilsonRows) (s := Finset.univ)
    (f := fun p : contactSites F → Bool => (patternContacts F p : ℝ)⁻¹ •
      (observedPattern (initialSampler R) (L ++ Q) F p).indicator (fun _ => (1 : ℝ)))
    (fun p _ => ((integrable_const (1 : ℝ)).indicator
      (measurable_observedPattern (initialSampler R) (L ++ Q) F p)).smul _) (fullHistory R L)
  have hsmul : ∀ᵐ ξ ∂wilsonRows, ∀ p : contactSites F → Bool,
      (wilsonRows[(patternContacts F p : ℝ)⁻¹ •
        (observedPattern (initialSampler R) (L ++ Q) F p).indicator (fun _ => (1 : ℝ)) |
        fullHistory R L]) ξ =
      (patternContacts F p : ℝ)⁻¹ *
        (wilsonRows[(observedPattern (initialSampler R) (L ++ Q) F p).indicator
          (fun _ => (1 : ℝ)) | fullHistory R L]) ξ := by
    apply ae_all_iff.mpr
    intro p
    exact condExp_smul (patternContacts F p : ℝ)⁻¹ _ _
  have hm := conditional_inverse_contacts_known R L Q ξ₀ out hs F hD
  filter_upwards [hlin, hsmul, hm] with ξ hl hs' hm' hhist
  calc
    (wilsonRows[observedInverseContacts R (L ++ Q) F | fullHistory R L]) ξ =
      ∑ p : contactSites F → Bool,
        (wilsonRows[(patternContacts F p : ℝ)⁻¹ •
          (observedPattern (initialSampler R) (L ++ Q) F p).indicator (fun _ => (1 : ℝ)) |
          fullHistory R L]) ξ := by
      have hfun : (∑ p : contactSites F → Bool, (patternContacts F p : ℝ)⁻¹ •
          (observedPattern (initialSampler R) (L ++ Q) F p).indicator (fun _ => (1 : ℝ))) =
          observedInverseContacts R (L ++ Q) F := by
        funext η
        simp only [observedInverseContacts, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hfun] at hl
      simpa only [Finset.sum_apply] using hl
    _ = ∑ p : contactSites F → Bool, (patternContacts F p : ℝ)⁻¹ *
        (wilsonRows[(observedPattern (initialSampler R) (L ++ Q) F p).indicator
          (fun _ => (1 : ℝ)) | fullHistory R L]) ξ := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact hs' p
    _ = _ := hm' hhist

end
end FiniteAvalanches.Wilson.Lattice.CurrentObservedInverse
