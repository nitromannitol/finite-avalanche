import FiniteAvalanches.Wilson.Lattice.InverseContactMoment
import FiniteAvalanches.Wilson.Lattice.ReciprocalContactMonotonicity
import FiniteAvalanches.Wilson.Lattice.ConfinedRestartedRoots

/-! Inverse-contact contraction for the actual restarted law of a completed prefix. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentInverseContraction

open LatticeProb Sandpile MeasureTheory Filter
open CurrentInverseContact CurrentNestedPrefix BatchRestart ConditionalIteration7
open scoped Classical
noncomputable section

/-- A lower tail bound and an almost-sure cap give the inverse-moment contraction. -/
theorem inverse_contacts_integral_le (R : RootPair) (F : Finset (Site 2))
    (z t p : ℝ) (hz : 0 ≤ z) (ht : 0 < t)
    (hcap : ∀ᵐ σ ∂wilsonColorLaw R, (1 : ℝ) / (contacts F σ : ℝ) ≤ z)
    (hprob : p ≤ (wilsonColorLaw R).real (contactEvent F t)) :
    (∫ σ, (1 : ℝ) / (contacts F σ : ℝ) ∂wilsonColorLaw R) ≤
      (1 - p) * z + 1 / t := by
  let E := contactEvent F t
  have hE : MeasurableSet E := measurableSet_contactEvent F t
  have hcomp : MeasurableSet Eᶜ := hE.compl
  have hi : Integrable (fun σ : ColorField => z * (Eᶜ.indicator (fun _ => (1 : ℝ))) σ + 1 / t)
      (wilsonColorLaw R) :=
    (((integrable_const (1 : ℝ)).indicator hcomp).const_mul z).add (integrable_const _)
  have hpoint : ∀ᵐ σ ∂wilsonColorLaw R,
      (1 : ℝ) / (contacts F σ : ℝ) ≤
        z * (Eᶜ.indicator (fun _ => (1 : ℝ))) σ + 1 / t := by
    filter_upwards [hcap] with σ hσ
    by_cases hσE : σ ∈ E
    · have hct : t ≤ (contacts F σ : ℝ) := hσE
      have hb := one_div_le_one_div_of_le ht hct
      have hnot : σ ∉ Eᶜ := fun h => h hσE
      simpa only [Set.indicator_of_notMem hnot, mul_zero, zero_add] using hb
    · rw [Set.indicator_of_mem hσE, mul_one]
      exact hσ.trans (le_add_of_nonneg_right (one_div_nonneg.mpr ht.le))
  calc
    _ ≤ ∫ σ, z * (Eᶜ.indicator (fun _ => (1 : ℝ))) σ + 1 / t ∂wilsonColorLaw R :=
      integral_mono_ae (integrable_reciprocal_contacts R F) hi hpoint
    _ = z * (1 - (wilsonColorLaw R).real E) + 1 / t := by
      rw [integral_add (((integrable_const (1 : ℝ)).indicator hcomp).const_mul z)
        (integrable_const _), integral_const_mul, integral_indicator_const (1 : ℝ) hcomp,
        integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul, mul_one]
      have hc := probReal_add_probReal_compl (μ := wilsonColorLaw R) hE
      rw [show (wilsonColorLaw R).real Eᶜ = 1 - (wilsonColorLaw R).real E by linarith only [hc]]
    _ ≤ (1 - p) * z + 1 / t := by
      have h := mul_le_mul_of_nonneg_left (sub_le_sub_left hprob 1) hz
      nlinarith only [h]

/-- The actual restarted law fixes every color recorded in the earlier pattern. -/
theorem restarted_pattern_ae (R : RootPair) (L : List (Site 2)) (ξ₀ : Rows)
    (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (F : Finset (Site 2)) (p : contactSites F → Bool)
    (hp : ∀ d : contactSites F, out.colors d.val = some (p d)) :
    ∀ᵐ σ ∂wilsonColorLaw (restartedRoots R L ξ₀ out hs),
      ∀ d : contactSites F, σ d.val = p d := by
  let Q := restartedRoots R L ξ₀ out hs
  apply ae_all_iff.mpr
  intro d
  have hm : MeasurableSet {σ : ColorField | σ d.val = p d} :=
    (measurableSet_singleton (p d)).preimage (measurable_pi_apply _)
  change ∀ᵐ σ ∂wilsonColorLaw Q, σ d.val = p d
  rw [wilsonColorLaw]
  apply (ae_map_iff measurable_snd.aemeasurable hm).mpr
  filter_upwards [wilsonLaw_ae_root_colors Q] with ω hω
  cases hc : p d with
  | false => exact hω.2 d.val (by change out.colors d.val = some false; rw [hp d, hc])
  | true => exact hω.1 d.val (by change out.colors d.val = some true; rw [hp d, hc])

/-- Counts at nested source origins increase, with all repeated neighbor incidences retained. -/
theorem contacts_mono_origins {F H : Finset (Site 2)} (hFH : F ⊆ H) (σ : ColorField) :
    contacts F σ ≤ contacts H σ :=
  Finset.sum_le_sum_of_subset_of_nonneg hFH (fun _ _ _ => Nat.zero_le _)

/-- Positivity of the actual earlier observed count gives the cap on the next inverse count. -/
theorem restarted_inverse_cap (R : RootPair) (L : List (Site 2)) (ξ₀ : Rows)
    (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ₀ = some out)
    (F H : Finset (Site 2)) (p : contactSites F → Bool)
    (hp : ∀ d : contactSites F, out.colors d.val = some (p d))
    (hFH : F ⊆ H) (hpos : 0 < patternContacts F p) :
    ∀ᵐ σ ∂wilsonColorLaw (restartedRoots R L ξ₀ out hs),
      (1 : ℝ) / (contacts H σ : ℝ) ≤ (patternContacts F p : ℝ)⁻¹ := by
  filter_upwards [restarted_pattern_ae R L ξ₀ out hs F p hp] with σ hσ
  have he := patternContacts_eq_contacts F p σ hσ
  have hle : (patternContacts F p : ℝ) ≤ (contacts H σ : ℝ) :=
    Nat.cast_le.mpr (he ▸ contacts_mono_origins hFH σ)
  simpa only [one_div] using one_div_le_one_div_of_le (Nat.cast_pos.mpr hpos) hle

end
end FiniteAvalanches.Wilson.Lattice.CurrentInverseContraction
