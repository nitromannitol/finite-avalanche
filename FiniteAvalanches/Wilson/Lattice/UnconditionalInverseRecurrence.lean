import FiniteAvalanches.Wilson.Lattice.GlobalPrefixContraction
import FiniteAvalanches.Wilson.Lattice.ObservedInverseLaw
import FiniteAvalanches.Wilson.Lattice.CurrentPrefixLocalization
import FiniteAvalanches.Probability.Multiscale.ForcingError

/-! Incoming cd552a5, main.tex 519–523: integration of the consecutive-prefix
conditional inverse contraction, with the actual prefix escape error. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentUnconditionalInverse
open LatticeProb Sandpile MeasureTheory Filter
open Probability.CurrentScale CurrentInverseContact CurrentNestedPrefix
open CurrentObservedInverse ConditionalIteration7 ActualLocalizationUnion
open scoped Classical ENNReal
noncomputable section

theorem nat_inverse_le_one (m : ℕ) : (m : ℝ)⁻¹ ≤ 1 := by
  by_cases hm : m = 0
  · simp [hm]
  · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    simpa only [inv_one] using inv_anti₀ (by norm_num : (0 : ℝ) < 1) h1

/-- The literal finite pattern observation is everywhere between zero and one,
including rows where the finite sampler has not completed. -/
theorem observed_inverse_bounds (R : RootPair) (L : List (Site 2))
    (F : Finset (Site 2)) (ξ : Rows) :
    0 ≤ observedInverseContacts R L F ξ ∧ observedInverseContacts R L F ξ ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro p _hp
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) ξ)
  · by_cases hp : ∃ p : contactSites F → Bool,
        ξ ∈ observedPattern (initialSampler R) L F p
    · obtain ⟨p, hp⟩ := hp
      rw [observedInverseContacts_of_pattern R L F p ξ hp]
      exact nat_inverse_le_one _
    · have hzero : observedInverseContacts R L F ξ = 0 := by
        apply Finset.sum_eq_zero
        intro p _hp
        rw [Set.indicator_of_notMem (fun h => hp ⟨p, h⟩), mul_zero]
      rw [hzero]
      exact zero_le_one

/-- Integrate the conditional estimate on confinement and the unit bound off it.
This helper only performs integration; the source contraction and escape probability
are supplied by the concrete source theorem below. -/
theorem integrate_confined_contraction (R : RootPair) (L Q : List (Site 2))
    (F H : Finset (Site 2)) (h : ℕ) (q t : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hgood : ∀ᵐ ξ ∂wilsonRows, ξ ∉ prefixExit R L h →
      (wilsonRows[observedInverseContacts R Q H | fullHistory R L]) ξ ≤
        q * observedInverseContacts R L F ξ + t) :
    (∫ ξ, observedInverseContacts R Q H ξ ∂wilsonRows) ≤
      q * (∫ ξ, observedInverseContacts R L F ξ ∂wilsonRows) + t +
        wilsonRows.real (prefixExit R L h) := by
  let B := prefixExit R L h
  have hm := fullHistory_le R L
  have hV := integrable_observedInverseContacts R Q H
  have hW := integrable_observedInverseContacts R L F
  have hB : MeasurableSet B := measurable_prefixExit R L h
  have hcap : ∀ᵐ ξ ∂wilsonRows,
      (wilsonRows[observedInverseContacts R Q H | fullHistory R L]) ξ ≤ 1 := by
    have hc := condExp_mono (m := fullHistory R L) hV (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun ξ => (observed_inverse_bounds R Q H ξ).2))
    rw [condExp_const hm (1 : ℝ)] at hc
    filter_upwards [hc] with ξ hξ
    exact hξ
  have hbound : ∀ᵐ ξ ∂wilsonRows,
      (wilsonRows[observedInverseContacts R Q H | fullHistory R L]) ξ ≤
        q * observedInverseContacts R L F ξ + t + B.indicator (fun _ => (1 : ℝ)) ξ := by
    filter_upwards [hgood, hcap] with ξ hg hc
    by_cases hb : ξ ∈ B
    · rw [Set.indicator_of_mem hb]
      have hn := mul_nonneg hq (observed_inverse_bounds R L F ξ).1
      linarith
    · rw [Set.indicator_of_notMem hb, add_zero]
      exact hg hb
  have hsum : Integrable (fun ξ => q * observedInverseContacts R L F ξ + t) wilsonRows :=
    (hW.const_mul q).add (integrable_const t)
  have hind : Integrable (fun ξ => B.indicator (fun _ => (1 : ℝ)) ξ) wilsonRows :=
    (integrable_const (1 : ℝ)).indicator hB
  have hI := integral_mono_ae integrable_condExp (hsum.add hind) hbound
  rw [integral_condExp hm] at hI
  change (∫ ξ, observedInverseContacts R Q H ξ ∂wilsonRows) ≤
    ∫ ξ, (q * observedInverseContacts R L F ξ + t) + B.indicator (fun _ => (1 : ℝ)) ξ ∂wilsonRows at hI
  rw [integral_add hsum hind,
    integral_add (hW.const_mul q) (integrable_const t), integral_const_mul,
    integral_const, integral_indicator_const (1 : ℝ) hB] at hI
  simpa only [probReal_univ, smul_eq_mul, one_mul, mul_one] using hI

/-- Current Step 2, unconditionally on the original color law. One epsilon,
kappa and escape coefficient precede all geometries, roots, horizons and stages. -/
theorem source_inverse_mean_recurrence :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ κ : ℕ, 30 ≤ κ ∧ 73728 ≤ ε*(κ : ℝ) ∧ ∃ D : ℝ, 0 < D ∧
      ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      (0 : Site 2) ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ y ∈ γ, (lattice 2).Adj 0 y) →
      ∀ R : RootPair, R.zero = (K : Set (Site 2)) → R.one = γ →
      ∀ n : ℕ, 2 ≤ n →
      16 * scale (6 * κ) n ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ i : ℕ, 2 ≤ i → i ≤ n →
      (∫ σ, (contacts (sourceWindow K (6 * κ) i) σ : ℝ)⁻¹ ∂wilsonColorLaw R) ≤
        (1 - ε / 2) *
          (∫ σ, (contacts (sourceWindow K (6 * κ) (i - 1)) σ : ℝ)⁻¹ ∂wilsonColorLaw R) +
        16 / Real.log (scale (6 * κ) i : ℝ) +
        D * Real.rpow (scale (6 * κ) (i - 1) : ℝ) (-(1 / 2 : ℝ)) := by
  obtain ⟨ε, hε, hεsmall, κ, hκ, hpaid, hconditional⟩ :=
    CurrentGlobalContraction.global_prefix_inverse_contraction
  obtain ⟨D, hD, hescape⟩ := CurrentPrefixLocalization.source_prefix_localization
  have hb : 6 ≤ 6 * κ := by omega
  refine ⟨ε, hε, hεsmall, κ, hκ, hpaid, D, hD, ?_⟩
  intro K γ hK h0 hd hγ hfin hadj R hz ho n hn hdiam i hi hin
  have hisub : i - 1 + 1 = i := by omega
  have hprev : 1 ≤ i - 1 := by omega
  have hnextdiam : 16 * scale (6 * κ) (i - 1 + 1) ≤
      K.sup (fun x => K.sup (fun y => siteRadius x y)) := by
    rw [hisub]
    exact (Nat.mul_le_mul_left 16 (scale_mono _ hb hin)).trans hdiam
  have hgood := hconditional K γ hK h0 hd hγ hfin hadj R hz ho (i - 1) hprev hnextdiam
  rw [hisub] at hgood
  have hgood' : ∀ᵐ ξ ∂wilsonRows,
      ξ ∉ prefixExit R (stagePrefix (6 * κ) (i - 1)) (scale (6 * κ) (i - 1) ^ 6) →
      (wilsonRows[observedInverseContacts R (stagePrefix (6 * κ) i)
        (sourceWindow K (6 * κ) i) | fullHistory R (stagePrefix (6 * κ) (i - 1))]) ξ ≤
      (1 - ε / 2) * observedInverseContacts R (stagePrefix (6 * κ) (i - 1))
        (sourceWindow K (6 * κ) (i - 1)) ξ + 16 / Real.log (scale (6 * κ) i : ℝ) := hgood
  have hlog : 0 < Real.log (scale (6 * κ) i : ℝ) :=
    Real.log_pos (by exact_mod_cast CurrentPrefixLocalization.two_le_scale _ hb i)
  have hI := integrate_confined_contraction R (stagePrefix (6 * κ) (i - 1))
    (stagePrefix (6 * κ) i) (sourceWindow K (6 * κ) (i - 1))
    (sourceWindow K (6 * κ) i) (scale (6 * κ) (i - 1) ^ 6)
    (1 - ε / 2) (16 / Real.log (scale (6 * κ) i : ℝ)) (by linarith) (by positivity) hgood'
  rw [integral_source_observed_inverse_eq R K _ hb i (by omega),
    integral_source_observed_inverse_eq R K _ hb (i - 1) hprev] at hI
  have he := hescape (6 * κ) hb K hK h0 R (by rw [hz]) n hn hdiam (i - 1) hprev (by omega)
  have heR : wilsonRows.real
      (prefixExit R (stagePrefix (6 * κ) (i - 1)) (scale (6 * κ) (i - 1) ^ 6)) ≤
      D * Real.rpow (scale (6 * κ) (i - 1) : ℝ) (-(1 / 2 : ℝ)) := by
    have ht := ENNReal.toReal_mono (by simp) he
    have hnonneg : 0 ≤ D * (scale (6 * κ) (i - 1) : ℝ) ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    simpa only [Measure.real, ENNReal.toReal_ofReal hnonneg, Real.rpow_eq_pow] using ht
  exact hI.trans (add_le_add le_rfl heR)

end
end FiniteAvalanches.Wilson.Lattice.CurrentUnconditionalInverse
