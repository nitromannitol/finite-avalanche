module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Survival estimates from local success bounds on finite or general probability spaces. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability

open MeasureTheory

/-- A real-mass recurrence needs no finite carrier or independence. -/
theorem mass_le_pow (a : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) (hzero : a 0 ≤ 1)
    (n : ℕ) (hstep : ∀ i < n, a (i + 1) ≤ q * a i) : a n ≤ q ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using hzero
  | succ n ih =>
      have hprev := ih (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      calc
        a (n + 1) ≤ q * a n := hstep n (Nat.lt_succ_self n)
        _ ≤ q * q ^ n := mul_le_mul_of_nonneg_left hprev hq
        _ = q ^ (n + 1) := by rw [pow_succ, mul_comm]

/-- A finite weighted event recurrence. The success premise is the cross-multiplied
conditional lower bound on the preceding survival event, including zero-mass events. -/
theorem finite_failure_mass_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω = 1)
    (B S : ℕ → Finset Ω) (p : ℝ) (hp : p ≤ 1) (n : ℕ)
    (hnext : ∀ i < n, B (i + 1) ⊆ B i \ S i)
    (hsuccess : ∀ i < n,
      p * (∑ ω ∈ B i, w ω) ≤ ∑ ω ∈ B i ∩ S i, w ω) :
    (∑ ω ∈ B n, w ω) ≤ (1 - p) ^ n := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp
  have hzero : (∑ ω ∈ B 0, w ω) ≤ 1 := by
    calc
      (∑ ω ∈ B 0, w ω) ≤ ∑ ω ∈ Finset.univ, w ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun ω _ _ => hw ω)
      _ = 1 := htotal
  have hstep : ∀ i < n,
      (∑ ω ∈ B (i + 1), w ω) ≤ (1 - p) * (∑ ω ∈ B i, w ω) := by
    intro i hi
    have hsub : (∑ ω ∈ B (i + 1), w ω) ≤ ∑ ω ∈ B i \ S i, w ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (hnext i hi) (fun ω _ _ => hw ω)
    have hsplit := Finset.sum_inter_add_sum_sdiff (B i) (S i) w
    nlinarith only [hsub, hsplit, hsuccess i hi]
  exact mass_le_pow (fun i => ∑ ω ∈ B i, w ω) (1 - p) hq hzero n hstep

section Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Integrated local successes bound the probability of decreasing surviving events. -/
theorem survival_le_pow (B S : ℕ → Set Ω)
    (hS : ∀ i, MeasurableSet (S i)) (p : ℝ) (hp : p ≤ 1) (n : ℕ)
    (hnext : ∀ i < n, B (i + 1) ⊆ B i \ S i)
    (hsuccess : ∀ i < n,
      p * μ.real (B i) ≤ ∫ ω in B i, (S i).indicator (fun _ => (1 : ℝ)) ω ∂μ) :
    μ.real (B n) ≤ (1 - p) ^ n := by
  apply mass_le_pow (fun i => μ.real (B i)) (1 - p) (sub_nonneg.mpr hp)
    measureReal_le_one n
  intro i hi
  have hsub := measureReal_mono (hnext i hi) (μ := μ)
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := B i) (hS i)
  have hs := hsuccess i hi
  rw [setIntegral_indicator (hS i), setIntegral_const, smul_eq_mul, mul_one] at hs
  nlinarith only [hsub, hsplit, hs]

/-- Integrating an almost-sure conditional-success bound on a history-measurable event. -/
theorem success_mass_ge_of_condExp (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (B S : Set Ω) (hB : MeasurableSet[m] B) (hS : MeasurableSet[m₀] S) (p : ℝ)
    (hsuccess : ∀ᵐ ω ∂μ, ω ∈ B →
      p ≤ (μ[S.indicator (fun _ => (1 : ℝ)) | m]) ω) :
    p * μ.real B ≤ ∫ ω in B, S.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
  calc
    p * μ.real B = ∫ _ in B, p ∂μ := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ ω in B, (μ[S.indicator (fun _ => (1 : ℝ)) | m]) ω ∂μ :=
      setIntegral_mono_on_ae (integrable_const p) integrable_condExp.restrict
        (hm B hB) hsuccess
    _ = ∫ ω in B, S.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator hS) hB

/-- Conditional success on previous surviving histories suffices without independence. -/
theorem survival_le_pow_of_condExp (m : ℕ → MeasurableSpace Ω) (hm : ∀ i, m i ≤ m₀)
    (B S : ℕ → Set Ω) (hB : ∀ i, MeasurableSet[m i] (B i))
    (hS : ∀ i, MeasurableSet (S i)) (p : ℝ) (hp : p ≤ 1) (n : ℕ)
    (hnext : ∀ i < n, B (i + 1) ⊆ B i \ S i)
    (hsuccess : ∀ i < n, ∀ᵐ ω ∂μ, ω ∈ B i →
      p ≤ (μ[(S i).indicator (fun _ => (1 : ℝ)) | m i]) ω) :
    μ.real (B n) ≤ (1 - p) ^ n := by
  apply survival_le_pow μ B S hS p hp n hnext
  intro i hi
  exact success_mass_ge_of_condExp μ (m i) (hm i) (B i) (S i) (hB i) (hS i) p
    (hsuccess i hi)

end Probability

end FiniteAvalanches.Probability

