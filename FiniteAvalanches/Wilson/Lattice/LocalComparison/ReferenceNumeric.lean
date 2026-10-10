import FiniteAvalanches.Wilson.Lattice.LocalComparison.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
namespace JointReferenceNumeric

theorem variance_le_eight_sq (C M m r v : ℝ) (hM : 32 ≤ M)
    (hlog : 1 ≤ Real.log r) (hlogM : Real.log r ≤ 2*M)
    (hMm : M ≤ m) (hmr : m ≤ r^3)
    (hv : v ≤ C*M*(1+Real.log (m/M))) : v ≤ 8*(max 0 C)*M^2 := by
  have hMp : 0 < M := by linarith only [hM]
  have hmq : 1 ≤ m/M := (le_div_iff₀ hMp).mpr (by linarith only [hMm])
  have hL : 0 ≤ 1+Real.log (m/M) := by linarith only [Real.log_nonneg hmq]
  have hq : m/M ≤ r^3 := by
    have hm : 0 ≤ m := hMp.le.trans hMm
    exact (div_le_self hm (by linarith only [hM])).trans hmr
  have hupper : Real.log (m/M) ≤ 3*Real.log r := by
    have h := Real.log_le_log (lt_of_lt_of_le zero_lt_one hmq) hq
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hvar : v ≤ (max 0 C)*M*(1+Real.log (m/M)) :=
    hv.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 0 C) hMp.le) hL)
  have hC : 0 ≤ max 0 C := le_max_left 0 C
  have hCM : 0 ≤ max 0 C * M := mul_nonneg hC hMp.le
  calc
    v ≤ max 0 C * M * (1 + Real.log (m/M)) := hvar
    _ ≤ max 0 C * M * (1+3*Real.log r) := mul_le_mul_of_nonneg_left (by linarith only [hupper]) hCM
    _ ≤ max 0 C * M * (4*Real.log r) := mul_le_mul_of_nonneg_left (by linarith only [hlog]) hCM
    _ ≤ max 0 C * M * (8*M) := mul_le_mul_of_nonneg_left (by linarith only [hlogM]) hCM
    _ = 8*(max 0 C)*M^2 := by ring

end JointReferenceNumeric
