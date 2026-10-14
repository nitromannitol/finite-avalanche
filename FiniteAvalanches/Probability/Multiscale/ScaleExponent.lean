import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Numerical support for incoming cd552a5, main.tex 504–509 and 525–534.
The scales are consecutive and the exponent is the full -log(q)/log(b).
No forest estimate or recurrence is an input to these numerical results. -/

set_option autoImplicit false

namespace FiniteAvalanches.Probability.CurrentScale

/-- The literal natural scales in the incoming proof. -/
def scale (b i : ℕ) : ℕ := 2^(b^i)

/-- The full exponent supplied by consecutive scales. -/
noncomputable def exponent (b : ℕ) (q : ℝ) : ℝ := -Real.log q / Real.log (b : ℝ)

theorem scale_pos (b i : ℕ) : 0 < scale b i := by
  exact pow_pos (by norm_num) _

/-- Natural exponentiation is cast before applying the ordinary logarithm identity. -/
theorem log_scale (b i : ℕ) :
    Real.log (scale b i : ℝ) = (b : ℝ)^i * Real.log 2 := by
  simp only [scale, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem exponent_pos (b : ℕ) (hb : 6 ≤ b) (q : ℝ)
    (hqlo : (1/2 : ℝ) < q) (hqhi : q < 1) : 0 < exponent b q := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hq0 : 0 < q := (by norm_num : (0 : ℝ) < 1/2).trans hqlo
  exact div_pos (neg_pos.mpr (Real.log_neg hq0 hqhi)) (Real.log_pos hb1)

/-- The exact decay identity has no factor of two in its exponent. -/
theorem pow_eq_rpow (b : ℕ) (hb : 6 ≤ b) (q : ℝ)
    (hqlo : (1/2 : ℝ) < q) (n : ℕ) :
    q^n = (b : ℝ)^(-(exponent b q) * (n : ℝ)) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb1
  have hlb : Real.log (b : ℝ) ≠ 0 := (Real.log_pos hb1).ne'
  have hq0 : 0 < q := (by norm_num : (0 : ℝ) < 1/2).trans hqlo
  have hlog : Real.log (b : ℝ) * (-(exponent b q)) = Real.log q := by
    unfold exponent
    field_simp [hlb]
  have hbase : (b : ℝ)^(-(exponent b q)) = q := by
    rw [Real.rpow_def_of_pos hb0, hlog, Real.exp_log hq0]
  rw [Real.rpow_mul_natCast hb0.le, hbase]

/-- The same identity in the natural-power base used by the logarithmic cap. -/
theorem pow_eq_natural_base_rpow (b : ℕ) (hb : 6 ≤ b) (q : ℝ)
    (hqlo : (1/2 : ℝ) < q) (n : ℕ) :
    q^n = ((b : ℝ)^n)^(-(exponent b q)) := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  rw [pow_eq_rpow b hb q hqlo n,
    show -(exponent b q) * (n : ℝ) = (n : ℝ) * (-(exponent b q)) by ring,
    Real.rpow_natCast_mul hb0]

/-- Every natural diameter, including zero, gives a positive logarithm. -/
theorem log_diameter_pos (d : ℕ) : 0 < Real.log ((d : ℝ)+2) := by
  apply Real.log_pos
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

/-- A strict upper scale bound gives a symbolic logarithmic cap. -/
theorem log_diameter_le_scale (b i d : ℕ) (hd : d < 16*scale b i) :
    Real.log ((d : ℝ)+2) ≤ Real.log 18 + (b : ℝ)^i * Real.log 2 := by
  have hs : 1 ≤ scale b i := scale_pos b i
  have hnat : d+2 ≤ 18*scale b i := by omega
  have hreal : (d : ℝ)+2 ≤ 18*(scale b i : ℝ) := by exact_mod_cast hnat
  have hs0 : (0 : ℝ) < (scale b i : ℝ) := by exact_mod_cast scale_pos b i
  calc
    _ ≤ Real.log (18*(scale b i : ℝ)) :=
      Real.log_le_log (by positivity) hreal
    _ = Real.log 18 + (b : ℝ)^i * Real.log 2 := by
      rw [Real.log_mul (by norm_num) hs0.ne', log_scale]

/-- The maximal next scale costs a single factor b, rather than a doubled index. -/
theorem log_diameter_le_maximal_cap (b : ℕ) (hb : 6 ≤ b) (d n : ℕ)
    (hd : d < 16*scale b (n+1)) :
    Real.log ((d : ℝ)+2) ≤
      (Real.log 18 + (b : ℝ)*Real.log 2) * (b : ℝ)^n := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hbn : (1 : ℝ) ≤ (b : ℝ)^n := one_le_pow₀ hb1
  calc
    _ ≤ Real.log 18 + (b : ℝ)^(n+1)*Real.log 2 := log_diameter_le_scale b (n+1) d hd
    _ ≤ (Real.log 18 + (b : ℝ)*Real.log 2) * (b : ℝ)^n := by
      have hlog : 0 ≤ Real.log (18 : ℝ) := (Real.log_pos (by norm_num)).le
      have hmul := mul_le_mul_of_nonneg_left hbn hlog
      rw [pow_succ]
      nlinarith only [hmul]

/-- Negative real powers convert a positive multiplicative cap to a uniform bound. -/
theorem rpow_bound_of_le_mul (L A B a : ℝ) (hL : 0 < L) (hA : 0 < A)
    (hB : 0 < B) (ha : 0 ≤ a) (hcap : L ≤ A*B) :
    B^(-a) ≤ A^a * L^(-a) := by
  have hm := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hL hcap (neg_nonpos.mpr ha))
    (Real.rpow_pos_of_pos hA a).le
  have he : A^a * (A*B)^(-a) = B^(-a) := by
    rw [Real.mul_rpow hA.le hB.le, ← mul_assoc, ← Real.rpow_add hA]
    simp only [add_neg_cancel, Real.rpow_zero, one_mul]
  rwa [he] at hm

/-- One constant, chosen before both diameter ranges, yields the exact source exponent. -/
theorem maximal_scale_log_bound (b : ℕ) (hb : 6 ≤ b)
    (q : ℝ) (hqlo : (1/2 : ℝ) < q) (hqhi : q < 1) :
    0 < exponent b q ∧ ∃ C : ℝ, 0 < C ∧
      (∀ d n : ℕ, 2 ≤ n → 16*scale b n ≤ d → d < 16*scale b (n+1) →
        q^n ≤ C * (Real.log ((d : ℝ)+2)) ^ (-(exponent b q))) ∧
      (∀ d : ℕ, d < 16*scale b 2 →
        (1 : ℝ) ≤ C * (Real.log ((d : ℝ)+2)) ^ (-(exponent b q))) := by
  let a := exponent b q
  let A := Real.log 18 + (b : ℝ)*Real.log 2
  let B := Real.log 18 + (b : ℝ)^2*Real.log 2
  let C := A^a + B^a
  have ha : 0 < a := exponent_pos b hb q hqlo hqhi
  have hlog18 : 0 < Real.log (18 : ℝ) := Real.log_pos (by norm_num)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hA : 0 < A := by
    exact add_pos_of_pos_of_nonneg hlog18 (mul_nonneg (Nat.cast_nonneg b) hlog2)
  have hB : 0 < B := by
    exact add_pos_of_pos_of_nonneg hlog18 (mul_nonneg (sq_nonneg _) hlog2)
  have hAa : 0 < A^a := Real.rpow_pos_of_pos hA a
  have hBa : 0 < B^a := Real.rpow_pos_of_pos hB a
  have hC : 0 < C := add_pos hAa hBa
  refine ⟨ha, C, hC, ?_, ?_⟩
  · intro d n _hn _hlo hhi
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hcap := log_diameter_le_maximal_cap b hb d n hhi
    have hbound := rpow_bound_of_le_mul (Real.log ((d : ℝ)+2)) A ((b : ℝ)^n) a
      (log_diameter_pos d) hA (pow_pos hb0 n) ha.le hcap
    rw [← pow_eq_natural_base_rpow b hb q hqlo n] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hBa.le) (Real.rpow_pos_of_pos (log_diameter_pos d) (-a)).le)
  · intro d hd
    have hcap : Real.log ((d : ℝ)+2) ≤ B*1 := by
      simpa only [mul_one] using log_diameter_le_scale b 2 d hd
    have hbound := rpow_bound_of_le_mul (Real.log ((d : ℝ)+2)) B 1 a
      (log_diameter_pos d) hB zero_lt_one ha.le hcap
    rw [Real.one_rpow] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hAa.le) (Real.rpow_pos_of_pos (log_diameter_pos d) (-a)).le)

end FiniteAvalanches.Probability.CurrentScale
