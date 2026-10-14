import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.ConditioningMain.CurrentScale
open Filter
noncomputable section

/-- The literal source scale floor(M^(1/6)) preserves a uniform logarithmic
comparison and absorbs the polynomial error at the same M. -/
theorem literal_sixth_root_scale (a : ℝ) (ha : 0 < a) :
    ∀ᶠ M : ℕ in atTop,
      let r := ⌊(M : ℝ) ^ (1 / 6 : ℝ)⌋₊
      2 ≤ r ∧ r + 2 ≤ M ∧
      Real.log ((r : ℝ) + 2) ^ (-a) ≤
        (12 : ℝ) ^ a * Real.log ((M : ℝ) + 2) ^ (-a) ∧
      (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) ≤
        (2 : ℝ) ^ (1 / 3 : ℝ) * Real.log ((M : ℝ) + 2) ^ (-a) := by
  have hsmall : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ a ≤ x ^ (1 / 12 : ℝ) := by
    have h := (isLittleO_log_rpow_rpow_atTop a
      (show (0 : ℝ) < 1 / 12 by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg
      (Real.log_nonneg hx1) a), Real.norm_of_nonneg
      (Real.rpow_nonneg (by linarith : 0 ≤ x) (1 / 12)), one_mul] using hx
  have hxlim : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (64 : ℕ), hxlim.eventually hsmall] with M hM64 hsmallM
  let x : ℝ := (M : ℝ)
  have hx64 : (64 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hM64
  have hlogpower : Real.log ((M : ℝ) + 2) ^ a ≤ x ^ (1 / 6 : ℝ) := by
    apply hsmallM.trans
    calc
      _ ≤ (x ^ (2 : ℕ)) ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by dsimp [x]; nlinarith only [hx64])
          (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ x)]
        congr 1
        norm_num
  let r : ℕ := ⌊x ^ (1 / 6 : ℝ)⌋₊
  have hx : 0 < x := by dsimp [x]; linarith
  have hx1 : 1 ≤ x := by dsimp [x]; linarith
  have hp : 0 < x ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hx _
  have hrle : (r : ℝ) ≤ x ^ (1 / 6 : ℝ) := Nat.floor_le hp.le
  have hrlt : x ^ (1 / 6 : ℝ) < (r : ℝ) + 1 := Nat.lt_floor_add_one _
  have htwo : (2 : ℝ) ≤ x ^ (1 / 6 : ℝ) := by
    have h := Real.rpow_le_rpow (show (0 : ℝ) ≤ 2 ^ (6 : ℕ) by norm_num)
      (show (2 : ℝ) ^ (6 : ℕ) ≤ x by dsimp [x]; norm_num; linarith)
      (show (0 : ℝ) ≤ 1 / 6 by norm_num)
    norm_num only [one_div] at h ⊢
    exact h
  have hr2 : 2 ≤ r := (Nat.le_floor_iff hp.le).mpr htwo
  have hroot : x ^ (1 / 6 : ℝ) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hsqrt : Real.sqrt x ≤ x / 4 := by
    have hsq := Real.sq_sqrt hx.le
    have hsn := Real.sqrt_nonneg x
    nlinarith only [hsq, hsn, hx64]
  have hrhalf : (r : ℝ) + 2 ≤ x / 2 := by
    have h := hrle.trans (hroot.trans hsqrt)
    dsimp [x] at *
    linarith only [h, hx64]
  have hrM : r + 2 ≤ M := by
    have h : (r : ℝ) + 2 ≤ (M : ℝ) := by
      dsimp [x] at hrhalf
      linarith only [hrhalf, hx64]
    exact_mod_cast h
  have hlog : 0 < Real.log ((M : ℝ) + 2) := Real.log_pos (by linarith)
  have hlogshift : Real.log ((M : ℝ) + 2) ≤ 2 * Real.log x := by
    have h := Real.log_le_log (show (0 : ℝ) < (M : ℝ) + 2 by positivity)
      (show (M : ℝ) + 2 ≤ x ^ (2 : ℕ) by dsimp [x]; nlinarith only [hx64])
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hrl : Real.log ((M : ℝ) + 2) / 12 ≤ Real.log ((r : ℝ) + 2) := by
    have h := Real.log_le_log hp (show x ^ (1 / 6 : ℝ) ≤ (r : ℝ) + 2 by linarith)
    rw [Real.log_rpow hx] at h
    linarith only [h, hlogshift]
  have hlogbound := Real.rpow_le_rpow_of_nonpos
    (show 0 < Real.log ((M : ℝ) + 2) / 12 by positivity) hrl (neg_nonpos.mpr ha.le)
  have hscale : (Real.log ((M : ℝ) + 2) / 12) ^ (-a) =
      (12 : ℝ) ^ a * Real.log ((M : ℝ) + 2) ^ (-a) := by
    rw [Real.div_rpow hlog.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 12) a]
    simp only [div_inv_eq_mul, mul_comm]
  rw [hscale] at hlogbound
  have hdiff : x / 2 ≤ (M : ℝ) - (r : ℝ) := by
    dsimp [x] at *
    linarith only [hrhalf]
  have hdiffpow := Real.rpow_le_rpow_of_nonpos
    (show 0 < x / 2 by positivity) hdiff (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  have hpoly : (r : ℝ) * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) ≤
      (2 : ℝ) ^ (1 / 3 : ℝ) * x ^ (-(1 / 6 : ℝ)) := by
    calc
      _ ≤ x ^ (1 / 6 : ℝ) * (x / 2) ^ (-(1 / 3 : ℝ)) :=
        mul_le_mul hrle hdiffpow (Real.rpow_nonneg (by linarith) _) hp.le
      _ = _ := by
        rw [Real.div_rpow hx.le (by norm_num),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (1 / 3)]
        simp only [div_inv_eq_mul]
        rw [mul_comm (x ^ (-(1 / 3 : ℝ))), ← mul_assoc,
          mul_comm (x ^ (1 / 6 : ℝ)), mul_assoc, ← Real.rpow_add hx]
        congr 1
        norm_num
  have habsorb : x ^ (-(1 / 6 : ℝ)) ≤ Real.log ((M : ℝ) + 2) ^ (-a) := by
    rw [Real.rpow_neg hx.le, Real.rpow_neg hlog.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hlog _)).mpr hlogpower
  exact ⟨hr2, hrM, hlogbound,
    hpoly.trans (mul_le_mul_of_nonneg_left habsorb (by positivity))⟩

end
end FiniteAvalanches.ConditioningMain.CurrentScale

#print axioms FiniteAvalanches.ConditioningMain.CurrentScale.literal_sixth_root_scale
