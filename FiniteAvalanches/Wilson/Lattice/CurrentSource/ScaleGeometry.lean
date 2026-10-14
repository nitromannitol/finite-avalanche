import FiniteAvalanches.Wilson.Lattice.LocalComparison.ScaleGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CurrentScaleGeometry
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- One kappa, chosen before all scales, pays the current greedy-needle budget. -/
theorem exists_uniform_kappa (ε : ℝ) (hε : 0 < ε) :
    ∃ κ : ℕ, 30 ≤ κ ∧ 73728 ≤ ε*(κ : ℝ) ∧
      ∀ h r : ℕ, 10 ≤ h → h^κ ≤ r →
        10^30 ≤ r ∧ 2*h ≤ r ∧
        (κ : ℝ)*Real.log (h : ℝ) ≤ Real.log (r : ℝ) ∧
        2304*Real.log (h : ℝ) ≤ (ε/2)*(Real.log (r : ℝ)/16) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (73728/ε)
  let κ := max 30 k
  have hκ : 30 ≤ κ := le_max_left _ _
  have hεk : 73728 ≤ ε*(κ : ℝ) := by
    have hdiv : 73728/ε < (κ : ℝ) := hk.trans_le (Nat.cast_le.mpr (le_max_right _ _))
    have he := (div_lt_iff₀ hε).mp hdiv
    nlinarith only [he]
  refine ⟨κ, hκ, hεk, ?_⟩
  intro h r hh hr
  have hscale : 10^30 ≤ r := by
    calc
      10^30 ≤ h^30 := Nat.pow_le_pow_left hh 30
      _ ≤ h^κ := Nat.pow_le_pow_right (by omega) hκ
      _ ≤ r := hr
  have htwo : 2*h ≤ r := by
    calc
      2*h ≤ h^2 := by nlinarith only [hh]
      _ ≤ h^κ := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ r := hr
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hlog : (κ : ℝ)*Real.log (h : ℝ) ≤ Real.log (r : ℝ) := by
    have hpow : (h : ℝ)^κ ≤ (r : ℝ) := by exact_mod_cast hr
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos hhpos κ) hpow
  have hlogh := Real.log_natCast_nonneg h
  have hpaid := mul_le_mul_of_nonneg_right hεk hlogh
  have hεlog := mul_le_mul_of_nonneg_left hlog hε.le
  refine ⟨hscale, htwo, hlog, ?_⟩
  nlinarith only [hpaid, hεlog]

end
end FiniteAvalanches.Wilson.Lattice.CurrentScaleGeometry
