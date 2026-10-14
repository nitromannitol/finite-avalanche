import FiniteAvalanches.Electrical.Physical.Undilated.Square
import Mathlib.Topology.Order.Compact

/-! Exact dictionaries for the incoming literal function and compact-square oscillation. -/

set_option autoImplicit false
open Set
open FiniteAvalanches.Electrical.Geometry

namespace FiniteAvalanches.Electrical.Physical.Undilated

/-- The source function has no singularity anywhere on the declared plane. -/
theorem continuous_angular (epsilon y0 : ℝ) (he : 0 < epsilon) :
    Continuous (angular epsilon y0) := by
  unfold angular radialDistance
  fun_prop (disch := intro z; positivity)

/-- The pairwise-difference supremum is literally the attained maximum minus minimum. -/
theorem square_angularOsc_eq_max_sub_min (Q : Square) (epsilon y0 : ℝ) (he : 0 < epsilon) :
    ∃ lo ∈ Q.carrier, ∃ hi ∈ Q.carrier,
      (∀ z ∈ Q.carrier, angular epsilon y0 lo ≤ angular epsilon y0 z) ∧
      (∀ z ∈ Q.carrier, angular epsilon y0 z ≤ angular epsilon y0 hi) ∧
      Q.angularOsc epsilon y0 1 (by norm_num) he =
        angular epsilon y0 hi - angular epsilon y0 lo := by
  have hcompact : IsCompact Q.carrier := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (angular epsilon y0) Q.carrier :=
    (continuous_angular epsilon y0 he).continuousOn
  obtain ⟨lo, hlo, hmin⟩ := hcompact.exists_isMinOn Q.carrier_nonempty hcont
  obtain ⟨hi, hhi, hmax⟩ := hcompact.exists_isMaxOn Q.carrier_nonempty hcont
  refine ⟨lo, hlo, hi, hhi, hmin, hmax, le_antisymm ?_ ?_⟩
  · apply oscillation_le
    intro u hu v hv
    rw [square_dilate_one] at hu hv
    refine abs_le.mpr ⟨?_, sub_le_sub (hmax hu) (hmin hv)⟩
    calc
      _ ≤ -(angular epsilon y0 v - angular epsilon y0 u) :=
        neg_le_neg (sub_le_sub (hmax hv) (hmin hu))
      _ = _ := neg_sub _ _
  · have h := abs_sub_le_oscillation (F := angular epsilon y0) hhi hlo
      ⟨1, fun u _ v _ => angular_sub_le_one epsilon y0 he u v⟩
    rw [abs_of_nonneg (sub_nonneg.mpr (hmin hhi))] at h
    simpa only [Square.angularOsc, square_dilate_one] using h

/-- Side is the exact max-coordinate diameter, including the point-square case. -/
theorem square_side_distance (Q : Square) :
    pointDist (Q.x, Q.y) (Q.x + Q.side, Q.y + Q.side) = Q.side := by
  simp only [pointDist, sub_add_cancel_left, abs_neg,
    abs_of_nonneg Q.side_nonneg, max_self]

/-- Translating by y0 and scaling by 2/p yields the paper's literal F, not a new cutoff. -/
theorem angular_half_current_eq_literal_scaled (p y0 : ℝ) (hp : 0 < p) (z : ℝ × ℝ) :
    angular (p / 2) y0 z =
      1 / 2 + ((2 / p) * (z.2 - y0)) /
        (2 * max 1 (max |(2 / p) * z.1| |(2 / p) * (z.2 - y0)|)) := by
  let c := 2 / p
  have hc : 0 < c := by dsimp [c]; positivity
  have hunit : c * (p / 2) = 1 := by dsimp [c]; field_simp
  have hd : 0 < max (p / 2) (radialDistance y0 z) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hmax : max 1 (max |c * z.1| |c * (z.2 - y0)|) =
      c * max (p / 2) (radialDistance y0 z) := by
    calc
      _ = max 1 (c * radialDistance y0 z) := by
        unfold radialDistance
        rw [abs_mul, abs_mul, abs_of_pos hc, mul_max_of_nonneg _ _ hc.le]
      _ = _ := by rw [mul_max_of_nonneg _ _ hc.le, hunit]
  change 1 / 2 + (z.2 - y0) / (2 * max (p / 2) (radialDistance y0 z)) =
    1 / 2 + (c * (z.2 - y0)) / (2 * max 1 (max |c * z.1| |c * (z.2 - y0)|))
  rw [hmax]
  field_simp [hc.ne', hd.ne']

end FiniteAvalanches.Electrical.Physical.Undilated
