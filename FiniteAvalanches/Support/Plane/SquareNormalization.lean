import FiniteAvalanches.Support.Plane.PlaneArcStraightening
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Normalizing a simple arc inside a closed square

A simple arc in an open plane set is sent by a plane homeomorphism onto a
centred horizontal segment, so that the closed unit ball of the sup norm on
`ℝ × ℝ` pulls back into the open set, while a given compact set off the arc
stays outside that ball. The homeomorphism is the whole-plane straightening of
the arc followed by an affine rescaling.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric

/-- The affine plane homeomorphism `(x, y) ↦ ((2x - 1)c, y / δ)`. -/
noncomputable def squareRescale (c δ : ℝ) (hc : c ≠ 0) (hδ : δ ≠ 0) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := ((2 * z.1 - 1) * c, z.2 / δ)
  invFun z := ((z.1 / c + 1) / 2, z.2 * δ)
  left_inv z := by
    apply Prod.ext
    · change ((2 * z.1 - 1) * c / c + 1) / 2 = z.1
      field_simp
      ring
    · change z.2 / δ * δ = z.2
      field_simp
  right_inv z := by
    apply Prod.ext
    · change (2 * ((z.1 / c + 1) / 2) - 1) * c = z.1
      field_simp
      ring
    · change z.2 * δ / δ = z.2
      field_simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Coordinates of a point of the closed unit sup-norm ball are bounded by one. -/
theorem abs_fst_le_one_of_norm_le {z : ℝ × ℝ} (hz : ‖z‖ ≤ 1) : |z.1| ≤ 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hz
  exact (le_max_left _ _).trans hz

/-- Coordinates of a point of the closed unit sup-norm ball are bounded by one. -/
theorem abs_snd_le_one_of_norm_le {z : ℝ × ℝ} (hz : ‖z‖ ≤ 1) : |z.2| ≤ 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hz
  exact (le_max_right _ _).trans hz

/-- A simple arc in an open plane set can be normalized to a centred horizontal
segment whose closed unit sup-norm ball neighbourhood pulls back into the set and
avoids a given compact set disjoint from the arc. -/
theorem exists_square_normalization {x y : ℝ × ℝ} (p : Path x y)
    (hp : Function.Injective p) {U P : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hpU : range p ⊆ U) (hP : IsCompact P) (hPp : Disjoint P (range p)) :
    ∃ G : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      (∀ t : unitInterval, G (p t) = ((2 * (t : ℝ) - 1) * c, 0)) ∧
      (∀ z : ℝ × ℝ, ‖z‖ ≤ 1 → G.symm z ∈ U) ∧
      (∀ z ∈ P, 1 < ‖G z‖) := by
  obtain ⟨F, hF⟩ := exists_plane_homeomorph_straightening p hp
  let L : Set (ℝ × ℝ) := F '' range p
  have hL : IsCompact L := (isCompact_range p.continuous).image F.continuous
  let O : Set (ℝ × ℝ) := F '' U \ F '' P
  have hO : IsOpen O := (F.isOpenMap U hU).sdiff (hP.image F.continuous).isClosed
  have hLO : L ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨z, hpU hz, rfl⟩, ?_⟩
    rintro ⟨w, hw, hwz⟩
    exact disjoint_left.mp hPp (F.injective hwz ▸ hw) hz
  obtain ⟨δ, hδ, hsub⟩ := hL.exists_cthickening_subset_open hO hLO
  let c : ℝ := 1 / (1 + 2 * δ)
  have hc : 0 < c := by positivity
  have hc1 : c < 1 := by
    apply (div_lt_one (by positivity)).2
    linarith
  let A := squareRescale c δ hc.ne' hδ.ne'
  have hA : ∀ w : ℝ × ℝ, ‖w‖ ≤ 1 → A.symm w ∈ O := by
    intro w hw
    apply hsub
    have h1 := abs_le.mp (abs_fst_le_one_of_norm_le hw)
    have h2 := abs_snd_le_one_of_norm_le hw
    let a : ℝ := (w.1 / c + 1) / 2
    have ha : a = (w.1 * (1 + 2 * δ) + 1) / 2 := by
      simp only [a, c]
      field_simp
    let b : ℝ := max 0 (min 1 a)
    have hb : b ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    have hbL : (b, (0 : ℝ)) ∈ L := ⟨p ⟨b, hb⟩, mem_range_self _, hF _⟩
    apply mem_cthickening_of_dist_le _ (b, (0 : ℝ)) δ L hbL
    rw [Prod.dist_eq]
    apply max_le
    · change dist a b ≤ δ
      rw [Real.dist_eq, abs_le]
      have hlo : -δ ≤ a := by rw [ha]; nlinarith
      have hhi : a ≤ 1 + δ := by rw [ha]; nlinarith
      simp only [b, max_def, min_def]
      split_ifs <;> constructor <;> linarith
    · change dist (w.2 * δ) 0 ≤ δ
      rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hδ]
      nlinarith [abs_nonneg w.2]
  refine ⟨F.trans A, c, hc, hc1, ?_, ?_, ?_⟩
  · intro t
    change A (F (p t)) = _
    rw [hF t]
    change ((2 * (t : ℝ) - 1) * c, (0 : ℝ) / δ) = _
    rw [zero_div]
  · intro z hz
    obtain ⟨⟨w, hw, hwz⟩, _⟩ := hA z hz
    change F.symm (A.symm z) ∈ U
    rw [← hwz, F.symm_apply_apply]
    exact hw
  · intro z hz
    by_contra hle
    have hmem := (hA _ (not_lt.mp hle)).2
    apply hmem
    refine ⟨z, hz, ?_⟩
    change F z = A.symm (A (F z))
    rw [A.symm_apply_apply]

end FiniteAvalanches.Electrical.StatementGeometry
