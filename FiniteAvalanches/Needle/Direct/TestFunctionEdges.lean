import FiniteAvalanches.Needle.Direct.TestFunction

/-! Edge variation of the clipped lattice test function. -/

namespace FiniteAvalanches.Needle
open LatticeProb

private theorem abs_radius_sub_radius_le_one (x y c : Point)
    (hxy : (lattice 2).Adj x y) : |radius (x - c) - radius (y - c)| ≤ 1 := by
  have h1 := linf_triangle x y c
  have h2 := linf_triangle y x c
  dsimp only [linf] at h1 h2
  rw [radius_sub_neighbor hxy] at h1
  rw [radius_sub_neighbor hxy.symm] at h2
  rw [abs_le]
  omega

/-- Variation on a lattice edge decays with its distance from the boundary vertex. -/
theorem needle_test_function_edge_bound (h : ℕ) (w x y : Point)
    (hw : radius w = 2 * h) (hxy : (lattice 2).Adj x y) :
    |needleTestFunction h w x - needleTestFunction h w y| ≤
      6 / (1 + max (linf x w : ℝ) (linf y w : ℝ)) := by
  have hx : 0 ≤ (linf x w : ℝ) := by exact_mod_cast radius_nonneg (x - w)
  have hy : 0 ≤ (linf y w : ℝ) := by exact_mod_cast radius_nonneg (y - w)
  have hr : |(radius x : ℝ) - (radius y : ℝ)| ≤ 1 := by
    have he := abs_radius_sub_radius_le_one x y 0 hxy
    simp only [sub_zero] at he
    exact_mod_cast he
  have hd : |(linf x w : ℝ) - (linf y w : ℝ)| ≤ 1 := by
    exact_mod_cast abs_radius_sub_radius_le_one x y w hxy
  have hab : |3 * max 0 (2 * (h : ℝ) + 1 - (radius x : ℝ)) -
      3 * max 0 (2 * (h : ℝ) + 1 - (radius y : ℝ))| ≤ 3 := by
    have hm := abs_max_sub_max_le_max (0 : ℝ)
      (2 * (h : ℝ) + 1 - (radius x : ℝ)) 0
      (2 * (h : ℝ) + 1 - (radius y : ℝ))
    have he : (2 * (h : ℝ) + 1 - (radius x : ℝ)) -
        (2 * (h : ℝ) + 1 - (radius y : ℝ)) =
        (radius y : ℝ) - (radius x : ℝ) := by ring
    rw [sub_self, abs_zero, he] at hm
    rw [max_eq_right (abs_nonneg ((radius y : ℝ) - (radius x : ℝ)))] at hm
    have hr' : |(radius y : ℝ) - (radius x : ℝ)| ≤ 1 := by
      rw [abs_sub_comm]
      exact hr
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hden : |(1 + (linf x w : ℝ)) - (1 + (linf y w : ℝ))| ≤ 1 := by
    simpa only [add_sub_add_left_eq_sub] using hd
  have hclip := abs_min_one_div_sub_min_one_div_le
    (3 * max 0 (2 * (h : ℝ) + 1 - (radius x : ℝ)))
    (3 * max 0 (2 * (h : ℝ) + 1 - (radius y : ℝ)))
    (1 + (linf x w : ℝ)) (1 + (linf y w : ℝ))
    (mul_nonneg (by norm_num) (le_max_left _ _))
    (mul_nonneg (by norm_num) (le_max_left _ _))
    (by linarith) (by linarith)
    (needle_test_numerator_le_denominator h w x hw)
    (needle_test_numerator_le_denominator h w y hw) hab hden
  have he : max (1 + (linf x w : ℝ)) (1 + (linf y w : ℝ)) =
      1 + max (linf x w : ℝ) (linf y w : ℝ) := by
    rcases le_total (linf x w : ℝ) (linf y w : ℝ) with hle | hle
    · rw [max_eq_right hle, max_eq_right (by linarith)]
    · rw [max_eq_left hle, max_eq_left (by linarith)]
  simpa only [needleTestFunction, he] using hclip

end FiniteAvalanches.Needle
