import FiniteAvalanches.External.ClassicalBeurling
import FiniteAvalanches.Wilson.Lattice.BeurlingGeometry

set_option autoImplicit false
namespace FiniteAvalanches.BeurlingConnected
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.External.Beurling
open scoped Classical ENNReal
noncomputable section

/-- Uniform Beurling estimate for connected lattice obstacles joining0 to the square circuit. -/
 theorem connected_square_exit_bound : ∃ C : ℝ, 0 < C ∧
    ∀ K : Set (Site 2), ((lattice 2).induce K).Preconnected → (0 : Site 2) ∈ K →
    ∀ r H : ℕ, 4 * r + 4 ≤ H →
      (∃ z ∈ K, FiniteAvalanches.siteRadius 0 z = H) →
    ∀ x : Site 2, FiniteAvalanches.siteRadius 0 x ≤ r →
      FiniteAvalanches.Wilson.Lattice.walkLaw (hitBefore K {z | H < FiniteAvalanches.siteRadius 0 z} x) ≤
        ENNReal.ofReal (C * Real.sqrt (((r + 1 : ℕ) : ℝ) / H)) := by
  obtain ⟨c, hc, h⟩ := FiniteAvalanches.External.lawler_limic_beurling_srw_Z2
  let C : ℝ := max c 1 * Real.sqrt 8
  have hCpos : 0 < C := mul_pos (lt_of_lt_of_le hc (le_max_left _ _)) (by positivity)
  refine ⟨C, hCpos, ?_⟩
  intro K hK h0 r H hH hboundary x hx
  rw [← supNorm_eq_siteRadius] at hx
  obtain ⟨z, hz, hzr⟩ := hboundary
  rw [← supNorm_eq_siteRadius] at hzr
  by_cases hlong : 8 * r + 8 ≤ H
  · let k : ℕ := 2 * r + 1
    let n : ℕ := (H - r) / 2
    obtain ⟨hk, hkn, hnH, _⟩ := long_range_integer_radii r H hlong
    change 0 < k at hk
    change k < n at hkn
    change 2 * n + r ≤ H + 1 at hnH
    let Krel : Set (Site 2) := {y | y + x ∈ K}
    let A : Set (Site 2) := padded Krel k n
    have hout : (n : ℝ) ≤ euclidNorm (z - x) := by
      have ht := supNorm_triangle (z - x) x
      rw [sub_add_cancel, hzr] at ht
      have hn : n ≤ supNorm (z - x) := by dsimp [n]; omega
      exact (by exact_mod_cast hn : (n : ℝ) ≤ (supNorm (z - x) : ℝ)).trans
        (supNorm_le_euclidNorm _)
    have hmid : ∀ j : ℕ, k ≤ j → j < n → ∃ y ∈ Krel,
        (j : ℝ) ≤ euclidNorm y ∧ euclidNorm y < (j : ℝ) + 1 := by
      intro j hjk hjn
      have hin : euclidNorm (-x) < j :=
        lt_of_lt_of_le (query_initial_distance x r hx) (by exact_mod_cast hjk)
      have hjout : (j : ℝ) ≤ euclidNorm (z - x) :=
        (by exact_mod_cast hjn.le : (j : ℝ) ≤ n).trans hout
      obtain ⟨y, hy, hl, hu⟩ := connected_shell K hK h0 z hz x j hin hjout
      exact ⟨y - x, by change (y - x) + x ∈ K; simpa only [sub_add_cancel] using hy, hl, hu⟩
    have hstd := h A (padded_dense Krel k n hmid) k n hk hkn
    rw [pathLaw_eq_walkLaw] at hstd
    have hsub : hitBefore K {z | H < FiniteAvalanches.siteRadius 0 z} x ⊆
        {ω | ∃ t : ℕ, 2 * (n : ℝ) ≤ euclidNorm (position 0 ω t) ∧
          ∀ s : ℕ, 1 ≤ s → s ≤ t → position 0 ω s ∉ annulus A k n} := by
      rintro ω ⟨t, ht, hav⟩
      change H < FiniteAvalanches.siteRadius 0 (position x ω t) at ht
      have hexit := translated_square_exit x (position x ω t) r H n hx
        (by rwa [supNorm_eq_siteRadius]) hnH
      rw [position_translate] at hexit
      refine ⟨t, hexit, ?_⟩
      intro s _ hs hmem
      change position 0 ω s ∈ annulus (padded Krel k n) k n at hmem
      rw [annulus_padded] at hmem
      apply hav s hs
      have he : position 0 ω s + x = position x ω s := by
        rw [← position_translate]; abel
      have hm : position 0 ω s + x ∈ K := hmem.1
      rwa [he] at hm
    have hratio : (k : ℝ) / n ≤ 8 * (((r + 1 : ℕ) : ℝ) / H) := by
      simpa [k, n, mul_div_assoc] using long_range_ratio r H hlong
    have hsqrt : Real.sqrt ((k : ℝ) / n) ≤
        Real.sqrt 8 * Real.sqrt (((r + 1 : ℕ) : ℝ) / H) := by
      calc _ ≤ Real.sqrt (8 * (((r + 1 : ℕ) : ℝ) / H)) := Real.sqrt_le_sqrt hratio
        _ = _ := Real.sqrt_mul (by norm_num) _
    have hscalar : c * Real.sqrt ((k : ℝ) / n) ≤
        C * Real.sqrt (((r + 1 : ℕ) : ℝ) / H) := by
      calc _ ≤ c * (Real.sqrt 8 * Real.sqrt (((r + 1 : ℕ) : ℝ) / H)) :=
          mul_le_mul_of_nonneg_left hsqrt hc.le
        _ ≤ max c 1 * (Real.sqrt 8 * Real.sqrt (((r + 1 : ℕ) : ℝ) / H)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ = _ := by dsimp [C]; ring
    exact (measure_mono hsub).trans (hstd.trans (ENNReal.ofReal_le_ofReal hscalar))
  · have hHp : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
    have hshort : H ≤ 8 * (r + 1) := by omega
    have hratio : (1 : ℝ) ≤ 8 * (((r + 1 : ℕ) : ℝ) / H) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hHp).mpr
      simpa only [one_mul] using
        (show (H : ℝ) ≤ 8 * (((r + 1 : ℕ) : ℝ)) by exact_mod_cast hshort)
    have hroot : 1 ≤ Real.sqrt 8 * Real.sqrt (((r + 1 : ℕ) : ℝ) / H) := by
      rw [← Real.sqrt_mul (by norm_num)]
      simpa using Real.sqrt_le_sqrt hratio
    have hC : Real.sqrt 8 ≤ C := by
      have hh := mul_le_mul_of_nonneg_right (le_max_right c (1 : ℝ))
        (Real.sqrt_nonneg (8 : ℝ))
      calc
        Real.sqrt 8 = 1 * Real.sqrt 8 := (one_mul _).symm
        _ ≤ C := hh
    have hh : 1 ≤ C * Real.sqrt (((r + 1 : ℕ) : ℝ) / H) :=
      hroot.trans (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))
    calc _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal hh


end
end FiniteAvalanches.BeurlingConnected
