/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/DiskGreenFar.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`Set.mem_ofPred_eq` replaced by `Set.mem_setOf_eq` (once); `set_option maxHeartbeats 400000 in`
added before `green_far_asymptotics`.
-/
import FiniteAvalanches.Walk.Beurling.DiskGreen
import FiniteAvalanches.Walk.Beurling.GreenWalk

/-!
# Green function estimates far from the boundary

Translation and comparison estimates for the Green function of a planar disk.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

private theorem killedGreenReal_translate (B : Finset (Site 2)) (a x y : Site 2) :
    Graph.killedGreenReal (lattice 2) ((B.image (fun v => a + v) : Finset (Site 2)) : Set (Site 2))
      (a + x) (a + y) = Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) x y := by
  classical
  have hnn (D : Finset (Site 2)) (u v : Site 2) :
      0 ≤ 4 * Graph.killedGreenReal (lattice 2) (D : Set (Site 2)) u v :=
    by
      obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset D
      exact mul_nonneg (by norm_num)
        (Network.killedGreenReal_nonneg (Graph.Zd.latticeConnected 2) D hq u v)
  have he : ENNReal.ofReal (4 * Graph.killedGreenReal (lattice 2)
      ((B.image (fun v => a + v) : Finset (Site 2)) : Set (Site 2)) (a + x) (a + y)) =
      ENNReal.ofReal (4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) x y) := by
    rw [ofReal_killedGreenReal_eq, ofReal_killedGreenReal_eq]
    apply lintegral_congr
    intro ω
    congr 1
    funext t
    congr 1
    ext ω'
    simp only [Set.mem_setOf_eq, Finset.mem_image]
    have hp (s : ℕ) : walkPos (a + x) ω' s = a + walkPos x ω' s := by
      simp [walkPos, add_assoc]
    simp only [hp]
    simp
  have he' := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (hnn _ _ _), ENNReal.toReal_ofReal (hnn _ _ _)] at he'
  linarith

private def siteEuclidean {d : ℕ} (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => ((x i : ℤ) : ℝ)

private theorem siteEuclidean_norm {d : ℕ} (x : Site d) :
    ‖siteEuclidean x‖ = euclidNorm x := by
  simp only [siteEuclidean, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, euclidNorm]

private theorem euclidNorm_add_le (x y : Site 2) :
    euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by
  have h : siteEuclidean (x + y) = siteEuclidean x + siteEuclidean y := by
    ext i
    simp [siteEuclidean]
  rw [← siteEuclidean_norm, h, ← siteEuclidean_norm, ← siteEuclidean_norm]
  exact norm_add_le _ _

private theorem euclidNorm_neg (x : Site 2) : euclidNorm (-x) = euclidNorm x := by
  have h : siteEuclidean (-x) = -siteEuclidean x := by
    ext i
    simp [siteEuclidean]
  rw [← siteEuclidean_norm, h, norm_neg, siteEuclidean_norm]

private theorem mem_diskFinset_iff {r : ℝ} {x : Site 2} :
    x ∈ diskFinset r ↔ euclidNorm x < r := by
  rw [diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

private theorem green_disk_comparison (r t : ℝ) (z w : Site 2)
    (hz : euclidNorm z ≤ t) :
    green (r - t) 0 (w - z) ≤ green r z w ∧
      green r z w ≤ green (r + t) 0 (w - z) := by
  classical
  let shift (s : ℝ) := (diskFinset s).image (fun x => z + x)
  have hleft : shift (r - t) ⊆ diskFinset r := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    apply mem_diskFinset_iff.mpr
    have hy' := mem_diskFinset_iff.mp hy
    have h := euclidNorm_add_le z y
    linarith
  have hright : diskFinset r ⊆ shift (r + t) := by
    intro x hx
    apply Finset.mem_image.mpr
    refine ⟨x - z, ?_, by abel⟩
    apply mem_diskFinset_iff.mpr
    have hx' := mem_diskFinset_iff.mp hx
    have h := euclidNorm_add_le x (-z)
    rw [euclidNorm_neg] at h
    simpa only [sub_eq_add_neg] using (show euclidNorm (x + -z) < r + t by linarith)
  have he (s : ℝ) : 4 * Graph.killedGreenReal (lattice 2) (shift s : Set (Site 2)) z w =
      green s 0 (w - z) := by
    rw [green]
    have h := killedGreenReal_translate (diskFinset s) z 0 (w - z)
    simpa only [add_zero, add_sub_cancel] using congrArg (fun u : ℝ => 4 * u) h
  constructor
  · rw [← he]
    exact mul_le_mul_of_nonneg_left (killedGreenReal_mono hleft z w) (by norm_num)
  · rw [← he]
    exact mul_le_mul_of_nonneg_left (killedGreenReal_mono hright z w) (by norm_num)

private theorem scale_rpow_bound {n a : ℝ} (hn : 2 ≤ n) (ha : n ^ 4 ≤ 2 * a) :
    a ^ (-(1 / 3 : ℝ)) ≤ 2 * n ^ (-(4 / 3 : ℝ)) := by
  have hn0 : 0 < n := by linarith
  have ha0 : 0 < a := by nlinarith [pow_pos hn0 4]
  have hc := Real.rpow_le_rpow_of_nonpos (pow_pos hn0 4) ha (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha0.le] at hc
  have hp : (n ^ 4) ^ (-(1 / 3 : ℝ)) = n ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast_mul hn0.le 4]
    norm_num
  rw [hp] at hc
  have htwo : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by
    calc (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have ha' : 0 ≤ a ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg ha0.le _
  nlinarith

private theorem log_difference_le {n a b : ℝ} (hn : 2 ≤ n)
    (ha : 0 < a) (hb : n ^ 4 ≤ 2 * b) (hab : a - b ≤ n) :
    Real.log a - Real.log b ≤ 2 * n ^ (-(4 / 3 : ℝ)) := by
  have hn0 : 0 < n := by linarith
  have hb0 : 0 < b := by nlinarith [pow_pos hn0 4]
  have hpow : 1 / n ^ 3 ≤ n ^ (-(4 / 3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ n)
      (by norm_num : (-3 : ℝ) ≤ -(4 / 3 : ℝ))
    rw [Real.rpow_neg hn0.le] at h
    change (n ^ ((3 : ℕ) : ℝ))⁻¹ ≤ _ at h
    rw [Real.rpow_natCast] at h
    simpa only [one_div] using h
  calc
    Real.log a - Real.log b = Real.log (a / b) := (Real.log_div ha.ne' hb0.ne').symm
    _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb0)
    _ = (a - b) / b := by field_simp
    _ ≤ n / b := div_le_div_of_nonneg_right hab hb0.le
    _ ≤ 2 / n ^ 3 := by
      rw [div_le_div_iff₀ hb0 (pow_pos hn0 3)]
      nlinarith
    _ = 2 * (1 / n ^ 3) := by ring
    _ ≤ 2 * n ^ (-(4 / 3 : ℝ)) := by gcongr

private theorem abs_log_difference_le {n a b : ℝ} (hn : 2 ≤ n)
    (ha : n ^ 4 ≤ 2 * a) (hb : n ^ 4 ≤ 2 * b) (hab : |a - b| ≤ n) :
    |Real.log a - Real.log b| ≤ 2 * n ^ (-(4 / 3 : ℝ)) := by
  have hn0 : 0 < n := by linarith
  have ha0 : 0 < a := by nlinarith [pow_pos hn0 4]
  have hb0 : 0 < b := by nlinarith [pow_pos hn0 4]
  have h := abs_le.mp hab
  have h1 := log_difference_le hn ha0 hb h.2
  have h2 := log_difference_le hn hb0 ha (by linarith)
  exact abs_le.mpr ⟨by linarith, h1⟩

set_option maxHeartbeats 400000 in
/-- **Lawler and Limic (2004), Lemma 4.** If `m ≥ n⁴`, the Green function between two
points in `C̄_n` has the logarithmic asymptotics of a disk of radius `m`. -/
theorem green_far_asymptotics : ∃ C : ℝ, ∀ n m : ℕ, 2 ≤ n → n ^ 4 ≤ m → ∀ z w : Site 2,
    z ≠ w → euclidNorm z ≤ n → euclidNorm w ≤ n →
    |Real.pi / 2 * green m z w - (Real.log m - Real.log (euclidNorm (z - w)))| ≤
      C * (1 / euclidNorm (z - w) + (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
  obtain ⟨C, hC⟩ := green_asymptotics
  refine ⟨2 * |C| + 2, fun n m hn hm z w hzw hz hw => ?_⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm' : (n : ℝ) ^ 4 ≤ m := by exact_mod_cast hm
  have hn4 : 8 * (n : ℝ) ≤ (n : ℝ) ^ 4 := by
    have h1 : 0 ≤ (n : ℝ) ^ 2 - 4 := by nlinarith
    have h2 := mul_nonneg h1 (show 0 ≤ (n : ℝ) ^ 2 + 4 by positivity)
    nlinarith
  have hnm : n ≤ m := by exact_mod_cast (show (n : ℝ) ≤ m by linarith)
  have hsub : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := Nat.cast_sub hnm
  have hadd : ((m + n : ℕ) : ℝ) = (m : ℝ) + n := by push_cast; rfl
  have hsmall : (n : ℝ) ^ 4 ≤ 2 * ((m - n : ℕ) : ℝ) := by rw [hsub]; linarith
  have hlarge : (n : ℝ) ^ 4 ≤ 2 * ((m + n : ℕ) : ℝ) := by rw [hadd]; linarith
  have hm2 : (n : ℝ) ^ 4 ≤ 2 * (m : ℝ) := by linarith
  have hs2 : 2 ≤ m - n := by
    have : (2 : ℝ) ≤ ((m - n : ℕ) : ℝ) := by rw [hsub]; linarith
    exact_mod_cast this
  have hl2 : 2 ≤ m + n := by omega
  have hnorm : euclidNorm (w - z) ≤ 2 * (n : ℝ) := by
    have h := euclidNorm_add_le w (-z)
    rw [euclidNorm_neg] at h
    simp only [sub_eq_add_neg]
    linarith
  have hlt : euclidNorm (w - z) < ((m - n : ℕ) : ℝ) := by rw [hsub]; linarith
  have hlt' : euclidNorm (w - z) < ((m + n : ℕ) : ℝ) := by rw [hadd]; linarith
  have hne : w - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzw)
  have hnormeq : euclidNorm (w - z) = euclidNorm (z - w) := by
    rw [show w - z = -(z - w) by abel, euclidNorm_neg]
  have hs := (hC (m - n) hs2).1 (w - z) hne hlt
  have hl := (hC (m + n) hl2).1 (w - z) hne hlt'
  rw [hnormeq] at hs hl
  have hsp := scale_rpow_bound hn' hsmall
  have hlp := scale_rpow_bound hn' hlarge
  have hsl := abs_log_difference_le hn' hsmall hm2 (by rw [hsub]; simp)
  have hll := abs_log_difference_le hn' hlarge hm2 (by rw [hadd]; simp)
  have cmp := green_disk_comparison (m : ℝ) (n : ℝ) z w hz
  rw [← hsub, ← hadd] at cmp
  have hp : 0 ≤ Real.pi / 2 := by positivity
  have hc : C ≤ |C| := le_abs_self C
  have hv : 0 ≤ 1 / euclidNorm (z - w) :=
    div_nonneg (by norm_num) (ContinuousTime.euclidNorm_pos (sub_ne_zero.mpr hzw)).le
  have ht : 0 ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hn0.le _
  have hsr : 0 ≤ ((m - n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  have hlr : 0 ≤ ((m + n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  have hs' := abs_le.mp hs
  have hl' := abs_le.mp hl
  have hsl' := abs_le.mp hsl
  have hll' := abs_le.mp hll
  have hcs : C * (1 / euclidNorm (z - w) + ((m - n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) ≤
      |C| * (1 / euclidNorm (z - w) + 2 * (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
    calc
      _ ≤ |C| * (1 / euclidNorm (z - w) + ((m - n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ _ := by gcongr
  have hcl : C * (1 / euclidNorm (z - w) + ((m + n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) ≤
      |C| * (1 / euclidNorm (z - w) + 2 * (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
    calc
      _ ≤ |C| * (1 / euclidNorm (z - w) + ((m + n : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ _ := by gcongr
  have hcmp1 := mul_le_mul_of_nonneg_left cmp.1 hp
  have hcmp2 := mul_le_mul_of_nonneg_left cmp.2 hp
  apply abs_le.mpr
  constructor <;> nlinarith [abs_nonneg C]

end FiniteAvalanches.Walk.Beurling
