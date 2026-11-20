/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/DenseSum.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; import
`LatticeProb.Lattice.Translation` replaced by `FiniteAvalanches.Walk.SiteTranslation`; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`ite_eq_left` replaced by `if_pos` (6 times); `ite_eq_right` replaced by `if_neg` (6 times).
-/
import FiniteAvalanches.Walk.Beurling.DiskGreen
import FiniteAvalanches.Walk.SiteTranslation

/-!
# The Green function summed over a minimal dense set

Lemma 5 of G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*,
Electron. J. Probab. 9 (2004), for the simple random walk on `ℤ²`: if `w j` lies in the
annulus `j ≤ |w| < j + 1` for every `j`, then `∑_{j < n} G_n(z, w_j) ≤ c n` for all `z ∈ C_n`,
with `c` independent of `n`, `z` and the sequence `w`.

The killed Green function is invariant under translations of the lattice, so
`G_n(z, w) ≤ G_{2n}(0, w - z)` for `z ∈ C_n` by domain monotonicity, and Lemma 3 gives
`(π/2) G_{2n}(0, y) ≤ log n - log |y| + O(1)`. If `m = ⌊|z|⌋`, then
`|w_j - z| ≥ |j - m| - 1`, and `j ↦ |j - m|` is at most two-to-one, so the sum is bounded by
twice `∑_{k < n} (log n - log k + O(1)) = O(n)`.

## Main statements

* `sum_green_minimal_le`: Lawler-Limic (2004), Lemma 5, formula (12).
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

private theorem mem_diskFinset_iff' {r : ℝ} {y : Site 2} :
    y ∈ diskFinset r ↔ euclidNorm y < r := by
  rw [diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

private theorem euclidNorm_eq_norm (y : Site 2) :
    euclidNorm y = ‖(WithLp.toLp 2 fun i => ((y i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2))‖ := by
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, euclidNorm]

private theorem toLp_sub (a b : Site 2) :
    (WithLp.toLp 2 fun i => (((a - b) i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2)) =
      (WithLp.toLp 2 fun i => ((a i : ℤ) : ℝ)) - (WithLp.toLp 2 fun i => ((b i : ℤ) : ℝ)) := by
  ext i
  simp

private theorem euclidNorm_sub_le_add (a b : Site 2) :
    euclidNorm (a - b) ≤ euclidNorm a + euclidNorm b := by
  rw [euclidNorm_eq_norm (a - b), euclidNorm_eq_norm a, euclidNorm_eq_norm b, toLp_sub]
  exact norm_sub_le _ _

private theorem abs_euclidNorm_sub_le (a b : Site 2) :
    |euclidNorm a - euclidNorm b| ≤ euclidNorm (a - b) := by
  rw [euclidNorm_eq_norm (a - b), euclidNorm_eq_norm a, euclidNorm_eq_norm b, toLp_sub]
  exact abs_norm_sub_norm_le _ _

private theorem one_le_euclidNorm {y : Site 2} (hy : y ≠ 0) : 1 ≤ euclidNorm y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
  have h1 : 1 ≤ supNorm y :=
    (Int.natAbs_pos.2 hi).trans_le (Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ i))
  exact (by exact_mod_cast h1 : (1 : ℝ) ≤ supNorm y).trans (supNorm_le_euclidNorm y)

private theorem sum_neighborFinset_add_right (v x : Site 2) (f : Site 2 → ℝ) :
    ∑ u ∈ (lattice 2).neighborFinset (x + v), f u =
      ∑ u ∈ (lattice 2).neighborFinset x, f (u + v) := by
  symm
  refine Finset.sum_nbij' (fun u => u + v) (fun u => u - v) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact (lattice_adj_add_right_iff v x u).2 hu
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    rw [← lattice_adj_add_right_iff v, sub_add_cancel]
    exact hu
  · intro u _
    simp
  · intro u _
    simp
  · intro u _
    rfl

private theorem degree_add_right (v x : Site 2) :
    (lattice 2).degree (x + v) = (lattice 2).degree x := by
  have h := sum_neighborFinset_add_right v x (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, SimpleGraph.card_neighborFinset_eq_degree]
    at h
  exact_mod_cast h

/-- The killed kernel of the lattice is invariant under translations. -/
private theorem killedHeat_add_right (C : Set (Site 2)) (v : Site 2) :
    ∀ (k : ℕ) (x y : Site 2), Graph.killedHeat (lattice 2) C k (x + v) (y + v) =
      Graph.killedHeat (lattice 2) ((· + v) ⁻¹' C) k x y := by
  intro k
  induction k with
  | zero =>
    intro x y
    rw [Network.killedHeat_zero, Network.killedHeat_zero]
    by_cases h : x + v ∈ C
    · rw [if_pos h, if_pos (show x ∈ (· + v) ⁻¹' C from h)]
      by_cases hxy : x = y
      · rw [if_pos hxy, if_pos (show x + v = y + v by rw [hxy])]
      · rw [if_neg hxy,
          if_neg (show x + v ≠ y + v from fun h' => hxy (add_right_cancel h'))]
    · rw [if_neg h, if_neg (show x ∉ (· + v) ⁻¹' C from h)]
  | succ k ih =>
    intro x y
    rw [Network.killedHeat_succ, Network.killedHeat_succ, sum_neighborFinset_add_right v x
      (fun u => Graph.killedHeat (lattice 2) C k u (y + v)), degree_add_right]
    by_cases h : x + v ∈ C
    · rw [if_pos h, if_pos (show x ∈ (· + v) ⁻¹' C from h)]
      simp only [ih]
    · rw [if_neg h, if_neg (show x ∉ (· + v) ⁻¹' C from h)]

/-- The killed Green function of the lattice is invariant under translations. -/
private theorem killedGreenReal_add_right (C : Set (Site 2)) (v x y : Site 2) :
    Graph.killedGreenReal (lattice 2) C (x + v) (y + v) =
      Graph.killedGreenReal (lattice 2) ((· + v) ⁻¹' C) x y := by
  simp only [Graph.killedGreenReal, Graph.killedGreen, killedHeat_add_right C v,
    degree_add_right]

/-- `G_r(z, y) ≤ G_{2r}(0, y - z)` for `z ∈ C_r`. -/
private theorem green_le_green_two_mul {r : ℝ} {z : Site 2} (hz : euclidNorm z < r)
    (y : Site 2) : green r z y ≤ green (2 * r) 0 (y - z) := by
  set F := (diskFinset (2 * r)).filter (fun u => u + z ∈ diskFinset r) with hFdef
  have hF : (· + z) ⁻¹' (diskFinset r : Set (Site 2)) = (F : Set (Site 2)) := by
    ext u
    simp only [Set.mem_preimage, Finset.mem_coe, hFdef, Finset.mem_filter, mem_diskFinset_iff']
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    have := euclidNorm_sub_le_add (u + z) z
    rw [add_sub_cancel_right] at this
    linarith
  have h1 : Graph.killedGreenReal (lattice 2) (diskFinset r : Set (Site 2)) z y =
      Graph.killedGreenReal (lattice 2) (F : Set (Site 2)) 0 (y - z) := by
    rw [← hF, ← killedGreenReal_add_right, zero_add, sub_add_cancel]
  rw [green, green, h1]
  exact mul_le_mul_of_nonneg_left (killedGreenReal_mono (Finset.filter_subset _ _) 0 (y - z))
    (by norm_num)

/-- `n log n - n ≤ log n!`. -/
private theorem sum_log_succ_ge (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ ∑ k ∈ Finset.range n, Real.log ((k : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hstep : (n : ℝ) * Real.log (n + 1) ≤ n * Real.log n + 1 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have h := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
        rw [Real.log_div (by positivity) hn'.ne'] at h
        have h2 : (n : ℝ) * (((n : ℝ) + 1) / n - 1) = 1 := by
          field_simp
          ring
        nlinarith
    have hexp : ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) =
        (n : ℝ) * Real.log ((n : ℝ) + 1) + Real.log ((n : ℝ) + 1) := by ring
    linarith

/-- The map `j ↦ |j - m|` on `{0, …, n - 1}` is at most two-to-one. -/
private theorem sum_range_dist_le {n m : ℕ} (hm : m < n) (H : ℕ → ℝ) (hH : ∀ k < n, 0 ≤ H k) :
    ∑ j ∈ Finset.range n, H (Nat.dist j m) ≤ 2 * ∑ k ∈ Finset.range n, H k := by
  have hmaps : ∀ j ∈ Finset.range n, Nat.dist j m ∈ Finset.range n := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    unfold Nat.dist
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hsub : (Finset.range n).filter (fun j => Nat.dist j m = k) ⊆ {m + k, m - k} := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_insert, Finset.mem_singleton]
    unfold Nat.dist at hj
    omega
  have hc : (((Finset.range n).filter (fun j => Nat.dist j m = k)).card : ℝ) ≤ 2 := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_le_two
  calc ∑ j ∈ (Finset.range n).filter (fun j => Nat.dist j m = k), H (Nat.dist j m)
      = ∑ j ∈ (Finset.range n).filter (fun j => Nat.dist j m = k), H k :=
        Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2]
    _ = ((Finset.range n).filter (fun j => Nat.dist j m = k)).card * H k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * H k := mul_le_mul_of_nonneg_right hc (hH k (Finset.mem_range.1 hk))

/-- **Lawler and Limic (2004), Lemma 5, formula (12)**, for the simple random walk on `ℤ²`:
there is `c` such that `∑_{j < n} G_n(z, w_j) ≤ c n` for all `n ≥ 1`, all `z ∈ C_n` and every
sequence with `j ≤ |w_j| < j + 1`. -/
theorem sum_green_minimal_le : ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ w : ℕ → Site 2,
    (∀ j : ℕ, (j : ℝ) ≤ euclidNorm (w j) ∧ euclidNorm (w j) < j + 1) → ∀ z : Site 2,
    euclidNorm z < n → ∑ j ∈ Finset.range n, green n z (w j) ≤ c * n := by
  obtain ⟨C, hC⟩ := green_asymptotics
  refine ⟨2 / Real.pi * (6 * Real.log 2 + 2 + 2 * |C|), fun n hn w hw z hz => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (2 * n) + Real.log 2 := ⟨_, rfl⟩
  obtain ⟨hfar, hzero⟩ := hC (2 * n) (by omega)
  push_cast at hfar hzero
  have hterm : ∀ y : Site 2, euclidNorm y < 2 * n → Real.pi / 2 * green (2 * n) 0 y ≤
      Real.log (2 * n) - Real.log (max 1 (euclidNorm y)) + 2 * |C| := by
    intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      have h := (abs_le.1 hzero).2
      rw [euclidNorm_zero, max_eq_left zero_le_one, Real.log_one]
      linarith [le_abs_self C, abs_nonneg C]
    · have h1 := one_le_euclidNorm hy0
      have hs := (abs_le.1 (hfar y hy0 hy)).2
      have hrp : (2 * (n : ℝ)) ^ (-(1/3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      have hrp0 : 0 ≤ (2 * (n : ℝ)) ^ (-(1/3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      have hinv : 1 / euclidNorm y ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact h1
      have hinv0 : 0 ≤ 1 / euclidNorm y := div_nonneg zero_le_one (euclidNorm_nonneg y)
      have hCs : C * (1 / euclidNorm y + (2 * (n : ℝ)) ^ (-(1/3 : ℝ))) ≤ 2 * |C| :=
        calc C * (1 / euclidNorm y + (2 * (n : ℝ)) ^ (-(1/3 : ℝ)))
            ≤ |C| * (1 / euclidNorm y + (2 * (n : ℝ)) ^ (-(1/3 : ℝ))) :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
          _ ≤ |C| * 2 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
          _ = 2 * |C| := mul_comm _ _
      rw [max_eq_right h1]
      linarith
  have hz0 := euclidNorm_nonneg z
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌊euclidNorm z⌋₊ := ⟨_, rfl⟩
  have hmz : (m : ℝ) ≤ euclidNorm z := hm ▸ Nat.floor_le hz0
  have hzm : euclidNorm z < m + 1 := hm ▸ Nat.lt_floor_add_one _
  have hmn : m < n := hm ▸ (Nat.floor_lt hz0).2 hz
  have hbound : ∀ j ∈ Finset.range n, Real.pi / 2 * green n z (w j) ≤
      (L - Real.log (max 1 (Nat.dist j m : ℝ))) + 2 * |C| := by
    intro j hj
    have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hj
    have hwj := hw j
    have hy : euclidNorm (w j - z) < 2 * n := by
      linarith [euclidNorm_sub_le_add (w j) z, hwj.2]
    have hd : (Nat.dist j m : ℝ) - 1 ≤ euclidNorm (w j - z) := by
      have habs := abs_le.1 (abs_euclidNorm_sub_le (w j) z)
      rcases le_total m j with h | h
      · have hdist : Nat.dist j m = j - m := by
          unfold Nat.dist
          omega
        rw [hdist, Nat.cast_sub h]
        linarith [habs.2, hwj.1]
      · have hdist : Nat.dist j m = m - j := by
          unfold Nat.dist
          omega
        rw [hdist, Nat.cast_sub h]
        linarith [habs.1, hwj.2]
    have hmax : max 1 (Nat.dist j m : ℝ) / 2 ≤ max 1 (euclidNorm (w j - z)) := by
      rcases Nat.lt_or_ge (Nat.dist j m) 2 with h | h
      · have h1 : (Nat.dist j m : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 h
        rw [max_eq_left h1]
        linarith [le_max_left 1 (euclidNorm (w j - z))]
      · have h2 : (2 : ℝ) ≤ Nat.dist j m := by exact_mod_cast h
        rw [max_eq_right (by linarith)]
        linarith [le_max_right 1 (euclidNorm (w j - z))]
    have hpos : (0 : ℝ) < max 1 (Nat.dist j m : ℝ) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hlog : Real.log (max 1 (Nat.dist j m : ℝ)) - Real.log 2 ≤
        Real.log (max 1 (euclidNorm (w j - z))) := by
      rw [← Real.log_div hpos.ne' (by norm_num)]
      exact Real.log_le_log (div_pos hpos two_pos) hmax
    have hG := mul_le_mul_of_nonneg_left (green_le_green_two_mul hz (w j))
      (le_of_lt (by positivity : (0 : ℝ) < Real.pi / 2))
    have hT := hterm _ hy
    rw [hL]
    linarith
  have hH : ∀ k < n, 0 ≤ L - Real.log (max 1 (k : ℝ)) := by
    intro k hk
    have hk' : max 1 (k : ℝ) ≤ n := max_le hn1 (by exact_mod_cast hk.le)
    have h1 : Real.log (max 1 (k : ℝ)) ≤ Real.log n :=
      Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) hk'
    have h2 : Real.log n ≤ Real.log (2 * n) := Real.log_le_log hn0 (by linarith)
    rw [hL]
    linarith
  have hfib : ∑ j ∈ Finset.range n, (L - Real.log (max 1 (Nat.dist j m : ℝ))) ≤
      2 * ∑ k ∈ Finset.range n, (L - Real.log (max 1 (k : ℝ))) :=
    sum_range_dist_le hmn (fun k => L - Real.log (max 1 (k : ℝ))) hH
  have hlogsum : ∑ k ∈ Finset.range n, (L - Real.log (max 1 (k : ℝ))) ≤
      (3 * Real.log 2 + 1) * n := by
    have hk : ∀ k ∈ Finset.range n,
        Real.log ((k : ℝ) + 1) - Real.log 2 ≤ Real.log (max 1 (k : ℝ)) := by
      intro k _
      rw [← Real.log_div (by positivity) (by norm_num)]
      apply Real.log_le_log (by positivity)
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num
      · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        rw [max_eq_right this]
        linarith
    have hs := Finset.sum_le_sum hk
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hst := sum_log_succ_ge n
    have hl2n : Real.log (2 * n) = Real.log 2 + Real.log n := Real.log_mul (by norm_num) hn0.ne'
    rw [hL, hl2n]
    nlinarith
  have hsum : Real.pi / 2 * ∑ j ∈ Finset.range n, green n z (w j) ≤
      (6 * Real.log 2 + 2 + 2 * |C|) * n := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.range n, Real.pi / 2 * green n z (w j)
        ≤ ∑ j ∈ Finset.range n, ((L - Real.log (max 1 (Nat.dist j m : ℝ))) + 2 * |C|) :=
          Finset.sum_le_sum hbound
      _ = ∑ j ∈ Finset.range n, (L - Real.log (max 1 (Nat.dist j m : ℝ))) + n * (2 * |C|) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (6 * Real.log 2 + 2 + 2 * |C|) * n := by nlinarith
  have hpi : 0 < Real.pi := Real.pi_pos
  calc ∑ j ∈ Finset.range n, green n z (w j)
      = 2 / Real.pi * (Real.pi / 2 * ∑ j ∈ Finset.range n, green n z (w j)) := by
        field_simp
    _ ≤ 2 / Real.pi * ((6 * Real.log 2 + 2 + 2 * |C|) * n) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 / Real.pi * (6 * Real.log 2 + 2 + 2 * |C|) * n := by ring

end FiniteAvalanches.Walk.Beurling
