/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/HitPoint.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added.
-/
import FiniteAvalanches.Walk.Beurling.LastExit
import FiniteAvalanches.Walk.Beurling.DiskGreen

/-!
# Hitting a point before leaving a disk

The annular estimate for the probability that planar simple random walk hits the origin before
leaving a disk, from Lawler and Limic (2004), Lemma 8.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open Filter
open scoped Topology

private theorem green_symm (r : ℝ) (x y : Site 2) : green r x y = green r y x := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) (diskFinset r)
  rw [green, green, Network.killedGreenReal_symm (Graph.Zd.latticeConnected 2) _ hq x y]

private theorem prob_hits_origin_zero {r : ℝ} (hr : 0 < r) :
    prob (hitsBefore {0} r 0) = 1 := by
  have h : hitsBefore {0} r 0 = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true]
    refine ⟨0, ?_, ?_⟩
    · simp [walkPos]
    · intro s hs
      have : s = 0 := Nat.eq_zero_of_le_zero hs
      subst s
      simpa [walkPos] using hr
  simp [prob, h]

private theorem prob_hits_origin_mul_green (r : ℝ) (hr : 0 < r) (z : Site 2) :
    prob (hitsBefore {0} r z) * green r 0 0 = green r 0 z := by
  have hz := hitsBefore_eq_sum_green_mul r ({0} : Finset (Site 2))
    (by simpa using hr) z
  have h0 := hitsBefore_eq_sum_green_mul r ({0} : Finset (Site 2))
    (by simpa using hr) 0
  simp only [Finset.sum_singleton, Finset.coe_singleton] at hz h0
  rw [prob_hits_origin_zero hr] at h0
  rw [hz, green_symm r z 0]
  calc
    (green r 0 z * prob (exitsBefore r {0} 0)) * green r 0 0 =
        green r 0 z * (green r 0 0 * prob (exitsBefore r {0} 0)) := by ring
    _ = green r 0 z := by rw [← h0, mul_one]

private theorem eventually_green_error_small (K a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, K * (11 * (n : ℝ) ^ (-(1 / 3 : ℝ))) ≤ a / 2 := by
  have ht : Tendsto (fun n : ℕ => K * (11 * (n : ℝ) ^ (-(1 / 3 : ℝ)))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
    convert (h.const_mul 11).const_mul K using 1 <;> norm_num
  exact (ht.eventually (eventually_lt_nhds (show (0 : ℝ) < a / 2 by linarith))).mono
    fun _ h => le_of_lt h

/-- The probability of hitting the origin from the middle of a disk is comparable to `1 / log n`.
This is Lawler and Limic (2004), Lemma 8, for planar simple random walk. -/
theorem hit_origin_annulus : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → ∀ z : Site 2, n / 10 ≤ euclidNorm z →
      euclidNorm z < 9 * n / 10 →
      c₁ / Real.log n ≤ prob (hitsBefore {0} n z) ∧
        prob (hitsBefore {0} n z) ≤ c₂ / Real.log n := by
  obtain ⟨C, hC⟩ := green_asymptotics
  let K : ℝ := |C| + 1
  let a : ℝ := Real.log (10 / 9)
  let b : ℝ := Real.log 10
  have hK : 0 < K := by dsimp [K]; positivity
  have ha : 0 < a := by dsimp [a]; exact Real.log_pos (by norm_num)
  have hb : 0 < b := by dsimp [b]; exact Real.log_pos (by norm_num)
  have hCK : C ≤ K := by dsimp [K]; have := le_abs_self C; linarith
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ max 1 (2 * K) ≤ Real.log n ∧
        K * (11 * (n : ℝ) ^ (-(1 / 3 : ℝ))) ≤ a / 2 := by
    filter_upwards [eventually_ge_atTop 2, hlog.eventually (eventually_ge_atTop (max 1 (2 * K))),
      eventually_green_error_small K a ha] with n hn hl he
    exact ⟨hn, hl, he⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨a / 3, 2 * b + a, by positivity, by positivity, N, ?_⟩
  intro n hn z hzl hzu
  obtain ⟨hn2, hlogbig, herr⟩ := hN n hn
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hzpos : 0 < euclidNorm z := by linarith
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    simp at hzpos
  have hzn : euclidNorm z < n := by linarith
  have hlogpos : 0 < Real.log n := by linarith [le_max_left (1 : ℝ) (2 * K)]
  have hlogK : 2 * K ≤ Real.log n := le_trans (le_max_right 1 (2 * K)) hlogbig
  have hpow : 0 ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnpos) _
  have hinv : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hzinv : 1 / euclidNorm z ≤ 10 / (n : ℝ) := by
    apply (div_le_div_iff₀ hzpos hnpos).2
    linarith
  have hinv10 : 10 / (n : ℝ) ≤ 10 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ 10 by norm_num)
  have hsmall : C * (1 / euclidNorm z + (n : ℝ) ^ (-(1 / 3 : ℝ))) ≤ a / 2 := by
    calc
      C * (1 / euclidNorm z + (n : ℝ) ^ (-(1 / 3 : ℝ))) ≤
          K * (1 / euclidNorm z + (n : ℝ) ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_right hCK (by positivity)
      _ ≤ K * (11 * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hK)
        linarith
      _ ≤ a / 2 := herr
  have hratio₁ : (10 / 9 : ℝ) ≤ (n : ℝ) / euclidNorm z := by
    apply (le_div_iff₀ hzpos).2
    linarith
  have hratio₂ : (n : ℝ) / euclidNorm z ≤ 10 := by
    apply (div_le_iff₀ hzpos).2
    linarith
  have hlog₁ : a ≤ Real.log n - Real.log (euclidNorm z) := by
    dsimp [a]
    rw [← Real.log_div (ne_of_gt hnpos) (ne_of_gt hzpos)]
    exact Real.log_le_log (by norm_num) hratio₁
  have hlog₂ : Real.log n - Real.log (euclidNorm z) ≤ b := by
    dsimp [b]
    rw [← Real.log_div (ne_of_gt hnpos) (ne_of_gt hzpos)]
    exact Real.log_le_log (div_pos hnpos hzpos) hratio₂
  obtain ⟨hoff, hdiag⟩ := hC n hn2
  have hoff' := abs_le.mp (hoff z hz0 hzn)
  have hdiag' := abs_le.mp hdiag
  have hofflo : a / 2 ≤ Real.pi / 2 * green n 0 z := by linarith
  have hoffhi : Real.pi / 2 * green n 0 z ≤ b + a / 2 := by linarith
  have hdiaglo : Real.log n / 2 ≤ Real.pi / 2 * green n 0 0 := by linarith
  have hdiaghi : Real.pi / 2 * green n 0 0 ≤ 3 * Real.log n / 2 := by linarith
  have hmul := prob_hits_origin_mul_green (n : ℝ) hnpos z
  have hmul' : prob (hitsBefore {0} n z) * (Real.pi / 2 * green n 0 0) =
      Real.pi / 2 * green n 0 z := by
    calc
      _ = (Real.pi / 2) * (prob (hitsBefore {0} n z) * green n 0 0) := by ring
      _ = _ := by rw [hmul]
  have hp : 0 ≤ prob (hitsBefore {0} n z) := by nlinarith
  constructor
  · apply (div_le_iff₀ hlogpos).2
    nlinarith
  · apply (le_div_iff₀ hlogpos).2
    nlinarith

end FiniteAvalanches.Walk.Beurling
