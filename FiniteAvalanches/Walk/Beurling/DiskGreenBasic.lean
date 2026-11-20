/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/DiskGreenBasic.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`ite_eq_left` replaced by `if_pos` (4 times).
-/
import FiniteAvalanches.Walk.Beurling.Defs

/-!
# Basic properties of the Green function of a disk

Two elementary facts used in the Beurling estimate of G. F. Lawler and V. Limic, *The Beurling
estimate for a class of random walks*, Electron. J. Probab. 9 (2004): the killed Green function
is monotone in the killing set, so `G_r` is monotone in the radius, and one step of the simple
random walk on `ℤ²` changes the Euclidean norm by at most one (Lemma 2 for the simple random
walk).

The killed Green function is monotone because the killed kernel is, by induction on the time.
The step bound is the triangle inequality, as a step has Euclidean length one; it is not strict,
since a step out of the origin has length exactly one.

## Main statements

* `killedGreenReal_mono`: `g_A ≤ g_B` for finite `A ⊆ B`.
* `green_mono`: `G_r ≤ G_{r'}` for `r ≤ r'`.
* `euclidNorm_walkPos_succ_le`: `|S_{t+1}| ≤ |S_t| + 1`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

/-- The killed Green function of a finite set is monotone in the set. -/
theorem killedGreenReal_mono {A B : Finset (Site 2)} (h : A ⊆ B) (w z : Site 2) :
    Graph.killedGreenReal (lattice 2) (A : Set (Site 2)) w z ≤
      Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) w z := by
  have hheat : ∀ k x, Graph.killedHeat (lattice 2) (A : Set (Site 2)) k x z ≤
      Graph.killedHeat (lattice 2) (B : Set (Site 2)) k x z := by
    intro k
    induction k with
    | zero =>
      intro x
      by_cases hx : x ∈ A
      · rw [Network.killedHeat_zero, Network.killedHeat_zero, if_pos (Finset.mem_coe.2 hx),
          if_pos (Finset.mem_coe.2 (h hx))]
      · rw [Network.killedHeat_of_source_not_mem fun hx' => hx (Finset.mem_coe.1 hx')]
        exact Network.killedHeat_nonneg _ _ x z
    | succ k ih =>
      intro x
      by_cases hx : x ∈ A
      · rw [Network.killedHeat_succ, Network.killedHeat_succ, if_pos (Finset.mem_coe.2 hx),
          if_pos (Finset.mem_coe.2 (h hx))]
        gcongr with y _
        exact ih y
      · rw [Network.killedHeat_of_source_not_mem fun hx' => hx (Finset.mem_coe.1 hx')]
        exact Network.killedHeat_nonneg _ _ x z
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset B
  have hqA : q ∉ A := fun hqA => hq (h hqA)
  rw [Network.killedGreenReal_eq_tsum (Graph.Zd.latticeConnected 2) A hqA w z,
    Network.killedGreenReal_eq_tsum (Graph.Zd.latticeConnected 2) B hq w z]
  gcongr ?_ / _
  exact Summable.tsum_le_tsum (fun k => hheat k w)
    (Network.summable_killedHeat (Graph.Zd.latticeConnected 2) A hqA w z)
    (Network.summable_killedHeat (Graph.Zd.latticeConnected 2) B hq w z)

/-- The Green function `G_r` of the disk `C_r` is monotone in the radius. -/
theorem green_mono {r r' : ℝ} (h : r ≤ r') (w z : Site 2) : green r w z ≤ green r' w z := by
  have hsub : diskFinset r ⊆ diskFinset r' := by
    intro y hy
    rw [diskFinset, Finset.mem_filter] at hy ⊢
    exact ⟨mem_ballFinset_iff.2 ((mem_ballFinset_iff.1 hy.1).trans h), hy.2.trans_le h⟩
  exact mul_le_mul_of_nonneg_left (killedGreenReal_mono hsub w z) (by norm_num)

/-- **Lawler-Limic, Lemma 2 for the simple random walk.** One step changes the Euclidean norm
by at most one. -/
theorem euclidNorm_walkPos_succ_le (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    euclidNorm (walkPos x ω (t + 1)) ≤ euclidNorm (walkPos x ω t) + 1 := by
  have hnorm : ∀ y : Site 2,
      euclidNorm y = ‖(WithLp.toLp 2 fun i => ((y i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2))‖ :=
    fun y => by
      simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, euclidNorm]
  have htri : ∀ y y' : Site 2, euclidNorm (y + y') ≤ euclidNorm y + euclidNorm y' := by
    intro y y'
    have hadd : (WithLp.toLp 2 fun i => (((y + y') i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2)) =
        (WithLp.toLp 2 fun i => ((y i : ℤ) : ℝ)) + (WithLp.toLp 2 fun i => ((y' i : ℤ) : ℝ)) := by
      ext i
      simp
    rw [hnorm (y + y'), hnorm y, hnorm y', hadd]
    exact norm_add_le _ _
  have hdir : ∀ a : Dir 2, euclidNorm (dirVec a) = 1 := by
    rintro ⟨i, b⟩
    fin_cases i <;> cases b <;> simp [euclidNorm, dirVec]
  have hstep : walkPos x ω (t + 1) = walkPos x ω t + dirVec (ω t) := by
    simp only [walkPos, Finset.sum_range_succ, add_assoc]
  rw [hstep]
  exact (htri _ _).trans_eq (by rw [hdir])

end FiniteAvalanches.Walk.Beurling
