import FiniteAvalanches.Walk.Beurling.ReturnAxis
import LatticeProb.Walk.ExteriorDirichlet
import LatticeProb.Walk.PotentialKernelFourier

/-!
# Entering the real axis at a prescribed point

For the simple random walk on `ℤ²` started at `z`, the probability that the first positive-time
visit of the real axis is a visit to the axis point `w` is at most `C / |z - w|`
(Lawler and Limic (2004), Proposition 12, inequality (22)).

The route is the half-plane Green function.  For `w` on the axis and the unit vertical step
`e = (0, s)` pointing to the side of `z`, the function
`F(y) = a(y - w + e) - a(y - w - e)` of the potential kernel `a` vanishes on the axis, is
harmonic on that side away from `w + e`, and tends to zero at infinity.  It is nonnegative by the
maximum principle, and the probability of entering the axis at `w` within `t` steps is bounded by
`F / 4` by induction on `t`.

## Main declarations

* `potentialKernel_nonneg`: the planar potential kernel is nonnegative.
* `halfPlaneKernel`: the function `F` above.
* `halfPlaneKernel_nonneg`, `halfPlaneKernel_le`: `0 ≤ F` on its half-plane and `F ≤ C / |y - w|`.
* `prob_entersBy_le`: `P^y(S enters the axis at w within t steps) ≤ F(y) / 4`.
* `axis_entry_point_le`: the bound `C / n` for `|z - w| ≥ n` and `w` on the axis.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

private theorem prob_nonneg (E : Set (ℕ → Dir 2)) : 0 ≤ prob E := ENNReal.toReal_nonneg

private theorem prob_mono {E F : Set (ℕ → Dir 2)} (h : E ⊆ F) : prob E ≤ prob F :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h)

/-! ### The potential kernel is nonnegative -/

/-- The planar potential kernel is nonnegative. -/
theorem potentialKernel_nonneg (x : Site 2) : 0 ≤ potentialKernel x := by
  rw [potentialKernel_eq_fourierPotential, ContinuousTime.fourierPotential]
  refine div_nonneg (integral_nonneg fun θ => ?_) (by positivity)
  have h1 : 0 ≤ 1 - Real.cos (dotSite θ x) := sub_nonneg.2 (Real.cos_le_one _)
  have h2 : 0 ≤ 1 - charFn 2 θ := by
    have h0 := Real.cos_le_one (θ 0)
    have h1 := Real.cos_le_one (θ 1)
    simp only [charFn, Fin.sum_univ_two]
    push_cast
    linarith
  exact div_nonneg h1 h2

private theorem euclidNorm_sq (x : Site 2) :
    euclidNorm x ^ 2 = ((x 0 : ℤ) : ℝ) ^ 2 + ((x 1 : ℤ) : ℝ) ^ 2 := by
  rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_two]

private theorem potentialKernel_approx :
    ∃ c₀ κ C R : ℝ, 0 < c₀ ∧ 0 ≤ C ∧ 1 ≤ R ∧ ∀ x : Site 2, R ≤ euclidNorm x →
      |potentialKernel x - (c₀ * Real.log (euclidNorm x) + κ)| ≤ C / euclidNorm x := by
  obtain ⟨κ, C, R, hR, h⟩ := exists_abs_potentialKernel_sub_log_le
  refine ⟨2 / Real.pi, κ, max C 0, R, div_pos two_pos Real.pi_pos, le_max_right _ _, hR,
    fun x hx => ?_⟩
  have hxpos : 0 < euclidNorm x := by linarith
  refine (h x hx).trans ?_
  have h2 : euclidNorm x ^ (-2 : ℝ) ≤ 1 / euclidNorm x := by
    rw [Real.rpow_neg hxpos.le, Real.rpow_two, one_div]
    exact inv_anti₀ hxpos (by nlinarith)
  calc C * euclidNorm x ^ (-2 : ℝ) ≤ max C 0 * euclidNorm x ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 / euclidNorm x) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max C 0 / euclidNorm x := by ring

/-! ### The half-plane kernel -/

/-- The unit vertical step `(0, s)`. -/
def vUnit (s : ℤ) : Site 2 := ![0, s]

@[simp] theorem vUnit_zero (s : ℤ) : vUnit s 0 = 0 := rfl

@[simp] theorem vUnit_one (s : ℤ) : vUnit s 1 = s := rfl

/-- The Green function of the half-plane on the side `s` of the real axis, with its pole at
`w + (0, s)`, in terms of the potential kernel: `a(y - w + e) - a(y - w - e)` for `e = (0, s)`. -/
def halfPlaneKernel (w : Site 2) (s : ℤ) (y : Site 2) : ℝ :=
  potentialKernel (y - (w - vUnit s)) - potentialKernel (y - (w + vUnit s))

theorem vUnit_neg (s : ℤ) : vUnit (-s) = -vUnit s := by
  funext i
  fin_cases i <;> rfl

/-- The half-plane kernel vanishes on the real axis. -/
theorem halfPlaneKernel_axis {w y : Site 2} (s : ℤ) (hw : w 1 = 0) (hy : y 1 = 0) :
    halfPlaneKernel w s y = 0 := by
  have h : y - (w - vUnit s) = axisRefl (y - (w + vUnit s)) := by
    ext i
    fin_cases i
    · simp [axisRefl]
    · simp only [Fin.mk_one, Pi.sub_apply, Pi.add_apply, vUnit_one, hw, hy, axisRefl,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
  rw [halfPlaneKernel, h, potentialKernel_axisRefl, sub_self]

/-- The half-plane kernel is harmonic off its two poles `w ± (0, s)`. -/
theorem nbrSum_halfPlaneKernel (w : Site 2) (s : ℤ) (y : Site 2) :
    nbrSum (halfPlaneKernel w s) y = 4 * halfPlaneKernel w s y
      + 4 * (if y = w - vUnit s then 1 else 0) - 4 * (if y = w + vUnit s then 1 else 0) := by
  have h1 := nbrSum_potentialKernel_sub (w - vUnit s) y
  have h2 := nbrSum_potentialKernel_sub (w + vUnit s) y
  have e : nbrSum (halfPlaneKernel w s) y =
      nbrSum (fun v => potentialKernel (v - (w - vUnit s))) y -
        nbrSum (fun v => potentialKernel (v - (w + vUnit s))) y := by
    simp only [nbrSum, halfPlaneKernel, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e, h1, h2, halfPlaneKernel]
  ring

/-! ### Bounds for the half-plane kernel -/

private theorem euclidNorm_add_le' (y z : Site 2) :
    euclidNorm (y + z) ≤ euclidNorm y + euclidNorm z := by
  have hnorm : ∀ x : Site 2,
      euclidNorm x = ‖(WithLp.toLp 2 fun i => ((x i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2))‖ :=
    fun x => by simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, euclidNorm]
  have hadd : (WithLp.toLp 2 fun i => (((y + z) i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2)) =
      (WithLp.toLp 2 fun i => ((y i : ℤ) : ℝ)) +
        (WithLp.toLp 2 fun i => ((z i : ℤ) : ℝ)) := by
    ext i
    simp
  rw [hnorm (y + z), hnorm y, hnorm z, hadd]
  exact norm_add_le _ _

private theorem euclidNorm_vUnit_le {s : ℤ} (hs : s = 1 ∨ s = -1) : euclidNorm (vUnit s) ≤ 1 := by
  have h := euclidNorm_sq (vUnit s)
  have hs2 : ((s : ℤ) : ℝ) ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [vUnit_zero, vUnit_one] at h
  push_cast at h
  nlinarith [euclidNorm_nonneg (vUnit s)]

private theorem one_le_euclidNorm_sub {w y : Site 2} (hw : w 1 = 0) (hy : y 1 ≠ 0) :
    1 ≤ euclidNorm (y - w) := by
  have h := abs_coord_le_euclidNorm (y - w) 1
  have h1 : (1 : ℝ) ≤ |(((y - w) 1 : ℤ) : ℝ)| := by
    have : (y - w) 1 ≠ 0 := by simpa [hw] using hy
    have := Int.one_le_abs this
    rw [← Int.cast_abs]
    exact_mod_cast this
  linarith

/-- Far from the pole the half-plane kernel is nonnegative up to `O(1 / |y - w|)` and at most
`O(1 / |y - w|)`. -/
private theorem halfPlaneKernel_far : ∃ c₀ C R₀ : ℝ, 0 < c₀ ∧ 0 ≤ C ∧ 1 ≤ R₀ ∧
    ∀ (s : ℤ) (w y : Site 2), (s = 1 ∨ s = -1) → w 1 = 0 → 0 < s * y 1 →
      R₀ + 1 ≤ euclidNorm (y - w) →
      -(2 * C / (euclidNorm (y - w) - 1)) ≤ halfPlaneKernel w s y ∧
      halfPlaneKernel w s y ≤ (8 * c₀ + 4 * C) / euclidNorm (y - w) := by
  obtain ⟨c₀, κ, C, R₀, hc₀, hC, hR₀, hpk⟩ := potentialKernel_approx
  refine ⟨c₀, C, R₀, hc₀, hC, hR₀, fun s w y hs hw hy hR => ?_⟩
  have hs2 : ((s : ℤ) : ℝ) ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hh1 : (1 : ℝ) ≤ (s : ℝ) * (y 1 : ℝ) := by
    have : (1 : ℤ) ≤ s * y 1 := hy
    exact_mod_cast this
  have hR2 : euclidNorm (y - w) ^ 2 =
      (((y 0 : ℤ) : ℝ) - ((w 0 : ℤ) : ℝ)) ^ 2 + ((y 1 : ℤ) : ℝ) ^ 2 := by
    rw [euclidNorm_sq]
    simp only [Pi.sub_apply, hw, Int.cast_sub, sub_zero]
  have hNp2 : euclidNorm (y - (w - vUnit s)) ^ 2 =
      (((y 0 : ℤ) : ℝ) - ((w 0 : ℤ) : ℝ)) ^ 2 + (((y 1 : ℤ) : ℝ) + s) ^ 2 := by
    rw [euclidNorm_sq]
    simp only [Pi.sub_apply, vUnit_zero, vUnit_one, hw, Int.cast_sub, Int.cast_zero, sub_zero]
    ring
  have hNm2 : euclidNorm (y - (w + vUnit s)) ^ 2 =
      (((y 0 : ℤ) : ℝ) - ((w 0 : ℤ) : ℝ)) ^ 2 + (((y 1 : ℤ) : ℝ) - s) ^ 2 := by
    rw [euclidNorm_sq]
    simp only [Pi.sub_apply, Pi.add_apply, vUnit_zero, vUnit_one, hw, Int.cast_sub, Int.cast_add,
      Int.cast_zero, zero_add]
    ring
  have hhR : (s : ℝ) * (y 1 : ℝ) ≤ euclidNorm (y - w) := by
    have h := abs_coord_le_euclidNorm (y - w) 1
    have h' : |(((y - w) 1 : ℤ) : ℝ)| = |((y 1 : ℤ) : ℝ)| := by simp [hw]
    rw [h'] at h
    rcases hs with rfl | rfl
    · simpa using (le_abs_self _).trans h
    · simpa using (neg_le_abs _).trans h
  set R := euclidNorm (y - w) with hRdef
  set Np := euclidNorm (y - (w - vUnit s)) with hNp
  set Nm := euclidNorm (y - (w + vUnit s)) with hNm
  set h := (s : ℝ) * (y 1 : ℝ) with hhdef
  have hNpR : Np ^ 2 = R ^ 2 + 2 * h + 1 := by rw [hNp2, hR2]; linear_combination hs2
  have hNmR : Nm ^ 2 = R ^ 2 - 2 * h + 1 := by rw [hNm2, hR2]; linear_combination hs2
  have hR2' : 2 ≤ R := by linarith
  have hNm0 : 0 ≤ Nm := euclidNorm_nonneg _
  have hNp0 : 0 ≤ Np := euclidNorm_nonneg _
  have hNm_ge : R - 1 ≤ Nm := by
    by_contra hlt
    push Not at hlt
    linarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < R - 1 + Nm)]
  have hNp_ge : Nm ≤ Np := by
    by_contra hlt
    push Not at hlt
    linarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < Nm + Np)]
  have hNm_pos : 0 < Nm := by linarith
  have hA := abs_le.1 (hpk (y - (w - vUnit s)) (by linarith))
  have hB := abs_le.1 (hpk (y - (w + vUnit s)) (by linarith))
  have hF : halfPlaneKernel w s y =
      potentialKernel (y - (w - vUnit s)) - potentialKernel (y - (w + vUnit s)) := rfl
  have hlog : Real.log Nm ≤ Real.log Np := Real.log_le_log hNm_pos hNp_ge
  have hCp : C / Np ≤ C / (R - 1) :=
    div_le_div_of_nonneg_left hC (by linarith) (by linarith)
  have hCm : C / Nm ≤ C / (R - 1) :=
    div_le_div_of_nonneg_left hC (by linarith) (by linarith)
  have hdiff : 0 ≤ c₀ * (Real.log Np - Real.log Nm) :=
    mul_nonneg hc₀.le (sub_nonneg.2 hlog)
  refine ⟨?_, ?_⟩
  · have e : 2 * C / (R - 1) = C / (R - 1) + C / (R - 1) := by ring
    rw [e, hF]
    linarith [hA.1, hA.2, hB.1, hB.2]
  · have hlogN : Real.log Np - Real.log Nm ≤ 2 * h / Nm ^ 2 := by
      have h2 : 2 * (Real.log Np - Real.log Nm) = Real.log (Np ^ 2 / Nm ^ 2) := by
        rw [Real.log_div (pow_pos (hNm_pos.trans_le hNp_ge) 2).ne' (pow_pos hNm_pos 2).ne',
          Real.log_pow, Real.log_pow]
        push_cast
        ring
      have h3 := Real.log_le_sub_one_of_pos
        (show 0 < Np ^ 2 / Nm ^ 2 from
          div_pos (pow_pos (hNm_pos.trans_le hNp_ge) 2) (pow_pos hNm_pos 2))
      have h4 : Np ^ 2 / Nm ^ 2 - 1 = 4 * h / Nm ^ 2 := by
        field_simp
        linarith
      rw [h4] at h3
      have : 2 * h / Nm ^ 2 = (4 * h / Nm ^ 2) / 2 := by ring
      linarith
    have hNm_half : R / 2 ≤ Nm := by linarith
    have hNm2' : R ^ 2 / 4 ≤ Nm ^ 2 := by
      have := pow_le_pow_left₀ (by linarith : 0 ≤ R / 2) hNm_half 2
      linarith
    have hR0 : 0 < R := by linarith
    have h1 : 2 * h / Nm ^ 2 ≤ 8 / R := by
      rw [div_le_div_iff₀ (pow_pos hNm_pos 2) hR0]
      have h7 : h * R ≤ R * R := mul_le_mul_of_nonneg_right hhR hR0.le
      linarith [h7, hNm2']
    have h2 : C / Nm ≤ 2 * C / R := by
      calc C / Nm ≤ C / (R / 2) := div_le_div_of_nonneg_left hC (by positivity) hNm_half
        _ = 2 * C / R := by field_simp
    have h3 : C / Np ≤ 2 * C / R :=
      (div_le_div_of_nonneg_left hC hNm_pos hNp_ge).trans h2
    have e : (8 * c₀ + 4 * C) / R = c₀ * (8 / R) + 2 * C / R + 2 * C / R := by ring
    rw [e, hF]
    have h5 : c₀ * (Real.log Np - Real.log Nm) ≤ c₀ * (8 / R) :=
      mul_le_mul_of_nonneg_left (hlogN.trans h1) hc₀.le
    linarith [hA.1, hA.2, hB.1, hB.2]

/-- The half-plane kernel is `O(1 / |y - w|)` on its half-plane. -/
theorem halfPlaneKernel_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℤ) (w y : Site 2), (s = 1 ∨ s = -1) →
    w 1 = 0 → 0 < s * y 1 → halfPlaneKernel w s y ≤ C / euclidNorm (y - w) := by
  obtain ⟨c₀, C, R₀, hc₀, hC, hR₀, hfar⟩ := halfPlaneKernel_far
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ v : Site 2, euclidNorm v ≤ R₀ + 3 →
      |potentialKernel v| ≤ M := by
    refine ⟨∑ v ∈ ballFinset 2 (R₀ + 3), |potentialKernel v|,
      Finset.sum_nonneg fun _ _ => abs_nonneg _, fun v hv => ?_⟩
    exact Finset.single_le_sum (f := fun v => |potentialKernel v|) (fun _ _ => abs_nonneg _)
      (mem_ballFinset_iff.2 hv)
  refine ⟨max (8 * c₀ + 4 * C) (2 * M * (R₀ + 1)), le_max_of_le_left (by positivity), ?_⟩
  intro s w y hs hw hy
  have hy1 : y 1 ≠ 0 := fun h => by simp [h] at hy
  have hR1 := one_le_euclidNorm_sub hw hy1
  by_cases hfarR : R₀ + 1 ≤ euclidNorm (y - w)
  · exact (hfar s w y hs hw hy hfarR).2.trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith))
  · push Not at hfarR
    have hs' : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> simp
    have e1 : y - (w - vUnit s) = (y - w) + vUnit s := by abel
    have e2 : y - (w + vUnit s) = (y - w) + vUnit (-s) := by
      rw [vUnit_neg]; abel
    have hn1 : euclidNorm (y - (w - vUnit s)) ≤ R₀ + 3 := by
      rw [e1]
      linarith [euclidNorm_add_le' (y - w) (vUnit s), euclidNorm_vUnit_le hs]
    have hn2 : euclidNorm (y - (w + vUnit s)) ≤ R₀ + 3 := by
      rw [e2]
      linarith [euclidNorm_add_le' (y - w) (vUnit (-s)), euclidNorm_vUnit_le hs']
    have hnear : halfPlaneKernel w s y ≤ 2 * M := by
      have a1 := hM _ hn1
      have a2 := hM _ hn2
      rw [halfPlaneKernel]
      linarith [le_abs_self (potentialKernel (y - (w - vUnit s))),
        neg_abs_le (potentialKernel (y - (w + vUnit s)))]
    refine hnear.trans ?_
    rw [le_div_iff₀ (by linarith)]
    have : 2 * M * (R₀ + 1) ≤ max (8 * c₀ + 4 * C) (2 * M * (R₀ + 1)) := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hfarR.le hM0]

/-- The maximum principle on a finite set of the lattice, for a function that is the mean of
its four neighbouring values on the set. -/
private theorem le_of_neighbour_mean (Λ : Finset (Site 2)) (g : Site 2 → ℝ) (M : ℝ)
    (hharm : ∀ y ∈ Λ, g y = (∑ a : Dir 2, g (y + dirVec a)) / 4)
    (hbd : ∀ y ∈ Λ, ∀ a : Dir 2, y + dirVec a ∉ Λ → g (y + dirVec a) ≤ M) :
    ∀ y ∈ Λ, g y ≤ M := by
  classical
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset Λ
  set g' : Site 2 → ℝ := fun x =>
    if x ∈ Λ ∨ ∃ y ∈ Λ, ∃ a : Dir 2, x = y + dirVec a then g x else M with hg'
  have hnear : ∀ y ∈ Λ, ∀ a : Dir 2, g' (y + dirVec a) = g (y + dirVec a) := fun y hy a => by
    have h : y + dirVec a ∈ Λ ∨ ∃ y' ∈ Λ, ∃ a' : Dir 2, y + dirVec a = y' + dirVec a' :=
      Or.inr ⟨y, hy, a, rfl⟩
    simp only [hg', h, ↓reduceIte]
  have hin : ∀ y ∈ Λ, g' y = g y := fun y hy => by
    simp only [hg', hy, true_or, ↓reduceIte]
  have key := le_of_harmonic_on_box (d := 2) (by norm_num) Λ ∅ g' M hq
    (fun y hy _ => by
      rw [walkOp_eq_sum_dir, hin y hy, hharm y hy,
        Finset.sum_congr rfl fun a _ => hnear y hy a]
      push_cast
      ring)
    (fun x hx => by
      by_cases h : x ∈ Λ ∨ ∃ y ∈ Λ, ∃ a : Dir 2, x = y + dirVec a
      · have hx' : g' x = g x := by simp only [hg', h, ↓reduceIte]
        rw [hx']
        rcases h with h | ⟨y, hy, a, rfl⟩
        · exact absurd h hx
        · exact hbd y hy a hx
      · have hx' : g' x = M := by simp only [hg', h, ↓reduceIte]
        rw [hx'])
    (fun x hx => absurd hx (Set.notMem_empty x))
  intro y hy
  rw [← hin y hy]
  exact key y

private theorem dirVec_apply_one (a : Dir 2) :
    dirVec a 1 = 0 ∨ dirVec a 1 = 1 ∨ dirVec a 1 = -1 := by
  rcases a with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp [dirVec]

private theorem side_nbr {s : ℤ} (hs : s = 1 ∨ s = -1) {v : Site 2} (hv : 0 < s * v 1)
    (a : Dir 2) (h0 : (v + dirVec a) 1 ≠ 0) : 0 < s * (v + dirVec a) 1 := by
  have hd := dirVec_apply_one a
  simp only [Pi.add_apply] at h0 ⊢
  rcases hs with rfl | rfl <;> rcases hd with hd | hd | hd <;> rw [hd] at h0 ⊢ <;> omega

private theorem ne_sub_vUnit {s : ℤ} (hs : s = 1 ∨ s = -1) {w y : Site 2} (hw : w 1 = 0)
    (hy : 0 < s * y 1) : y ≠ w - vUnit s := by
  intro h
  rw [h] at hy
  simp only [Pi.sub_apply, vUnit_one, hw] at hy
  rcases hs with rfl | rfl <;> omega

/-- **The half-plane kernel is nonnegative on its half-plane.**  It vanishes on the axis, is
harmonic away from its pole `w + (0, s)` where it is nonnegative, and is `O(1 / |y - w|)` at
infinity. -/
theorem halfPlaneKernel_nonneg {s : ℤ} (hs : s = 1 ∨ s = -1) {w y : Site 2} (hw : w 1 = 0)
    (hy : 0 < s * y 1) : 0 ≤ halfPlaneKernel w s y := by
  obtain ⟨c₀, C, R₀, hc₀, hC, hR₀, hfar⟩ := halfPlaneKernel_far
  have hpole : 0 ≤ halfPlaneKernel w s (w + vUnit s) := by
    have e1 : w + vUnit s - (w - vUnit s) = vUnit s + vUnit s := by abel
    rw [halfPlaneKernel, e1, sub_self, potentialKernel_zero, sub_zero]
    exact potentialKernel_nonneg _
  by_cases hyu : y = w + vUnit s
  · rw [hyu]
    exact hpole
  by_contra hneg
  push Not at hneg
  set δ := -halfPlaneKernel w s y with hδ
  have hδpos : 0 < δ := by linarith
  set L : ℝ := R₀ + 2 + euclidNorm (y - w) + 2 * C / δ with hL
  have hnorm0 := euclidNorm_nonneg (y - w)
  have hCδ : 0 ≤ 2 * C / δ := by positivity
  have hL1 : R₀ + 1 ≤ L := by linarith
  have hLy : euclidNorm (y - w) < L := by linarith
  have hL1' : 0 < L - 1 := by linarith
  have hM : 2 * C / (L - 1) < δ := by
    rw [div_lt_iff₀ hL1']
    have : δ * (2 * C / δ) = 2 * C := by field_simp
    nlinarith
  have hM0 : 0 ≤ 2 * C / (L - 1) := by positivity
  classical
  let Λ : Finset (Site 2) := ((diskFinset L).image (fun v => v + w)).filter
    (fun v => 0 < s * v 1 ∧ v ≠ w + vUnit s)
  have hΛ : ∀ v, v ∈ Λ ↔ euclidNorm (v - w) < L ∧ 0 < s * v 1 ∧ v ≠ w + vUnit s := by
    intro v
    simp only [Λ, Finset.mem_filter, Finset.mem_image, diskFinset, mem_ballFinset_iff]
    constructor
    · rintro ⟨⟨x, ⟨⟨hx1, hx2⟩, rfl⟩⟩, h3, h4⟩
      exact ⟨by simpa using hx2, h3, h4⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨v - w, ⟨⟨h1.le, h1⟩, by simp⟩⟩, h2, h3⟩
  have hyΛ : y ∈ Λ := (hΛ y).2 ⟨hLy, hy, hyu⟩
  have key := le_of_neighbour_mean Λ (fun v => -halfPlaneKernel w s v) (2 * C / (L - 1))
    (fun v hv => by
      show -halfPlaneKernel w s v = (∑ a : Dir 2, -halfPlaneKernel w s (v + dirVec a)) / 4
      obtain ⟨_, hv1, hv2⟩ := (hΛ v).1 hv
      have hn := nbrSum_halfPlaneKernel w s v
      have hne := ne_sub_vUnit hs hw hv1
      simp only [hne, hv2, ↓reduceIte] at hn
      simp only [Finset.sum_neg_distrib]
      rw [← nbrSum_eq_sum_dir, hn]
      ring)
    (fun v hv a hnot => by
      show -halfPlaneKernel w s (v + dirVec a) ≤ 2 * C / (L - 1)
      obtain ⟨_, hv1, hv2⟩ := (hΛ v).1 hv
      by_cases h0 : (v + dirVec a) 1 = 0
      · rw [halfPlaneKernel_axis s hw h0, neg_zero]
        exact hM0
      by_cases hu : v + dirVec a = w + vUnit s
      · rw [hu]
        linarith
      have hv' := side_nbr hs hv1 a h0
      have hfn : ¬ euclidNorm (v + dirVec a - w) < L := fun h => hnot ((hΛ _).2 ⟨h, hv', hu⟩)
      push Not at hfn
      have h1 := (hfar s w (v + dirVec a) hs hw hv' (by linarith)).1
      have h2 : 2 * C / (euclidNorm (v + dirVec a - w) - 1) ≤ 2 * C / (L - 1) :=
        div_le_div_of_nonneg_left (by positivity) hL1' (by linarith)
      linarith)
    y hyΛ
  have key' : -halfPlaneKernel w s y ≤ 2 * C / (L - 1) := key
  linarith

/-! ### Entering the axis at a prescribed point within a bounded time -/

/-- The walk from `x` is at `w` at some time `s` with `1 ≤ s ≤ t`, and has not been on the real
axis at the times `1, …, s - 1`. -/
def entersBy (w x : Site 2) (t : ℕ) : Set (ℕ → Dir 2) :=
  {ω | ∃ s, 1 ≤ s ∧ s ≤ t ∧ walkPos x ω s = w ∧ ∀ r, 1 ≤ r → r < s → walkPos x ω r 1 ≠ 0}

theorem measurableSet_entersBy (w x : Site 2) (t : ℕ) : MeasurableSet (entersBy w x t) :=
  measurableSet_setOf.2 <| Measurable.exists fun s =>
    (measurable_const (a := 1 ≤ s)).and <| (measurable_const (a := s ≤ t)).and <|
      (measurable_walkPos_pred x (· = w) s).and <| Measurable.forall fun r =>
        measurable_walkPos_pred x (fun z => 1 ≤ r → r < s → z 1 ≠ 0) r

theorem entersBy_mono (w x : Site 2) {t t' : ℕ} (h : t ≤ t') : entersBy w x t ⊆ entersBy w x t' :=
  fun _ ⟨s, hs1, hs2, hs3, hs4⟩ => ⟨s, hs1, hs2.trans h, hs3, hs4⟩

theorem entersAt_axisSet_univ_eq (w x : Site 2) :
    entersAt (axisSet Set.univ) w x = ⋃ t, entersBy w x t := by
  ext ω
  simp only [entersAt, entersBy, axisSet, Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ,
    and_true]
  constructor
  · rintro ⟨t, ht1, ht2, ht3⟩
    exact ⟨t, t, ht1, le_rfl, ht2, ht3⟩
  · rintro ⟨t, s, hs1, hs2, hs3, hs4⟩
    exact ⟨s, hs1, hs3, hs4⟩

/-- The first-step recursion for `entersBy`. -/
theorem prob_entersBy_succ {w : Site 2} (hw : w 1 = 0) (y : Site 2) (t : ℕ) :
    prob (entersBy w y (t + 1)) = ∑ a : Dir 2, (1 / 4 : ℝ) *
      (if y + dirVec a = w then 1 else
        if (y + dirVec a) 1 = 0 then 0 else prob (entersBy w (y + dirVec a) t)) := by
  classical
  let F : Dir 2 → Set (ℕ → Dir 2) := fun a =>
    if y + dirVec a = w then Set.univ else
      if (y + dirVec a) 1 = 0 then ∅ else entersBy w (y + dirVec a) t
  have hF : ∀ a, MeasurableSet (F a) := fun a => by
    simp only [F]
    split_ifs
    · exact MeasurableSet.univ
    · exact MeasurableSet.empty
    · exact measurableSet_entersBy _ _ _
  have hset : entersBy w y (t + 1) = {ω | shiftBy 1 ω ∈ F (ω 0)} := by
    ext ω
    have hs1 : walkPos y ω 1 = y + dirVec (ω 0) := by
      have := walkPos_succ_eq_shiftBy y ω 0
      rw [walkPos_at_zero] at this
      simpa using this
    constructor
    · rintro ⟨s, hs1', hst, hpos, hav⟩
      show shiftBy 1 ω ∈ F (ω 0)
      rcases Nat.eq_or_lt_of_le hs1' with h | h
      · subst h
        rw [hs1] at hpos
        simp only [F, hpos, ↓reduceIte, Set.mem_univ]
      · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
        have h1 : (y + dirVec (ω 0)) 1 ≠ 0 := by
          have := hav 1 le_rfl (by omega)
          rwa [hs1] at this
        have h2 : y + dirVec (ω 0) ≠ w := fun h => h1 (by rw [h]; exact hw)
        simp only [F, h2, h1, ↓reduceIte]
        refine ⟨s', by omega, by omega, ?_, fun r hr1 hr2 => ?_⟩
        · rw [walkPos_succ_eq_shiftBy] at hpos
          exact hpos
        · have := hav (r + 1) (by omega) (by omega)
          rw [walkPos_succ_eq_shiftBy] at this
          exact this
    · intro h
      change shiftBy 1 ω ∈ F (ω 0) at h
      by_cases h1 : y + dirVec (ω 0) = w
      · exact ⟨1, le_rfl, by omega, by rw [hs1, h1], fun r hr1 hr2 => by omega⟩
      · by_cases h2 : (y + dirVec (ω 0)) 1 = 0
        · simp only [F, h1, h2, ↓reduceIte] at h
          exact absurd h (Set.notMem_empty _)
        · simp only [F, h1, h2, ↓reduceIte] at h
          obtain ⟨s', hs1', hst, hpos, hav⟩ := h
          refine ⟨s' + 1, by omega, by omega, ?_, fun r hr1 hr2 => ?_⟩
          · rw [walkPos_succ_eq_shiftBy]
            exact hpos
          · rcases Nat.eq_or_lt_of_le hr1 with h3 | h3
            · subst h3
              rw [hs1]
              exact h2
            · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
              rw [walkPos_succ_eq_shiftBy]
              exact hav r' (by omega) (by omega)
  rw [hset, prob_firstStep F hF]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [F]
  split_ifs
  · exact prob_univ
  · exact prob_empty
  · rfl

private theorem site_ext_iff (u v : Site 2) : u = v ↔ u 0 = v 0 ∧ u 1 = v 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1

private theorem sum_dir_eq_pole {s : ℤ} (hs : s = 1 ∨ s = -1) {w y : Site 2} (hw : w 1 = 0)
    (hy : 0 < s * y 1) :
    (∑ a : Dir 2, if y + dirVec a = w then (1 : ℝ) else 0) = if y = w + vUnit s then 1 else 0 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, Fintype.sum_bool,
    dirVec_eq_unit, dirVec_eq_neg_unit, dirVec_eq_unit, dirVec_eq_neg_unit]
  simp only [site_ext_iff, Pi.add_apply, Pi.neg_apply, unit, Pi.single_apply, vUnit_zero,
    vUnit_one]
  rcases hs with rfl | rfl <;> split_ifs <;> first | omega | norm_num

/-- **The bound by the half-plane kernel.**  The probability that the walk started on the side
`s` of the axis enters the axis at `w` within `t` steps is at most `F / 4`. -/
theorem prob_entersBy_le {s : ℤ} (hs : s = 1 ∨ s = -1) {w : Site 2} (hw : w 1 = 0) :
    ∀ (t : ℕ) (y : Site 2), 0 < s * y 1 → prob (entersBy w y t) ≤ halfPlaneKernel w s y / 4 := by
  intro t
  induction t with
  | zero =>
    intro y hy
    have h : entersBy w y 0 = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun ω hω => by
        obtain ⟨r, hr1, hr2, -⟩ := hω
        omega
    rw [h, prob_empty]
    linarith [halfPlaneKernel_nonneg hs hw hy]
  | succ t ih =>
    intro y hy
    rw [prob_entersBy_succ hw]
    have hterm : ∀ a : Dir 2, (1 / 4 : ℝ) * (if y + dirVec a = w then 1 else
        if (y + dirVec a) 1 = 0 then 0 else prob (entersBy w (y + dirVec a) t)) ≤
        (1 / 4) * (halfPlaneKernel w s (y + dirVec a) / 4 +
          (if y + dirVec a = w then 1 else 0)) := fun a => by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      by_cases h1 : y + dirVec a = w
      · simp only [h1, halfPlaneKernel_axis s hw hw, ↓reduceIte]
        norm_num
      · by_cases h2 : (y + dirVec a) 1 = 0
        · have h3 := halfPlaneKernel_axis s hw h2 (w := w) (y := y + dirVec a)
          simp only [h1, h2, h3, ↓reduceIte]
          norm_num
        · have := ih (y + dirVec a) (side_nbr hs hy a h2)
          simp only [h1, h2, ↓reduceIte]
          linarith
    refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div, sum_dir_eq_pole hs hw hy]
    have hn := nbrSum_halfPlaneKernel w s y
    have hne := ne_sub_vUnit hs hw hy
    rw [nbrSum_eq_sum_dir] at hn
    simp only [hne, ↓reduceIte] at hn
    split_ifs at hn ⊢ <;> linarith

/-- The probability of entering the axis at `w` is at most `B` once every bounded-time version
is. -/
theorem prob_entersAt_le_of_forall {w z : Site 2} {B : ℝ} (h : ∀ t, prob (entersBy w z t) ≤ B) :
    prob (entersAt (axisSet Set.univ) w z) ≤ B := by
  have hB : 0 ≤ B := (prob_nonneg _).trans (h 0)
  have hmono : Monotone fun t => entersBy w z t := fun a b hab => entersBy_mono w z hab
  rw [entersAt_axisSet_univ_eq, prob, hmono.measure_iUnion]
  refine ENNReal.toReal_le_of_le_ofReal hB (iSup_le fun t => ?_)
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).2 (h t)

private theorem euclidNorm_neg' (x : Site 2) : euclidNorm (-x) = euclidNorm x := by
  simp [euclidNorm]

private theorem euclidNorm_dirVec_le (a : Dir 2) : euclidNorm (dirVec a) ≤ 1 := by
  have h := euclidNorm_sq (dirVec a)
  have : ((dirVec a 0 : ℤ) : ℝ) ^ 2 + ((dirVec a 1 : ℤ) : ℝ) ^ 2 = 1 := by
    rcases a with ⟨i, b⟩
    fin_cases i <;> cases b <;> simp [dirVec]
  nlinarith [euclidNorm_nonneg (dirVec a)]

/-- **Entering the real axis at a prescribed point** (Lawler and Limic (2004), Proposition 12,
inequality (22), for a target `w` on the real axis): the walk started at `z` first visits the
real axis at `w` with probability at most `C / n` when `|z - w| ≥ n`. -/
theorem axis_entry_point_le : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (z w : Site 2), 1 ≤ n →
    w ∈ axisSet Set.univ → (n : ℝ) ≤ euclidNorm (z - w) →
      prob (entersAt (axisSet Set.univ) w z) ≤ C / n := by
  obtain ⟨C₂, hC₂, hle⟩ := halfPlaneKernel_le
  refine ⟨max 1 (C₂ / 2), lt_max_of_lt_left one_pos, ?_⟩
  intro n z w hn hw' hR
  have hw : w 1 = 0 := hw'.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK1 : (1 : ℝ) ≤ max 1 (C₂ / 2) := le_max_left _ _
  have hK2 : C₂ / 2 ≤ max 1 (C₂ / 2) := le_max_right _ _
  -- the bound from a start off the axis
  have hoff : ∀ (y : Site 2), y 1 ≠ 0 → (n : ℝ) / 2 ≤ euclidNorm (y - w) →
      ∀ t, prob (entersBy w y t) ≤ C₂ / 2 / n := by
    intro y hy1 hR' t
    have hside : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ 0 < s * y 1 := by
      rcases lt_or_gt_of_ne hy1 with h | h
      · exact ⟨-1, Or.inr rfl, by omega⟩
      · exact ⟨1, Or.inl rfl, by omega⟩
    obtain ⟨s, hs, hsy⟩ := hside
    have h1 := prob_entersBy_le hs hw t y hsy
    have h2 := hle s w y hs hw hsy
    have hRpos : 0 < euclidNorm (y - w) := by linarith
    have h3 : C₂ / euclidNorm (y - w) ≤ C₂ / (n / 2) :=
      div_le_div_of_nonneg_left hC₂ (by positivity) hR'
    have h4 : C₂ / (n / 2) = 2 * C₂ / n := by field_simp
    have h5 : 2 * C₂ / (n : ℝ) = 4 * (C₂ / 2 / n) := by field_simp; ring
    have h6 : 0 ≤ C₂ / 2 / (n : ℝ) := by positivity
    linarith
  by_cases hz : z 1 = 0
  · refine prob_entersAt_le_of_forall fun t => ?_
    cases t with
    | zero =>
      have h : entersBy w z 0 = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun ω hω => by
          obtain ⟨r, hr1, hr2, -⟩ := hω
          omega
      rw [h, prob_empty]
      positivity
    | succ t =>
      rw [prob_entersBy_succ hw]
      have hterm : ∀ a : Dir 2, (1 / 4 : ℝ) * (if z + dirVec a = w then 1 else
          if (z + dirVec a) 1 = 0 then 0 else prob (entersBy w (z + dirVec a) t)) ≤
          (1 / 4) * (max 1 (C₂ / 2) / n) := fun a => by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have hK : C₂ / 2 / (n : ℝ) ≤ max 1 (C₂ / 2) / n :=
          div_le_div_of_nonneg_right hK2 hn0.le
        by_cases h1 : z + dirVec a = w
        · have hzw : z - w = -dirVec a := by rw [← h1]; abel
          have : euclidNorm (z - w) ≤ 1 := by
            rw [hzw, euclidNorm_neg']
            exact euclidNorm_dirVec_le a
          have hn1' : (n : ℝ) ≤ 1 := hR.trans this
          simp only [h1, ↓reduceIte]
          rw [le_div_iff₀ hn0]
          linarith
        · by_cases h2 : (z + dirVec a) 1 = 0
          · simp only [h1, h2, ↓reduceIte]
            positivity
          · simp only [h1, h2, ↓reduceIte]
            refine (hoff _ h2 ?_ t).trans hK
            have htri : euclidNorm (z - w) ≤ euclidNorm (z + dirVec a - w) + 1 := by
              have e : z - w = (z + dirVec a - w) + -dirVec a := by abel
              rw [e]
              refine (euclidNorm_add_le' _ _).trans ?_
              rw [euclidNorm_neg']
              linarith [euclidNorm_dirVec_le a]
            have hone := one_le_euclidNorm_sub hw h2
            linarith
      refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      push_cast
      linarith
  · refine prob_entersAt_le_of_forall fun t => ?_
    have h := hoff z hz (by linarith) t
    exact h.trans (div_le_div_of_nonneg_right hK2 hn0.le)

end FiniteAvalanches.Walk.Beurling
