import FiniteAvalanches.Walk.Beurling.StripExit
import FiniteAvalanches.Walk.Beurling.DiskGreenBasic
import LatticeProb.Network.FirstReturn
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Walk.Harnack.Basics

/-!
# Returning to a point before the real axis

For the simple random walk on `ℤ²` started at `z`, let `q(z)` be the probability that the first
positive-time visit to `{z} ∪ ℤ` is a visit to `z`, where `ℤ` is the real axis. This file proves
the bound `q(z) ≤ 1 - c / log n` of Lawler and Limic (2004), Lemma 11 (b), for the points `z`
whose height is at most `n`: there are `c > 0` and `N` such that `q(z) ≤ 1 - c / log n` for
`n ≥ N` and `|Im z| ≤ n`. On the axis the event includes a simultaneous first visit to `z` and
to the axis.

G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*, Electron. J.
Probab. 9 (2004), Lemma 11 (b).

## Main statements

* `potentialKernel_axisRefl`: the potential kernel is invariant under the reflection `axisRefl`
  in the real axis.
* `four_mul_killedGreenReal_halfDisk_le`: the expected number of visits to `z` before the walk
  leaves the half-disk `halfDisk z R` is at most `a(z - z̄) + 1` for large `R`.
* `prob_returnEvent_le`: the renewal bound `P_z(T_z < τ_B) ≤ 1 - 1 / G_B(z, z)`.
* `return_before_axis`: Lemma 11 (b) for the points of height at most `n`.

## Proof

Let `h = Im z ≠ 0` and let `z̄` be the reflection of `z`. On the half-plane on the side of `z`,
the function `x ↦ a(x - z̄) - a(x - z)` has Laplacian `-δ_z`, it vanishes on the axis by the
symmetry of `a`, and the asymptotics `a(x) = (2/π) log |x| + κ + O(|x|⁻²)` make it at least
`-1` far from `z`. The maximum principle bounds the Green function `G_B(z, z)` of every large
half-disk `B` around `z` by `a(z - z̄) + 1 = a(2ih) + 1 ≤ A + log |h|`. Through the renewal
identity, the walk returns to `z` before leaving `B` with probability at most
`1 - 1 / G_B(z, z)`. Before its first visit to the axis the walk stays on the side of `z`, so the
event is the increasing union over the half-disks of these return events. At height `0`, a first
horizontal step reaches the axis away from `z`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

open MeasureTheory

/-! ### Reflection in the real axis -/

/-- The reflection `x ↦ x̄` of `ℤ²` in the real axis. -/
def axisRefl (x : Site 2) : Site 2 := ![x 0, -x 1]

@[simp] theorem axisRefl_apply_zero (x : Site 2) : axisRefl x 0 = x 0 := rfl

@[simp] theorem axisRefl_apply_one (x : Site 2) : axisRefl x 1 = -x 1 := rfl

theorem axisRefl_add (x y : Site 2) : axisRefl (x + y) = axisRefl x + axisRefl y := by
  ext i
  fin_cases i <;> simp [axisRefl]
  ring

theorem axisRefl_axisRefl (x : Site 2) : axisRefl (axisRefl x) = x := by
  ext i
  fin_cases i <;> simp [axisRefl]

/-- The reflection of the directions: the two vertical directions are exchanged. -/
def dirRefl (a : Dir 2) : Dir 2 := if a.1 = 1 then (a.1, !a.2) else a

theorem dirRefl_dirRefl (a : Dir 2) : dirRefl (dirRefl a) = a := by
  rcases a with ⟨i, b⟩
  fin_cases i <;> cases b <;> rfl

theorem dirVec_dirRefl (a : Dir 2) : dirVec (dirRefl a) = axisRefl (dirVec a) := by
  rcases a with ⟨i, b⟩
  fin_cases i <;> cases b <;> ext j <;> fin_cases j <;> simp [dirVec, dirRefl, axisRefl]

/-- The heat kernel of the walk is invariant under the reflection in the real axis. -/
theorem srwHeat_axisRefl (n : ℕ) (x : Site 2) : srwHeat 2 n (axisRefl x) = srwHeat 2 n x := by
  classical
  induction n generalizing x with
  | zero =>
    have h : axisRefl x = 0 ↔ x = 0 := by
      constructor
      · intro h
        rw [← axisRefl_axisRefl x, h]
        ext i
        fin_cases i <;> simp [axisRefl]
      · rintro rfl
        ext i
        fin_cases i <;> simp [axisRefl]
    simp [h]
  | succ n ih =>
    rw [srwHeat_succ_eq_sum_dir, srwHeat_succ_eq_sum_dir]
    congr 1
    refine Finset.sum_nbij' dirRefl dirRefl (fun a _ => Finset.mem_univ _)
      (fun a _ => Finset.mem_univ _) (fun a _ => dirRefl_dirRefl a) (fun a _ => dirRefl_dirRefl a)
      fun a _ => ?_
    rw [dirVec_dirRefl, ← ih (axisRefl x + dirVec a), axisRefl_add, axisRefl_axisRefl]

/-- **The potential kernel is symmetric in the real axis**: `a(x̄) = a(x)`. -/
theorem potentialKernel_axisRefl (x : Site 2) :
    potentialKernel (axisRefl x) = potentialKernel x := by
  have h : (fun M : ℕ => srwGreen 2 M 0 - srwGreen 2 M (axisRefl x)) =
      fun M => srwGreen 2 M 0 - srwGreen 2 M x := by
    funext M
    simp only [srwGreen, srwHeat_axisRefl]
  rw [potentialKernel, potentialKernel, h]

/-- The potential kernel centred at `z` solves `(P - I) a(· - z) = δ_z`. -/
theorem nbrSum_potentialKernel_sub (z x : Site 2) :
    nbrSum (fun y => potentialKernel (y - z)) x =
      4 * potentialKernel (x - z) + 4 * if x = z then 1 else 0 := by
  have h := walkOp_potentialKernel_sub (x - z)
  have e : nbrSum (fun y => potentialKernel (y - z)) x = nbrSum potentialKernel (x - z) := by
    simp only [nbrSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_sub_right_comm, sub_right_comm]
  rw [e]
  rw [walkOp] at h
  simp only [sub_eq_zero] at h
  push_cast at h
  split_ifs at h ⊢ <;> linarith

/-! ### Half-disks -/

private theorem euclidNorm_add_le (y z : Site 2) :
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

/-- The sites on the side of `z` of the real axis at distance less than `R` from `z`. -/
def halfDisk (z : Site 2) (R : ℝ) : Finset (Site 2) :=
  (ballFinset 2 (euclidNorm z + R)).filter fun w => 0 < w 1 * z 1 ∧ euclidNorm (w - z) < R

theorem mem_halfDisk {z w : Site 2} {R : ℝ} :
    w ∈ halfDisk z R ↔ 0 < w 1 * z 1 ∧ euclidNorm (w - z) < R := by
  rw [halfDisk, Finset.mem_filter, mem_ballFinset_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have := euclidNorm_add_le z (w - z)
  rw [add_sub_cancel] at this
  linarith [h.2]

theorem halfDisk_mono (z : Site 2) {R R' : ℝ} (h : R ≤ R') : halfDisk z R ⊆ halfDisk z R' :=
  fun _ hw => mem_halfDisk.2 ⟨(mem_halfDisk.1 hw).1, (mem_halfDisk.1 hw).2.trans_le h⟩

/-! ### The Green function of a half-disk -/

private theorem norm_le_norm_sub_axisRefl {y z : Site 2} (hy : 0 < y 1 * z 1) :
    euclidNorm (y - z) ≤ euclidNorm (y - axisRefl z) := by
  unfold euclidNorm
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_two, Pi.sub_apply, axisRefl_apply_zero, axisRefl_apply_one,
    Int.cast_sub, Int.cast_neg]
  have : (0 : ℝ) < (y 1 : ℝ) * (z 1 : ℝ) := by exact_mod_cast hy
  nlinarith

private theorem rpow_neg_two_le_inv {e R : ℝ} (hR : 1 ≤ R) (he : R ≤ e) :
    e ^ (-2 : ℝ) ≤ R⁻¹ := by
  have he0 : 0 ≤ e := by linarith
  rw [Real.rpow_neg he0, Real.rpow_two]
  exact inv_anti₀ (by linarith) (by nlinarith)

/-- **The Green function of a half-disk.** For large `R`, four times the killed Green function of
`halfDisk z R` at `(z, z)`, the expected number of visits to `z` before the walk leaves the
half-disk, is at most `a(z - z̄) + 1`. -/
theorem four_mul_killedGreenReal_halfDisk_le : ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ z : Site 2, z 1 ≠ 0 →
    ∀ R : ℝ, R₀ ≤ R → 4 * Graph.killedGreenReal (lattice 2) (halfDisk z R : Set (Site 2)) z z ≤
      potentialKernel (z - axisRefl z) + 1 := by
  obtain ⟨κ, C, R₁, hR₁, hC⟩ := exists_abs_potentialKernel_sub_log_le
  refine ⟨R₁ + 2 * |C|, by linarith [abs_nonneg C], fun z hz R hR => ?_⟩
  have hR1 : 1 ≤ R := by linarith [abs_nonneg C]
  set B := halfDisk z R with hBdef
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) B
  have hG := Graph.Zd.latticeConnected 2
  have hzz : 0 < z 1 * z 1 := mul_self_pos.2 hz
  have hzB : z ∈ B := mem_halfDisk.2 ⟨hzz, by simp; linarith⟩
  -- far from `z`, on the side of `z`
  have hfar : ∀ y : Site 2, 0 < y 1 * z 1 → R ≤ euclidNorm (y - z) →
      potentialKernel (y - z) - potentialKernel (y - axisRefl z) ≤ 1 := by
    intro y hy hyR
    have hle := norm_le_norm_sub_axisRefl hy
    have h1 := abs_le.1 (hC (y - z) (by linarith [abs_nonneg C]))
    have h2 := abs_le.1 (hC (y - axisRefl z) (by linarith [abs_nonneg C]))
    have hlog : Real.log (euclidNorm (y - z)) ≤ Real.log (euclidNorm (y - axisRefl z)) :=
      Real.log_le_log (by linarith) hle
    have hlog' : 2 / Real.pi * Real.log (euclidNorm (y - z)) ≤
        2 / Real.pi * Real.log (euclidNorm (y - axisRefl z)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have he1 := rpow_neg_two_le_inv hR1 hyR
    have he2 := rpow_neg_two_le_inv hR1 (hyR.trans hle)
    have hp1 : 0 ≤ euclidNorm (y - z) ^ (-2 : ℝ) := Real.rpow_nonneg (euclidNorm_nonneg _) _
    have hp2 : 0 ≤ euclidNorm (y - axisRefl z) ^ (-2 : ℝ) :=
      Real.rpow_nonneg (euclidNorm_nonneg _) _
    have hc1 : C * euclidNorm (y - z) ^ (-2 : ℝ) ≤ |C| * R⁻¹ :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) hp1).trans
        (mul_le_mul_of_nonneg_left he1 (abs_nonneg C))
    have hc2 : C * euclidNorm (y - axisRefl z) ^ (-2 : ℝ) ≤ |C| * R⁻¹ :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) hp2).trans
        (mul_le_mul_of_nonneg_left he2 (abs_nonneg C))
    have hCR : |C| * R⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
      linarith
    linarith [h1.1, h1.2, h2.1, h2.2]
  -- on the axis
  have haxis : ∀ y : Site 2, y 1 = 0 →
      potentialKernel (y - z) = potentialKernel (y - axisRefl z) := by
    intro y hy
    have e : y - axisRefl z = axisRefl (y - z) := by
      ext i
      fin_cases i <;> simp [axisRefl, hy]
    rw [e, potentialKernel_axisRefl]
  -- the comparison function
  set φ : Site 2 → ℝ := fun x =>
    if 0 ≤ x 1 * z 1 then potentialKernel (x - axisRefl z) - potentialKernel (x - z) else 0
    with hφ
  set g : Site 2 → ℝ := fun y => Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) y z
    with hg
  set v : Site 2 → ℝ := fun x => 4 * g x - φ x with hv
  have hsym : ∀ y, g y = Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) z y :=
    fun y => Network.killedGreenReal_symm hG B hq y z
  have hK : ∀ x ∈ B, nbrSum g x = 4 * g x - if x = z then 1 else 0 := by
    intro x hx
    have hl := Network.laplacian_killedGreenReal hG B hzB hq (v := x) (by exact_mod_cast hx)
    rw [laplacian_eq_nbrSum_sub (d := 2) (by norm_num)] at hl
    have hfun : g = Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) z := funext hsym
    rw [hfun]
    push_cast at hl
    split_ifs at hl ⊢ <;> linarith
  have hnbr : ∀ x ∈ B, ∀ i : Fin 2, 0 ≤ (x + unit i) 1 * z 1 ∧ 0 ≤ (x - unit i) 1 * z 1 := by
    intro x hx i
    have hxz := (mem_halfDisk.1 hx).1
    have hu : (unit i : Site 2) 1 = 0 ∨ (unit i : Site 2) 1 = 1 := by
      fin_cases i <;> simp [unit]
    simp only [Pi.add_apply, Pi.sub_apply]
    rcases lt_trichotomy (z 1) 0 with hz0 | hz0 | hz0
    · have : x 1 < 0 := by
        by_contra hc
        have := not_lt.1 hc
        nlinarith
      rcases hu with hu | hu <;> rw [hu] <;> constructor <;> nlinarith
    · exact absurd hz0 hz
    · have : 0 < x 1 := by
        by_contra hc
        have := not_lt.1 hc
        nlinarith
      rcases hu with hu | hu <;> rw [hu] <;> constructor <;> nlinarith
  have hharm : ∀ x ∈ B, nbrSum v x = 4 * v x := by
    intro x hx
    have hxz := (mem_halfDisk.1 hx).1
    have hxr : x ≠ axisRefl z := by
      rintro rfl
      simp only [axisRefl_apply_one] at hxz
      nlinarith
    have hφx : φ x = potentialKernel (x - axisRefl z) - potentialKernel (x - z) :=
      if_pos hxz.le
    have hφn : nbrSum φ x = nbrSum (fun y => potentialKernel (y - axisRefl z)) x -
        nbrSum (fun y => potentialKernel (y - z)) x := by
      simp only [nbrSum, Fin.sum_univ_two, hφ]
      rw [if_pos (hnbr x hx 0).1, if_pos (hnbr x hx 0).2, if_pos (hnbr x hx 1).1,
        if_pos (hnbr x hx 1).2]
      ring
    have hlin : nbrSum v x = 4 * nbrSum g x - nbrSum φ x := by
      simp only [hv, nbrSum, Fin.sum_univ_two]
      ring
    rw [hlin, hφn, hK x hx, nbrSum_potentialKernel_sub, nbrSum_potentialKernel_sub,
      if_neg hxr]
    simp only [hv, hφx]
    split_ifs <;> ring
  have hout : ∀ x, x ∉ B → v x ≤ 1 := by
    intro x hx
    have hgx : g x = 0 := by
      rw [hsym x]
      exact Network.killedGreenReal_eq_zero_of_not_mem hG B hq hx z
    simp only [hv, hgx, mul_zero, zero_sub, hφ]
    split_ifs with h0
    · rcases h0.lt_or_eq with h0 | h0
      · have hR' : R ≤ euclidNorm (x - z) := by
          by_contra hc
          exact hx (mem_halfDisk.2 ⟨h0, not_le.1 hc⟩)
        linarith [hfar x h0 hR']
      · have hx1 : x 1 = 0 := by
          rcases mul_eq_zero.1 h0.symm with h | h
          · exact h
          · exact absurd h hz
        rw [haxis x hx1]
        simp
    · norm_num
  have hmax := Network.le_of_harmonicOn hG Network.isCond_unitCond B ∅ v 1 hq
    (fun x hx _ => by
      rw [Network.netLaplacian_unitCond, laplacian_eq_nbrSum_sub (d := 2) (by norm_num),
        hharm x hx]
      push_cast
      ring)
    hout (fun x hx => absurd hx (Set.notMem_empty x)) z
  have hφz : φ z = potentialKernel (z - axisRefl z) := by
    rw [hφ]
    simp only [if_pos hzz.le, sub_self, potentialKernel_zero, sub_zero]
  have : v z = 4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) z z -
      potentialKernel (z - axisRefl z) := by
    simp only [hv, hg, hφz]
  linarith

/-! ### The renewal bound -/

theorem walkPos_at_zero (x : Site 2) (ω : ℕ → Dir 2) : walkPos x ω 0 = x := by
  simp [walkPos]

theorem walkPos_succ_eq_shiftBy (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos x ω (t + 1) = walkPos (x + dirVec (ω 0)) (shiftBy 1 ω) t := by
  simp only [walkPos, shiftBy, Finset.sum_range_succ']
  have h : ∀ j : ℕ, 1 + j = j + 1 := fun j => Nat.add_comm 1 j
  simp only [h]
  abel

private theorem sum_quarter_eq_graphWalkOp (f : Site 2 → ℝ) (x : Site 2) :
    ∑ a : Dir 2, (1 / 4 : ℝ) * f (x + dirVec a) =
      (∑ y ∈ (lattice 2).neighborFinset x, f y) / ((lattice 2).degree x : ℝ) := by
  have h := Graph.Zd.walkOp_eq f x
  rw [Graph.walkOp, walkOp_eq_sum_dir] at h
  rw [h, ← Finset.mul_sum]
  push_cast
  ring

/-- The walk started at `x` is at `z` at time `k` and in `B \ {z}` at the earlier times. -/
def firstHitEvent (B : Set (Site 2)) (z x : Site 2) (k : ℕ) : Set (ℕ → Dir 2) :=
  {ω | walkPos x ω k = z ∧ ∀ s < k, walkPos x ω s ∈ B ∧ walkPos x ω s ≠ z}

theorem measurableSet_firstHitEvent (B : Set (Site 2)) (z x : Site 2) (k : ℕ) :
    MeasurableSet (firstHitEvent B z x k) :=
  measurableSet_setOf.2 <| (measurable_walkPos_pred x (· = z) k).and <|
    Measurable.forall fun s => measurable_walkPos_pred x (fun y => s < k → y ∈ B ∧ y ≠ z) s

/-- The first-passage kernel of the network library is the probability of `firstHitEvent`. -/
theorem prob_firstHitEvent (B : Set (Site 2)) (z : Site 2) (k : ℕ) (x : Site 2) :
    prob (firstHitEvent B z x k) = Network.firstHit (lattice 2) B z k x := by
  induction k generalizing x with
  | zero =>
    rw [Network.firstHit_zero]
    by_cases hx : x = z
    · have h : firstHitEvent B z x 0 = Set.univ := by
        ext ω
        simp [firstHitEvent, walkPos_at_zero, hx]
      rw [h, prob_univ, if_pos hx]
    · have h : firstHitEvent B z x 0 = ∅ := by
        ext ω
        simp [firstHitEvent, walkPos_at_zero, hx]
      rw [h, prob_empty, if_neg hx]
  | succ k ih =>
    rw [Network.firstHit_succ]
    by_cases hxz : x = z
    · have h : firstHitEvent B z x (k + 1) = ∅ := by
        ext ω
        refine ⟨fun hω => absurd hω ?_, fun hω => absurd hω (Set.notMem_empty ω)⟩
        simp only [firstHitEvent, Set.mem_setOf_eq]
        rintro ⟨-, h⟩
        exact (h 0 (Nat.succ_pos k)).2 (by rw [walkPos_at_zero, hxz])
      rw [h, prob_empty, if_pos hxz]
    rw [if_neg hxz]
    by_cases hxB : x ∈ B
    · rw [if_pos hxB]
      have h : firstHitEvent B z x (k + 1) =
          {ω | shiftBy 1 ω ∈ firstHitEvent B z (x + dirVec (ω 0)) k} := by
        ext ω
        simp only [firstHitEvent, Set.mem_setOf_eq, walkPos_succ_eq_shiftBy]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun s hs => ?_⟩
          have := h2 (s + 1) (by omega)
          rwa [walkPos_succ_eq_shiftBy] at this
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun s hs => ?_⟩
          rcases s with _ | s
          · rw [walkPos_at_zero]
            exact ⟨hxB, hxz⟩
          · rw [walkPos_succ_eq_shiftBy]
            exact h2 s (by omega)
      rw [h, prob_firstStep (fun a => firstHitEvent B z (x + dirVec a) k)
        fun a => measurableSet_firstHitEvent B z _ k]
      simp_rw [ih]
      exact sum_quarter_eq_graphWalkOp (fun y => Network.firstHit (lattice 2) B z k y) x
    · rw [if_neg hxB]
      have h : firstHitEvent B z x (k + 1) = ∅ := by
        ext ω
        refine ⟨fun hω => absurd hω ?_, fun hω => absurd hω (Set.notMem_empty ω)⟩
        simp only [firstHitEvent, Set.mem_setOf_eq]
        rintro ⟨-, h⟩
        have := (h 0 (Nat.succ_pos k)).1
        rw [walkPos_at_zero] at this
        exact hxB this
      rw [h, prob_empty]

/-- The walk started at `z` returns to `z` at a positive time and stays in `B` in between. -/
def returnEvent (B : Set (Site 2)) (z : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, 1 ≤ t ∧ walkPos z ω t = z ∧
    ∀ s, 1 ≤ s → s < t → walkPos z ω s ∈ B ∧ walkPos z ω s ≠ z}

theorem returnEvent_mono {B B' : Set (Site 2)} (h : B ⊆ B') (z : Site 2) :
    returnEvent B z ⊆ returnEvent B' z :=
  fun _ ⟨t, ht, hz, hs⟩ => ⟨t, ht, hz, fun s h₁ h₂ => ⟨h (hs s h₁ h₂).1, (hs s h₁ h₂).2⟩⟩

/-- **The renewal bound.** For a finite `B ∋ z`, the walk started at `z` returns to `z` before
it leaves `B` with probability at most `1 - 1 / G_B(z, z)`, where `G_B(z, z)` is the expected
number of visits to `z` before the walk leaves `B` (four times the killed Green function of the
library), and `G_B(z, z) > 0`. -/
theorem prob_returnEvent_le (B : Finset (Site 2)) {z : Site 2} (hz : z ∈ B) :
    0 < 4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) z z ∧
      prob (returnEvent B z) ≤
        1 - 1 / (4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) z z) := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) B
  have hG := Graph.Zd.latticeConnected 2
  have hsub : returnEvent B z ⊆
      ⋃ k, {ω | shiftBy 1 ω ∈ firstHitEvent (B : Set (Site 2)) z (z + dirVec (ω 0)) k} := by
    rintro ω ⟨t, ht, hzt, hs⟩
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [Set.mem_setOf_eq, firstHitEvent]
    refine ⟨by rw [← walkPos_succ_eq_shiftBy]; exact hzt, fun s hs' => ?_⟩
    rw [← walkPos_succ_eq_shiftBy]
    exact hs (s + 1) (by omega) (by omega)
  have hpiece : ∀ k, prob {ω | shiftBy 1 ω ∈ firstHitEvent (B : Set (Site 2)) z
      (z + dirVec (ω 0)) k} = Network.firstReturn (lattice 2) (B : Set (Site 2)) z k := by
    intro k
    rw [prob_firstStep (fun a => firstHitEvent (B : Set (Site 2)) z (z + dirVec a) k)
      fun a => measurableSet_firstHitEvent _ z _ k]
    simp_rw [prob_firstHitEvent]
    rw [Network.firstReturn]
    exact sum_quarter_eq_graphWalkOp _ z
  have hsum := Network.summable_firstReturn hG B hz hq
  have hnn : ∀ k, 0 ≤ Network.firstReturn (lattice 2) (B : Set (Site 2)) z k :=
    fun k => Network.firstReturn_nonneg _ z k
  have hle : pathLaw 2 (returnEvent B z) ≤
      ENNReal.ofReal (Network.returnProb (lattice 2) B z) := by
    calc pathLaw 2 (returnEvent B z)
        ≤ pathLaw 2 (⋃ k, {ω | shiftBy 1 ω ∈ firstHitEvent (B : Set (Site 2)) z
            (z + dirVec (ω 0)) k}) := measure_mono hsub
      _ ≤ ∑' k, pathLaw 2 {ω | shiftBy 1 ω ∈ firstHitEvent (B : Set (Site 2)) z
            (z + dirVec (ω 0)) k} := measure_iUnion_le _
      _ = ∑' k, ENNReal.ofReal (Network.firstReturn (lattice 2) (B : Set (Site 2)) z k) := by
          refine tsum_congr fun k => ?_
          rw [← hpiece k, prob, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ = ENNReal.ofReal (Network.returnProb (lattice 2) B z) := by
          rw [Network.returnProb, ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  have hret : 0 ≤ Network.returnProb (lattice 2) B z := tsum_nonneg hnn
  have hprob : prob (returnEvent B z) ≤ Network.returnProb (lattice 2) B z :=
    ENNReal.toReal_le_of_le_ofReal hret hle
  have hdeg : ((lattice 2).degree z : ℝ) = 4 := by
    rw [Graph.Zd.degree_eq]
    norm_num
  have h1 := Network.one_sub_returnProb hG B hz hq
  have h2 := Network.visitCount_eq_degree_mul_effRes hG B hz hq
  have h3 := Network.killedGreenReal_eq_tsum hG B hq z z
  have hR := Network.effRes_pos hG B hz hq
  have hV : ((lattice 2).degree z : ℝ) * Network.effRes (lattice 2) B z =
      4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) z z := by
    rw [← h2, h3, Network.visitCount, hdeg]
    ring
  have hpos : 0 < 4 * Graph.killedGreenReal (lattice 2) (B : Set (Site 2)) z z := by
    rw [← hV, hdeg]
    exact mul_pos (by norm_num) hR
  rw [hV] at h1
  exact ⟨hpos, by linarith⟩

/-! ### Exhausting the half-plane -/

private theorem walkPos_succ (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos x ω (t + 1) = walkPos x ω t + dirVec (ω t) := by
  simp only [walkPos, Finset.sum_range_succ, add_assoc]

private theorem abs_dirVec_one_le (a : Dir 2) : |dirVec a 1| ≤ 1 := by
  rcases a with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp [dirVec]

private theorem euclidNorm_walkPos_sub_le (z : Site 2) (ω : ℕ → Dir 2) (t : ℕ) :
    euclidNorm (walkPos z ω t - z) ≤ t := by
  have h : ∀ t, walkPos z ω t - z = walkPos 0 ω t := fun t => by simp [walkPos]
  rw [h]
  induction t with
  | zero => simp [walkPos]
  | succ t ih =>
    have := euclidNorm_walkPos_succ_le 0 ω t
    push_cast
    linarith

private theorem mul_pos_of_step {a b c : ℤ} (hac : 0 < a * c) (hb : b ≠ 0) (hab : |b - a| ≤ 1) :
    0 < b * c := by
  rcases abs_le.1 hab with ⟨h1, h2⟩
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have ha : a < 0 := by
      by_contra h
      have := not_lt.1 h
      nlinarith
    have : b < 0 := by omega
    nlinarith
  · simp [hc] at hac
  · have ha : 0 < a := by
      by_contra h
      have := not_lt.1 h
      nlinarith
    have : 0 < b := by omega
    positivity

/-- Before its first positive-time visit to the axis, the walk stays on the side of `z`. -/
private theorem side_of_avoid {z : Site 2} {ω : ℕ → Dir 2} {t : ℕ} (hz : z 1 ≠ 0)
    (hs : ∀ s, 1 ≤ s → s < t → walkPos z ω s ∉ ({z} ∪ axisSet Set.univ)) :
    ∀ s < t, 0 < walkPos z ω s 1 * z 1 := by
  intro s
  induction s with
  | zero =>
    intro _
    rw [walkPos_at_zero]
    exact mul_self_pos.2 hz
  | succ s ih =>
    intro hst
    have hprev := ih (by omega)
    have hnot := hs (s + 1) (by omega) hst
    have hne : walkPos z ω (s + 1) 1 ≠ 0 := fun h0 => hnot (Or.inr ⟨h0, Set.mem_univ _⟩)
    refine mul_pos_of_step hprev hne ?_
    rw [walkPos_succ]
    simpa using abs_dirVec_one_le (ω s)

/-- Off the axis, the return probability is at most `1 - 1 / (a(z - z̄) + 1)`. -/
theorem prob_entersAt_le_of_ne {z : Site 2} (hz : z 1 ≠ 0) :
    0 < potentialKernel (z - axisRefl z) + 1 ∧
      prob (entersAt ({z} ∪ axisSet Set.univ) z z) ≤
        1 - 1 / (potentialKernel (z - axisRefl z) + 1) := by
  obtain ⟨R₀, hR₀, hG⟩ := four_mul_killedGreenReal_halfDisk_le
  have hmono : Monotone fun k : ℕ => returnEvent (halfDisk z (R₀ + k)) z := by
    intro j k hjk
    have hjk' : R₀ + (j : ℝ) ≤ R₀ + k := by
      have : (j : ℝ) ≤ k := Nat.cast_le.2 hjk
      linarith
    exact returnEvent_mono (Finset.coe_subset.2 (halfDisk_mono z hjk')) z
  have hsub : entersAt ({z} ∪ axisSet Set.univ) z z ⊆
      ⋃ k : ℕ, returnEvent (halfDisk z (R₀ + k)) z := by
    rintro ω ⟨t, ht, hzt, hs⟩
    refine Set.mem_iUnion.2 ⟨t, t, ht, hzt, fun s h₁ h₂ => ⟨?_, ?_⟩⟩
    · rw [Finset.mem_coe, mem_halfDisk]
      refine ⟨side_of_avoid hz hs s h₂, ?_⟩
      have := euclidNorm_walkPos_sub_le z ω s
      have : (s : ℝ) < t := by exact_mod_cast h₂
      linarith
    · exact fun h => hs s h₁ h₂ (Or.inl h)
  have hbound : ∀ k : ℕ, 0 < 4 * Graph.killedGreenReal (lattice 2)
      (halfDisk z (R₀ + k) : Set (Site 2)) z z ∧
      prob (returnEvent (halfDisk z (R₀ + k)) z) ≤
        1 - 1 / (potentialKernel (z - axisRefl z) + 1) := by
    intro k
    have hzB : z ∈ halfDisk z (R₀ + k) :=
      mem_halfDisk.2 ⟨mul_self_pos.2 hz, by simp; positivity⟩
    obtain ⟨hpos, hle⟩ := prob_returnEvent_le (halfDisk z (R₀ + k)) hzB
    have hg := hG z hz (R₀ + k) (by simp)
    refine ⟨hpos, hle.trans ?_⟩
    have := one_div_le_one_div_of_le hpos hg
    linarith
  have hpos : 0 < potentialKernel (z - axisRefl z) + 1 :=
    (hbound 0).1.trans_le (hG z hz (R₀ + ((0 : ℕ) : ℝ)) (by simp))
  have hnn : 0 ≤ 1 - 1 / (potentialKernel (z - axisRefl z) + 1) :=
    (show (0 : ℝ) ≤ prob (returnEvent (halfDisk z (R₀ + ((0 : ℕ) : ℝ))) z) from
      ENNReal.toReal_nonneg).trans (hbound 0).2
  refine ⟨hpos, ENNReal.toReal_le_of_le_ofReal hnn ?_⟩
  calc pathLaw 2 (entersAt ({z} ∪ axisSet Set.univ) z z)
      ≤ pathLaw 2 (⋃ k : ℕ, returnEvent (halfDisk z (R₀ + k)) z) := measure_mono hsub
    _ = ⨆ k : ℕ, pathLaw 2 (returnEvent (halfDisk z (R₀ + k)) z) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal (1 - 1 / (potentialKernel (z - axisRefl z) + 1)) := iSup_le fun k => by
        rw [← ENNReal.ofReal_toReal (measure_ne_top (pathLaw 2) _)]
        exact ENNReal.ofReal_le_ofReal (hbound k).2

/-- On the axis, a first step to the right reaches the axis away from `z`. -/
theorem prob_entersAt_le_of_eq_zero {z : Site 2} (hz : z 1 = 0) :
    prob (entersAt ({z} ∪ axisSet Set.univ) z z) ≤ 3 / 4 := by
  have hsub : entersAt ({z} ∪ axisSet Set.univ) z z ⊆ {ω | ω 0 = ((0 : Fin 2), true)}ᶜ := by
    rintro ω ⟨t, ht, hzt, hs⟩ hω0
    have hω0' : ω 0 = ((0 : Fin 2), true) := hω0
    have h1 : walkPos z ω 1 = z + dirVec ((0 : Fin 2), true) := by
      rw [walkPos_succ, walkPos_at_zero, hω0']
    rcases Nat.lt_or_ge 1 t with h | h
    · refine hs 1 le_rfl h (Or.inr ⟨?_, Set.mem_univ _⟩)
      rw [h1]
      simp [dirVec, hz]
    · have ht1 : t = 1 := by omega
      subst ht1
      have := congrFun (h1.symm.trans hzt) 0
      simp [dirVec] at this
  have hm : MeasurableSet {ω : ℕ → Dir 2 | ω 0 = ((0 : Fin 2), true)} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  have hle := measure_mono (μ := pathLaw 2) hsub
  rw [prob_compl_eq_one_sub hm, pathLaw_firstStep] at hle
  have hne : (1 : ENNReal) - 4⁻¹ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hval : ((1 : ENNReal) - 4⁻¹).toReal = 3 / 4 := by
    rw [ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.2 (by norm_num)) ENNReal.one_ne_top]
    norm_num
  exact (ENNReal.toReal_mono hne hle).trans_eq hval

/-! ### Lemma 11 (b) for the points of height at most `n` -/

private theorem one_le_abs_intCast {m : ℤ} (hm : m ≠ 0) : (1 : ℝ) ≤ |(m : ℝ)| := by
  have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
  rw [← Int.cast_abs]
  exact_mod_cast this

private theorem sub_axisRefl_eq (z : Site 2) : z - axisRefl z = ![0, 2 * z 1] := by
  ext i
  fin_cases i
  · simp [axisRefl]
  · simp [axisRefl]
    ring

private theorem euclidNorm_vert (m : ℤ) : euclidNorm (![0, m] : Site 2) = |(m : ℝ)| := by
  simp [euclidNorm, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

/-- The potential kernel at `z - z̄ = 2i Im z` grows like `log |Im z|`. -/
theorem exists_potentialKernel_sub_axisRefl_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ z : Site 2, z 1 ≠ 0 →
    potentialKernel (z - axisRefl z) + 1 ≤ A + Real.log |((z 1 : ℤ) : ℝ)| := by
  obtain ⟨κ, C, R₁, hR₁, hC⟩ := exists_abs_potentialKernel_sub_log_le
  set H : ℕ := ⌈R₁⌉₊ with hH
  set M : ℝ := ∑ j ∈ Finset.Icc (-(H : ℤ)) H, |potentialKernel ![0, 2 * j]| with hMdef
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨M + |κ| + |C| + 2, by positivity, fun z hz => ?_⟩
  rw [sub_axisRefl_eq]
  have hh := one_le_abs_intCast hz
  have hlog0 : 0 ≤ Real.log |((z 1 : ℤ) : ℝ)| := Real.log_nonneg hh
  by_cases hbig : R₁ ≤ 2 * |((z 1 : ℤ) : ℝ)|
  · have hn : euclidNorm (![0, 2 * z 1] : Site 2) = 2 * |((z 1 : ℤ) : ℝ)| := by
      rw [euclidNorm_vert]
      push_cast
      rw [abs_mul]
      norm_num
    have h := abs_le.1 (hC ![0, 2 * z 1] (by rw [hn]; exact hbig))
    rw [hn] at h
    have hp : (2 * |((z 1 : ℤ) : ℝ)|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hp0 : 0 ≤ (2 * |((z 1 : ℤ) : ℝ)|) ^ (-2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hCp : C * (2 * |((z 1 : ℤ) : ℝ)|) ^ (-2 : ℝ) ≤ |C| :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) hp0).trans
        (mul_le_of_le_one_right (abs_nonneg C) hp)
    have hlog2 : Real.log (2 * |((z 1 : ℤ) : ℝ)|) =
        Real.log 2 + Real.log |((z 1 : ℤ) : ℝ)| :=
      Real.log_mul (by norm_num) (by positivity)
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      norm_num at this
      linarith
    have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hpi : 2 / Real.pi ≤ 1 := by
      rw [div_le_one Real.pi_pos]
      linarith [Real.pi_gt_three]
    have h2pi : 0 ≤ 2 / Real.pi := by positivity
    have hκ := le_abs_self κ
    rw [hlog2] at h
    have hmain : 2 / Real.pi * (Real.log 2 + Real.log |((z 1 : ℤ) : ℝ)|) ≤
        1 + Real.log |((z 1 : ℤ) : ℝ)| := by
      nlinarith
    linarith [h.2]
  · have h1 : |((z 1 : ℤ) : ℝ)| < (H : ℝ) := by
      have := Nat.le_ceil R₁
      linarith [not_le.1 hbig]
    have h2 : |z 1| < (H : ℤ) := by
      rw [← Int.cast_abs] at h1
      exact_mod_cast h1
    have hzH : z 1 ∈ Finset.Icc (-(H : ℤ)) H := by
      rw [Finset.mem_Icc]
      exact ⟨by linarith [neg_abs_le (z 1)], by linarith [le_abs_self (z 1)]⟩
    have := Finset.single_le_sum (f := fun j : ℤ => |potentialKernel ![0, 2 * j]|)
      (fun _ _ => abs_nonneg _) hzH
    linarith [le_abs_self (potentialKernel ![0, 2 * z 1]), abs_nonneg κ, abs_nonneg C]

/-- **Lawler and Limic (2004), Lemma 11 (b), for the points of height at most `n`.** There are `c > 0` and `N` such that,
for `n ≥ N` and every `z` with `|Im z| ≤ n`, the walk started at `z` makes its first
positive-time visit to `{z} ∪ ℤ` at `z` with probability at most `1 - c / log n`. -/
theorem return_before_axis : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ z : Site 2, |((z 1 : ℤ) : ℝ)| ≤ n →
    prob (entersAt ({z} ∪ axisSet Set.univ) z z) ≤ 1 - c / Real.log n := by
  obtain ⟨A, hA0, hA⟩ := exists_potentialKernel_sub_axisRefl_le
  refine ⟨1 / (A + 4), div_pos one_pos (by linarith), 3, fun n hn z hz => ?_⟩
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have hc : 1 / (A + 4) / Real.log n = 1 / ((A + 4) * Real.log n) := by rw [div_div]
  have hpos : 0 < (A + 4) * Real.log n := mul_pos (by linarith) (by linarith)
  have hAl : (A + 4) * 1 ≤ (A + 4) * Real.log n :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  rw [hc]
  by_cases h0 : z 1 = 0
  · have h := prob_entersAt_le_of_eq_zero h0
    have : 1 / ((A + 4) * Real.log n) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  · obtain ⟨hpos', h⟩ := prob_entersAt_le_of_ne h0
    have hA' := hA z h0
    have hzlog : Real.log |((z 1 : ℤ) : ℝ)| ≤ Real.log n :=
      Real.log_le_log (by linarith [one_le_abs_intCast h0]) hz
    have hAA : A * 1 ≤ A * Real.log n := mul_le_mul_of_nonneg_left hlog hA0
    have : 1 / ((A + 4) * Real.log n) ≤ 1 / (potentialKernel (z - axisRefl z) + 1) :=
      one_div_le_one_div_of_le hpos' (by nlinarith)
    linarith

end FiniteAvalanches.Walk.Beurling
