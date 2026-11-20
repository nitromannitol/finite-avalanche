import FiniteAvalanches.Walk.Beurling.DiskGreen

/-!
# A uniform lower bound for the Green function of a disk

For every `b < 1` there are `c > 0` and `N` such that `G_n(z, w) ≥ c` whenever `n ≥ N` and
`z, w ∈ C_{bn}`, where `G_n` is the Green function (expected number of visits) of the simple
random walk on `ℤ²` killed on leaving the disk `C_n`; see
G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*,
Electron. J. Probab. 9 (2004), Lemma 3, estimate (11).

## Main statements

* `green_lower`: the estimate (11).

## Proof

All comparisons are made with the minimum principle for superharmonic functions on a finite
set, whose boundary values are only needed at the lattice neighbours of the set.

* For `z, w ∈ C_{n/4}`, the function `y ↦ G_n(y, w) - (α - a(y - w))`, with `a` the potential
  kernel and `α` a lower bound for `a` on `{|y - w| ≥ 3n/4}`, is harmonic on `C_n` and nonnegative
  off `C_n`. The asymptotics `a(x) = (2/π) log |x| + κ + O(|x|⁻²)` give `G_n(z, w) ≥ c₀`.
* For `|z| < bn`, the function `y ↦ G_n(y, w)` is superharmonic on `C_n` and at least `m` on
  `C_{n/4}`, so it dominates `m (α - a(y)) / (α - β)` on `C_n \ C_{n/4}`, where `α` and `β` bound
  `a` from below outside `C_n` and near the inner circle. This is the statement that the walk
  started in `C_{bn}` reaches `C_{n/4}` before leaving `C_n` with probability at least
  `q_b = log(1/b) / (2 log 8)`.
* Applying the second step twice, once in each variable through the symmetry of `G_n`, gives
  `G_n(z, w) ≥ q_b² c₀`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb

private theorem mem_diskFinset_iff' {r : ℝ} {y : Site 2} :
    y ∈ diskFinset r ↔ euclidNorm y < r := by
  rw [diskFinset, Finset.mem_filter, mem_ballFinset_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

private theorem euclidNorm_add_le' (y y' : Site 2) :
    euclidNorm (y + y') ≤ euclidNorm y + euclidNorm y' := by
  have hnorm : ∀ y : Site 2,
      euclidNorm y = ‖(WithLp.toLp 2 fun i => ((y i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2))‖ :=
    fun y => by
      simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, euclidNorm]
  have hadd : (WithLp.toLp 2 fun i => (((y + y') i : ℤ) : ℝ) : EuclideanSpace ℝ (Fin 2)) =
      (WithLp.toLp 2 fun i => ((y i : ℤ) : ℝ)) + (WithLp.toLp 2 fun i => ((y' i : ℤ) : ℝ)) := by
    ext i
    simp
  rw [hnorm (y + y'), hnorm y, hnorm y', hadd]
  exact norm_add_le _ _

private theorem euclidNorm_neg' (y : Site 2) : euclidNorm (-y) = euclidNorm y := by
  simp [euclidNorm]

private theorem euclidNorm_unit' (i : Fin 2) : euclidNorm (unit i) = 1 := by
  have hsum : (∑ j : Fin 2, (((unit i) j : ℤ) : ℝ) ^ 2) = 1 := by
    classical
    rw [Finset.sum_eq_single i]
    · simp [unit]
    · intro j _ hji
      simp [unit, hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  unfold euclidNorm
  rw [hsum, Real.sqrt_one]

/-- Neighbouring sites have Euclidean norms within one of each other. -/
private theorem euclidNorm_le_of_nbr {x y : Site 2} {i : Fin 2}
    (h : y = x + unit i ∨ y = x - unit i) :
    euclidNorm x ≤ euclidNorm y + 1 := by
  rcases h with rfl | rfl
  · have h := euclidNorm_add_le' (x + unit i) (-unit i)
    rwa [add_neg_cancel_right, euclidNorm_neg', euclidNorm_unit'] at h
  · have h := euclidNorm_add_le' (x - unit i) (unit i)
    rwa [sub_add_cancel, euclidNorm_unit'] at h

/-- **Minimum principle.** A function superharmonic on a finite set `D` and nonnegative at the
lattice neighbours of `D` outside `D` is nonnegative on `D`. -/
private theorem nonneg_of_nbrSum_le (D : Finset (Site 2)) (f : Site 2 → ℝ)
    (hsup : ∀ x ∈ D, nbrSum f x ≤ 4 * f x)
    (hbd : ∀ x ∈ D, ∀ i : Fin 2, ∀ y, (y = x + unit i ∨ y = x - unit i) → y ∉ D → 0 ≤ f y) :
    ∀ x ∈ D, 0 ≤ f x := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁D, hx₁⟩ := hcon
  obtain ⟨x₀, hx₀D, hmin⟩ := D.exists_min_image f ⟨x₁, hx₁D⟩
  have hneg : f x₀ < 0 := (hmin x₁ hx₁D).trans_lt hx₁
  obtain ⟨y, hyM, hmax⟩ := (D.filter fun x => f x = f x₀).exists_max_image (fun x => x 0)
    ⟨x₀, Finset.mem_filter.2 ⟨hx₀D, rfl⟩⟩
  obtain ⟨hyD, hy⟩ := Finset.mem_filter.1 hyM
  have hge : ∀ i : Fin 2, ∀ z, (z = y + unit i ∨ z = y - unit i) → f x₀ ≤ f z := by
    intro i z hz
    by_cases hzD : z ∈ D
    · exact hmin z hzD
    · exact hneg.le.trans (hbd y hyD i z hz hzD)
  have h1 := hge 0 (y + unit 0) (Or.inl rfl)
  have h2 := hge 0 (y - unit 0) (Or.inr rfl)
  have h3 := hge 1 (y + unit 1) (Or.inl rfl)
  have h4 := hge 1 (y - unit 1) (Or.inr rfl)
  have hs := hsup y hyD
  rw [nbrSum, Fin.sum_univ_two] at hs
  have heq : f (y + unit 0) = f x₀ := by linarith
  have hin : y + unit 0 ∈ D := by
    by_contra h
    have := hbd y hyD 0 (y + unit 0) (Or.inl rfl) h
    linarith
  have := hmax (y + unit 0) (Finset.mem_filter.2 ⟨hin, heq⟩)
  simp [unit] at this

/-- `a(· - w)` has Laplacian `δ_w`. -/
private theorem nbrSum_potentialKernel_sub (w x : Site 2) :
    nbrSum (fun y => potentialKernel (y - w)) x =
      4 * potentialKernel (x - w) + if x = w then 4 else 0 := by
  have e : nbrSum (fun y => potentialKernel (y - w)) x = nbrSum potentialKernel (x - w) := by
    rw [nbrSum, nbrSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_sub_right_comm, sub_right_comm]
  have e4 : nbrSum potentialKernel (x - w) = 4 * walkOp potentialKernel (x - w) := by
    rw [walkOp]
    push_cast
    ring
  have h := walkOp_potentialKernel_sub (x - w)
  rw [e, e4]
  by_cases hxw : x = w
  · rw [if_pos (sub_eq_zero.2 hxw)] at h
    rw [if_pos hxw]
    linarith
  · rw [if_neg (sub_ne_zero.2 hxw)] at h
    rw [if_neg hxw]
    linarith

private theorem green_symm (r : ℝ) (x w : Site 2) : green r x w = green r w x := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) (diskFinset r)
  rw [green, green, Network.killedGreenReal_symm (Graph.Zd.latticeConnected 2) _ hq x w]

private theorem green_eq_zero_of_not_mem {r : ℝ} {x : Site 2} (hx : x ∉ diskFinset r)
    (w : Site 2) : green r x w = 0 := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) (diskFinset r)
  rw [green_symm, green,
    Network.killedGreenReal_eq_zero_of_not_mem (Graph.Zd.latticeConnected 2) _ hq hx w, mul_zero]

/-- `y ↦ G_r(y, w)` has Laplacian `-4 δ_w` on `C_r` (expected-visits normalization). -/
private theorem nbrSum_green {r : ℝ} {w x : Site 2} (hw : w ∈ diskFinset r)
    (hx : x ∈ diskFinset r) :
    nbrSum (fun y => green r y w) x = 4 * green r x w - if x = w then 4 else 0 := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) (diskFinset r)
  have hG := Graph.Zd.latticeConnected 2
  have hsym : (fun y => green r y w) = fun y =>
      4 * Graph.killedGreenReal (lattice 2) (diskFinset r : Set (Site 2)) w y :=
    funext fun y => by rw [green_symm, green]
  have hl := Network.laplacian_killedGreenReal hG (diskFinset r) hw hq (v := x)
    (by exact_mod_cast hx)
  rw [laplacian_eq_nbrSum_sub (d := 2) (by norm_num)] at hl
  have hlin : nbrSum (fun y =>
      4 * Graph.killedGreenReal (lattice 2) (diskFinset r : Set (Site 2)) w y) x =
      4 * nbrSum (Graph.killedGreenReal (lattice 2) (diskFinset r : Set (Site 2)) w) x := by
    simp only [nbrSum, Fin.sum_univ_two]
    ring
  rw [hsym, hlin, green_symm, green]
  push_cast at hl
  split_ifs at hl ⊢ <;> linarith

/-- The planar potential kernel asymptotics in a uniform form: for every `ε > 0` and all large
`T`, `a ≤ (2/π) log T + κ + ε` on `C_T` and `a(x) ≥ (2/π) log |x| + κ - ε` for `|x| ≥ T`. -/
private theorem exists_potentialKernel_bounds : ∃ κ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, 1 ≤ T₀ ∧
    (∀ x : Site 2, ∀ T : ℝ, T₀ ≤ T → euclidNorm x < T →
      potentialKernel x ≤ 2 / Real.pi * Real.log T + κ + ε) ∧
    (∀ x : Site 2, T₀ ≤ euclidNorm x →
      2 / Real.pi * Real.log (euclidNorm x) + κ - ε ≤ potentialKernel x) := by
  obtain ⟨κ, C, R, hR, hC⟩ := exists_abs_potentialKernel_sub_log_le
  refine ⟨κ, fun ε hε => ?_⟩
  have hpi0 := Real.pi_ne_zero
  have hCε : 0 ≤ |C| / ε := div_nonneg (abs_nonneg C) hε.le
  set R₁ := R + |C| / ε with hR₁
  have hR₁1 : 1 ≤ R₁ := by linarith
  have hpi : 0 < 2 / Real.pi := by positivity
  have herr : ∀ x : Site 2, R₁ ≤ euclidNorm x →
      |potentialKernel x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤ ε := by
    intro x hx
    have hx1 : 1 ≤ euclidNorm x := hR₁1.trans hx
    have hx0 : 0 < euclidNorm x := by linarith
    have hCe : |C| ≤ ε * euclidNorm x := by
      have h : |C| / ε ≤ euclidNorm x := by linarith
      rwa [div_le_iff₀ hε, mul_comm] at h
    calc |potentialKernel x - (2 / Real.pi * Real.log (euclidNorm x) + κ)|
        ≤ C * euclidNorm x ^ (-2 : ℝ) := hC x (by linarith)
      _ ≤ |C| * euclidNorm x ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)
      _ ≤ ε := by
          rw [Real.rpow_neg hx0.le, Real.rpow_two, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hx0 2)]
          nlinarith [mul_le_mul_of_nonneg_left hx1 (mul_nonneg hε.le hx0.le)]
  set M := ∑ y ∈ ballFinset 2 R₁, |potentialKernel y| with hM
  have hsmall : ∀ x : Site 2, euclidNorm x < R₁ → potentialKernel x ≤ M := fun x hx =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun y => |potentialKernel y|)
      (fun _ _ => abs_nonneg _) (mem_ballFinset_iff.2 hx.le))
  refine ⟨max R₁ (Real.exp (Real.pi / 2 * |M - κ|)), hR₁1.trans (le_max_left _ _), ?_, ?_⟩
  · intro x T hT hxT
    rcases lt_or_ge (euclidNorm x) R₁ with hx | hx
    · have hexp : Real.exp (Real.pi / 2 * |M - κ|) ≤ T := (le_max_right _ _).trans hT
      have hlogT : Real.pi / 2 * |M - κ| ≤ Real.log T := by
        have h := Real.log_le_log (Real.exp_pos _) hexp
        rwa [Real.log_exp] at h
      have hMT : M - κ ≤ 2 / Real.pi * Real.log T :=
        calc M - κ ≤ |M - κ| := le_abs_self _
          _ = 2 / Real.pi * (Real.pi / 2 * |M - κ|) := by field_simp
          _ ≤ 2 / Real.pi * Real.log T := mul_le_mul_of_nonneg_left hlogT hpi.le
      linarith [hsmall x hx]
    · have h := herr x hx
      have hx0 : 0 < euclidNorm x := by linarith
      have hlog : 2 / Real.pi * Real.log (euclidNorm x) ≤ 2 / Real.pi * Real.log T :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hx0 hxT.le) hpi.le
      rw [abs_le] at h
      linarith [h.2]
  · intro x hx
    have h := herr x ((le_max_left _ _).trans hx)
    rw [abs_le] at h
    linarith [h.1]

/-- **The estimate (11) on `C_{n/4}`.** -/
private theorem green_lower_quarter : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ z w : Site 2, euclidNorm z < n / 4 → euclidNorm w < n / 4 → c ≤ green n z w := by
  obtain ⟨κ, hκ⟩ := exists_potentialKernel_bounds
  set L := Real.log (3 / 2) with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  have hpi := Real.pi_pos
  set ε := L / (2 * Real.pi) with hε
  have hε0 : 0 < ε := div_pos hL0 (by positivity)
  obtain ⟨T₀, hT₀, hup, hlow⟩ := hκ ε hε0
  have hc : 2 / Real.pi * L - 2 * ε = L / Real.pi := by
    rw [hε]
    ring
  refine ⟨2 / Real.pi * L - 2 * ε, by rw [hc]; exact div_pos hL0 hpi, ⌈2 * T₀⌉₊,
    fun n hn z w hz hw => ?_⟩
  have hnT : 2 * T₀ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  set T : ℝ := (n : ℝ) / 2 with hT
  have hT0 : T₀ ≤ T := by rw [hT]; linarith
  have hTpos : 0 < T := by linarith
  set α := 2 / Real.pi * Real.log (3 / 2 * T) + κ - ε with hα
  have hzB : z ∈ diskFinset (n : ℝ) := mem_diskFinset_iff'.2 (by linarith)
  have hwB : w ∈ diskFinset (n : ℝ) := mem_diskFinset_iff'.2 (by linarith)
  have key := nonneg_of_nbrSum_le (diskFinset (n : ℝ))
    (fun y => green n y w - (α - potentialKernel (y - w)))
    (fun x hx => by
      have hlin : nbrSum (fun y => green n y w - (α - potentialKernel (y - w))) x =
          nbrSum (fun y => green n y w) x - 4 * α +
            nbrSum (fun y => potentialKernel (y - w)) x := by
        simp only [nbrSum, Fin.sum_univ_two]
        ring
      rw [hlin, nbrSum_green hwB hx, nbrSum_potentialKernel_sub]
      split_ifs <;> linarith)
    (fun x _ i y _ hy => by
      rw [mem_diskFinset_iff', not_lt] at hy
      rw [green_eq_zero_of_not_mem (by rw [mem_diskFinset_iff', not_lt]; exact hy)]
      have hyw : 3 / 2 * T ≤ euclidNorm (y - w) := by
        have h := euclidNorm_add_le' (y - w) w
        rw [sub_add_cancel] at h
        rw [hT]
        linarith
      have h := hlow (y - w) (by linarith)
      have hlog : 2 / Real.pi * Real.log (3 / 2 * T) ≤
          2 / Real.pi * Real.log (euclidNorm (y - w)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hyw) (by positivity)
      linarith)
    z hzB
  have hzw : euclidNorm (z - w) < T := by
    have h := euclidNorm_add_le' z (-w)
    rw [euclidNorm_neg', ← sub_eq_add_neg] at h
    rw [hT]
    linarith
  have h := hup (z - w) T hT0 hzw
  have hlog : Real.log (3 / 2 * T) = L + Real.log T := Real.log_mul (by norm_num) hTpos.ne'
  have hkey : 0 ≤ green n z w - (α - potentialKernel (z - w)) := key
  rw [hα, hlog] at hkey
  linarith

/-- **Entrance into `C_{n/4}`.** If `y ↦ G_n(y, w)` is at least `m ≥ 0` on `C_{n/4}`, it is at
least `q m` on `C_{bn}`. -/
private theorem green_ge_mul_of_quarter (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z w : Site 2, euclidNorm z < b * n →
      euclidNorm w < n → ∀ m : ℝ, 0 ≤ m → (∀ y : Site 2, euclidNorm y < n / 4 → m ≤ green n y w) →
        q * m ≤ green n z w := by
  classical
  obtain ⟨κ, hκ⟩ := exists_potentialKernel_bounds
  set L := Real.log b⁻¹ with hL
  have hL0 : 0 < L := Real.log_pos ((one_lt_inv₀ hb0).2 hb1)
  have hpi := Real.pi_pos
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  set ε := L / (2 * Real.pi) with hε
  have hε0 : 0 < ε := div_pos hL0 (by positivity)
  obtain ⟨T₀, hT₀, hup, hlow⟩ := hκ ε hε0
  have hnum : 2 / Real.pi * L - 2 * ε = L / Real.pi := by
    rw [hε]
    ring
  have h2pi : 0 < 2 / Real.pi := by positivity
  have hden : 0 < 2 / Real.pi * Real.log 8 := mul_pos h2pi h8
  set q₀ := (2 / Real.pi * L - 2 * ε) / (2 / Real.pi * Real.log 8) with hq₀
  have hq₀0 : 0 < q₀ := by rw [hq₀, hnum]; exact div_pos (div_pos hL0 hpi) hden
  refine ⟨min q₀ 1, lt_min hq₀0 one_pos, min_le_right _ _, ⌈8 * T₀ / b⌉₊,
    fun n hn z w hz hw m hm hA => ?_⟩
  have hnN : 8 * T₀ / b ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hbn : 8 * T₀ ≤ b * n := by
    rw [div_le_iff₀ hb0] at hnN
    linarith
  have hn0' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn8 : 8 * T₀ ≤ (n : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hb1.le hn0']
  have hn0 : 0 < (n : ℝ) := by linarith
  by_cases hzA : euclidNorm z < n / 4
  · exact (mul_le_of_le_one_left hm (min_le_right _ _)).trans (hA z hzA)
  set B := diskFinset (n : ℝ)
  set D := B \ diskFinset ((n : ℝ) / 4) with hD
  have hwB : w ∈ B := mem_diskFinset_iff'.2 hw
  have hzD : z ∈ D := Finset.mem_sdiff.2 ⟨mem_diskFinset_iff'.2 (by nlinarith),
    fun h => hzA (mem_diskFinset_iff'.1 h)⟩
  set α := 2 / Real.pi * Real.log n + κ - ε with hα
  set β := 2 / Real.pi * Real.log (n / 8) + κ - ε with hβ
  have hαβ : α - β = 2 / Real.pi * Real.log 8 := by
    rw [hα, hβ, Real.log_div hn0.ne' (by norm_num)]
    ring
  have hαβ0 : 0 ≤ α - β := by rw [hαβ]; exact hden.le
  have key := nonneg_of_nbrSum_le D
    (fun y => (α - β) * green n y w - m * (α - potentialKernel y))
    (fun x hx => by
      obtain ⟨hxB, hxA⟩ := Finset.mem_sdiff.1 hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hxA (mem_diskFinset_iff'.2 (by rw [euclidNorm_zero]; linarith))
      have hlin : nbrSum (fun y => (α - β) * green n y w - m * (α - potentialKernel y)) x =
          (α - β) * nbrSum (fun y => green n y w) x - m * (4 * α -
            nbrSum (fun y => potentialKernel (y - 0)) x) := by
        simp only [nbrSum, Fin.sum_univ_two, sub_zero]
        ring
      rw [hlin, nbrSum_green hwB hxB, nbrSum_potentialKernel_sub, sub_zero, if_neg hx0]
      split_ifs <;> linarith)
    (fun x hx i y hxy hy => by
      obtain ⟨_, hxA⟩ := Finset.mem_sdiff.1 hx
      have hxn : (n : ℝ) / 4 ≤ euclidNorm x := not_lt.1 fun h => hxA (mem_diskFinset_iff'.2 h)
      have hyx := euclidNorm_le_of_nbr hxy
      by_cases hyB : y ∈ B
      · have hyA : y ∈ diskFinset ((n : ℝ) / 4) := by
          by_contra h
          exact hy (Finset.mem_sdiff.2 ⟨hyB, h⟩)
        have hgy := hA y (mem_diskFinset_iff'.1 hyA)
        have hy8 : (n : ℝ) / 8 ≤ euclidNorm y := by linarith
        have h := hlow y (by linarith)
        have hlog : 2 / Real.pi * Real.log (n / 8) ≤ 2 / Real.pi * Real.log (euclidNorm y) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hy8) (by positivity)
        have hay : α - potentialKernel y ≤ α - β := by rw [hβ]; linarith
        nlinarith [mul_le_mul_of_nonneg_left hay hm, mul_le_mul_of_nonneg_left hgy hαβ0]
      · have hyn : (n : ℝ) ≤ euclidNorm y := not_lt.1 fun h => hyB (mem_diskFinset_iff'.2 h)
        rw [green_eq_zero_of_not_mem hyB, mul_zero, zero_sub, neg_nonneg]
        have h := hlow y (by linarith)
        have hlog : 2 / Real.pi * Real.log n ≤ 2 / Real.pi * Real.log (euclidNorm y) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log hn0 hyn) (by positivity)
        have hle : α - potentialKernel y ≤ 0 := by rw [hα]; linarith
        exact mul_nonpos_iff.2 (Or.inl ⟨hm, hle⟩))
    z hzD
  have hkey : m * (α - potentialKernel z) ≤ (α - β) * green n z w := by
    have h := key
    beta_reduce at h
    linarith
  have hz' := hup z (b * n) (by linarith) hz
  rw [Real.log_mul hb0.ne' hn0.ne'] at hz'
  have hlogb : Real.log b = -L := by rw [hL, Real.log_inv]; ring
  rw [hlogb] at hz'
  have hαz : 2 / Real.pi * L - 2 * ε ≤ α - potentialKernel z := by rw [hα]; linarith
  have h1 : q₀ * m * (α - β) ≤ (α - β) * green n z w := by
    calc q₀ * m * (α - β)
        = (2 / Real.pi * L - 2 * ε) / (2 / Real.pi * Real.log 8) *
            (2 / Real.pi * Real.log 8) * m := by
          rw [hq₀, hαβ]
          ring
      _ = (2 / Real.pi * L - 2 * ε) * m := by rw [div_mul_cancel₀ _ hden.ne']
      _ ≤ (α - potentialKernel z) * m := mul_le_mul_of_nonneg_right hαz hm
      _ ≤ (α - β) * green n z w := by linarith
  have hαβpos : 0 < α - β := by rw [hαβ]; exact hden
  have h2 : q₀ * m ≤ green n z w := by
    rw [mul_comm (α - β)] at h1
    exact le_of_mul_le_mul_right h1 hαβpos
  exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hm).trans h2

/-- **Lawler and Limic (2004), Lemma 3, estimate (11)**: for every `0 < b < 1` there are `c > 0`
and `N` such that `G_n(z, w) ≥ c` for all `n ≥ N` and `z, w ∈ C_{bn}`. -/
theorem green_lower (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ,
    N ≤ n → ∀ z w : Site 2, euclidNorm z < b * n → euclidNorm w < b * n → c ≤ green n z w := by
  obtain ⟨c₀, hc₀, N₀, h₀⟩ := green_lower_quarter
  obtain ⟨q, hq0, -, N₁, h₁⟩ := green_ge_mul_of_quarter b hb0 hb1
  refine ⟨q * (q * c₀), mul_pos hq0 (mul_pos hq0 hc₀), max N₀ N₁, fun n hn z w hz hw => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hwn : euclidNorm w < n := hw.trans_le (by nlinarith)
  have hstep : ∀ y : Site 2, euclidNorm y < n / 4 → q * c₀ ≤ green n y w := by
    intro y hy
    rw [green_symm]
    exact h₁ n (le_of_max_le_right hn) w y hw (by linarith) c₀ hc₀.le
      fun y' hy' => h₀ n (le_of_max_le_left hn) y' y hy' hy
  exact h₁ n (le_of_max_le_right hn) z w hz hwn (q * c₀) (mul_pos hq0 hc₀).le hstep

end FiniteAvalanches.Walk.Beurling
