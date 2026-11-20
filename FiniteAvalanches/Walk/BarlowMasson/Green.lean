import FiniteAvalanches.Walk.BarlowMasson.Annulus

/-!
# Expected visits before leaving a finite set

For a finite set `D ⊂ ℤ²`, `visits D x v` is the expected number of visits to `v` by the simple
random walk started at `x` before it leaves `D`; it is `4` times the killed Green function of
the library. It is symmetric, vanishes off `D`, and satisfies
`visits D x v = (1/4) ∑ₐ visits D (x + eₐ) v + 1_{x = v}` on `D`.

The probability of reaching `A` before `B` from a site of `D`, when `D` is disjoint from
`A ∪ B` and every site outside `D` lies in `A ∪ B`, is the sum over the sites `y` of `D` of
`visits D x y` times the probability of stepping from `y` into `A \ B`
(`prob_reaches_eq_sum_visits`, the first-entrance decomposition).

## Main statements

* `visits_symm`, `visits_mean`, `visits_mono`.
* `visits_eq_potentialKernel`: `visits D x v = E^x[a(S_τ - v)] - a(x - v)`.
* `prob_reaches_eq_sum_visits`: the first-entrance decomposition, with `stepInto A B y` the
  probability of stepping from `y` into `A \ B`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling

/-- The expected number of visits to `v` by the walk from `x` before it leaves `D`. -/
def visits (D : Finset (Site 2)) (x v : Site 2) : ℝ :=
  4 * Graph.killedGreenReal (lattice 2) (D : Set (Site 2)) x v

theorem visits_symm (D : Finset (Site 2)) (x v : Site 2) : visits D x v = visits D v x := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) D
  rw [visits, visits, Network.killedGreenReal_symm (Graph.Zd.latticeConnected 2) _ hq x v]

theorem visits_nonneg (D : Finset (Site 2)) (x v : Site 2) : 0 ≤ visits D x v := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) D
  exact mul_nonneg (by norm_num)
    (Network.killedGreenReal_nonneg (Graph.Zd.latticeConnected 2) _ hq x v)

theorem visits_eq_zero_right {D : Finset (Site 2)} {v : Site 2} (hv : v ∉ D) (x : Site 2) :
    visits D x v = 0 := by
  obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) D
  rw [visits, Network.killedGreenReal_eq_zero_of_not_mem (Graph.Zd.latticeConnected 2) _ hq hv x,
    mul_zero]

theorem visits_eq_zero_left {D : Finset (Site 2)} {x : Site 2} (hx : x ∉ D) (v : Site 2) :
    visits D x v = 0 := by
  rw [visits_symm, visits_eq_zero_right hx]

theorem visits_mono {D D' : Finset (Site 2)} (h : D ⊆ D') (x v : Site 2) :
    visits D x v ≤ visits D' x v :=
  mul_le_mul_of_nonneg_left (killedGreenReal_mono h x v) (by norm_num)

/-- The expected visits are the mean of their neighbouring values, plus one at the target. -/
theorem visits_mean {D : Finset (Site 2)} {x : Site 2} (hx : x ∈ D) (v : Site 2) :
    visits D x v = (∑ a : Dir 2, visits D (x + dirVec a) v) / 4 + if x = v then 1 else 0 := by
  by_cases hv : v ∈ D
  · obtain ⟨q, hq⟩ := exists_not_mem_finset (by norm_num : 1 ≤ 2) D
    have hG := Graph.Zd.latticeConnected 2
    have hl := Network.laplacian_killedGreenReal hG D hv hq (v := x) (by exact_mod_cast hx)
    rw [laplacian_eq_nbrSum_sub (d := 2) (by norm_num), nbrSum_eq_sum_dir] at hl
    have hs : ∀ y, visits D y v = 4 * Graph.killedGreenReal (lattice 2) (D : Set (Site 2)) v y :=
      fun y => by rw [visits_symm, visits]
    simp only [hs]
    rw [← Finset.mul_sum]
    push_cast at hl
    by_cases hxv : x = v
    · rw [if_pos hxv]
      rw [if_pos hxv] at hl
      linarith
    · rw [if_neg hxv]
      rw [if_neg hxv] at hl
      linarith
  · have hxv : x ≠ v := fun h => hv (h ▸ hx)
    simp only [visits_eq_zero_right hv, Finset.sum_const_zero, zero_div, if_neg hxv, add_zero]

/-- **The expected visits through the potential kernel.** For `x, v ∈ D`,
`visits D x v = E^x[a(S_τ - v)] - a(x - v)`, where `τ` is the exit time of `D`. -/
theorem visits_eq_potentialKernel (D : Finset (Site 2)) {x v : Site 2} (hx : x ∈ D)
    (hv : v ∈ D) :
    visits D x v = ∫ ω, potentialKernel (walkPos x ω (exitIdx D x ω) - v) ∂pathLaw 2
      - potentialKernel (x - v) :=
  killedGreenReal_eq_potentialKernel D hx hv

/-- The number of neighbours of `y` in `A \ B`, divided by `4`. -/
def stepInto (A B : Set (Site 2)) (y : Site 2) : ℝ :=
  (∑ a : Dir 2, (A \ B).indicator (fun _ => (1 : ℝ)) (y + dirVec a)) / 4

theorem stepInto_nonneg (A B : Set (Site 2)) (y : Site 2) : 0 ≤ stepInto A B y :=
  div_nonneg (Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (by norm_num)

theorem stepInto_le_one (A B : Set (Site 2)) (y : Site 2) : stepInto A B y ≤ 1 := by
  rw [stepInto, div_le_one (by norm_num : (0 : ℝ) < 4)]
  calc ∑ a : Dir 2, (A \ B).indicator (fun _ => (1 : ℝ)) (y + dirVec a) ≤ ∑ _a : Dir 2, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => Set.indicator_le_self' (fun _ _ => zero_le_one) _
    _ = 4 := by simp

/-- **The first-entrance decomposition.** If `D` is disjoint from `A ∪ B` and every site outside
`D` lies in `A ∪ B`, then from a site `x` of `D` the probability of reaching `A` before `B` is
`∑_{y ∈ D} visits D x y · stepInto A B y`. -/
theorem prob_reaches_eq_sum_visits (D : Finset (Site 2)) (A B : Set (Site 2))
    (hDA : ∀ y ∈ D, y ∉ A) (hDB : ∀ y ∈ D, y ∉ B) (hout : ∀ y, y ∉ D → y ∈ A ∨ y ∈ B)
    {x : Site 2} (hx : x ∈ D) :
    prob (reaches A B x) = ∑ y ∈ D, visits D x y * stepInto A B y := by
  classical
  set n : Site 2 → ℝ := stepInto A B with hn
  set P : Site 2 → ℝ := fun y => if y ∈ D then prob (reaches A B y) else 0 with hP
  set S : Site 2 → ℝ := fun y => ∑ w ∈ D, visits D y w * n w with hS
  have hprob : ∀ w, prob (reaches A B w) = P w + (A \ B).indicator (fun _ => (1 : ℝ)) w := by
    intro w
    by_cases hw : w ∈ D
    · simp only [hP, if_pos hw]
      rw [Set.indicator_of_notMem (fun h => hDA w hw h.1), add_zero]
    · simp only [hP, if_neg hw, zero_add]
      by_cases hwB : w ∈ B
      · rw [reaches_eq_empty hwB, Set.indicator_of_notMem (fun h => h.2 hwB), prob,
          measure_empty, ENNReal.toReal_zero]
      · have hwA : w ∈ A := (hout w hw).resolve_right hwB
        rw [reaches_eq_univ hwA hwB, Set.indicator_of_mem (show w ∈ A \ B from ⟨hwA, hwB⟩),
          prob_univ]
  have hPmean : ∀ y ∈ D, P y = (∑ a : Dir 2, P (y + dirVec a)) / 4 + n y := by
    intro y hy
    have hstep := prob_reaches_step (hDA y hy) (hDB y hy)
    rw [Finset.sum_congr rfl (fun a _ => hprob (y + dirVec a)), Finset.sum_add_distrib] at hstep
    have hPy : P y = prob (reaches A B y) := by simp only [hP, if_pos hy]
    rw [hPy, hstep, hn, stepInto]
    ring
  have hSmean : ∀ y ∈ D, S y = (∑ a : Dir 2, S (y + dirVec a)) / 4 + n y := by
    intro y hy
    simp only [hS]
    have hv : ∀ w ∈ D, visits D y w * n w =
        (∑ a : Dir 2, visits D (y + dirVec a) w * n w) / 4 + (if y = w then n w else 0) := by
      intro w _
      rw [visits_mean hy w, ← Finset.sum_mul]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hv, Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_comm, Finset.sum_ite_eq D y n, if_pos hy]
  have hzero : ∀ y ∈ D, P y - S y ≤ 0 ∧ S y - P y ≤ 0 := by
    have h1 := le_of_mean D (fun y => P y - S y) 0
      (fun y hy => by
        rw [hPmean y hy, hSmean y hy, Finset.sum_sub_distrib]
        ring)
      (fun y _ a ha => by
        simp only [hP, hS, if_neg ha, visits_eq_zero_left ha, zero_mul, Finset.sum_const_zero,
          sub_zero, le_refl])
    have h2 := le_of_mean D (fun y => S y - P y) 0
      (fun y hy => by
        rw [hPmean y hy, hSmean y hy, Finset.sum_sub_distrib]
        ring)
      (fun y _ a ha => by
        simp only [hP, hS, if_neg ha, visits_eq_zero_left ha, zero_mul, Finset.sum_const_zero,
          sub_zero, le_refl])
    exact fun y hy => ⟨h1 y hy, h2 y hy⟩
  have hx' := hzero x hx
  have hPx : P x = prob (reaches A B x) := by simp only [hP, if_pos hx]
  have : prob (reaches A B x) = S x := by linarith [hx'.1, hx'.2]
  rw [this]

end FiniteAvalanches.Walk.BarlowMasson
