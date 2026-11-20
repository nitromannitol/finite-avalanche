import FiniteAvalanches.Walk.BarlowMasson.SamplerPath
import FiniteAvalanches.Walk.BarlowMasson.Crossing
import FiniteAvalanches.Wilson.Lattice.WiredLawReduction
import FiniteAvalanches.Wilson.Lattice.BeurlingGeometry
import FiniteAvalanches.Trees.Lattice.InfiniteLaw

/-!
# The tree path between adjacent sites

Barlow and Masson (2011), Lemma 2.6, upper bound: the path between adjacent sites in the uniform
spanning tree of `ℤ²` leaves the closed Euclidean ball of radius `k` about one of them with
probability at most `C k ^ (-1/3)`.

## Proof

In the wired box of size `N`, sample the tree by the lattice Wilson sampler rooted at the exterior
of the box, from `x`, then from its neighbour `y`, then from the other sites of the ball
(`finiteLaw_cylinder_eq_sampler`). If the tree path leaves the ball, then (`joinedIn_of_samplerRun`)
either (a) the branch of `x` returns to the disk of radius `r` after its first site at distance
`k`, which has probability at most `C r / k` (`reentry_le`), or (b) the walk from `y` reaches
distance `r` before visiting the branch of `x`, which has probability at most `C r ^ (-1/2)` by the
Beurling estimate (`beurling_crossing`), the branch being a path from a neighbour of `y` to the
exterior of the box. The event is a finite union of edge cylinders, so its probability under the
limit law is the limit of its probabilities in the boxes. Take `r` of order `k ^ (2/3)`.

## Main statements

* `ust_joinedIn_compl_le`: the bound `C r / k + C r ^ (-1/2)` for natural `k` and `r`.
* `adjacent_ust_path_euclidean_tail_le`: the bound `C k ^ (-1/3)`.
-/

set_option autoImplicit false

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory ProbabilityTheory Filter FiniteAvalanches.Sandpile
open FiniteAvalanches.Walk.Beurling
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Trees.Lattice.BarlowMasson
open FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal

noncomputable section

/-- The law of one row of the sampler. -/
theorem wilsonRows_row_le (i : ℕ) (A : Set WalkDriver) :
    wilsonRows {ξ | ξ i ∈ A} ≤ walkLaw A := by
  calc wilsonRows {ξ | ξ i ∈ A}
      ≤ wilsonRows ((fun ξ : ℕ → WalkDriver => ξ i) ⁻¹' toMeasurable walkLaw A) :=
        measure_mono fun ξ hξ => subset_toMeasurable walkLaw A hξ
    _ = walkLaw (toMeasurable walkLaw A) :=
        (measurePreserving_eval_infinitePi (fun _ : ℕ => walkLaw) i).measure_preimage
          (measurableSet_toMeasurable _ _).nullMeasurableSet
    _ = walkLaw A := measure_toMeasurable A

/-- The first two rows of the sampler are independent. -/
theorem wilsonRows_rows_le (A B : Set WalkDriver) :
    wilsonRows {ξ | ξ 0 ∈ A ∧ ξ 1 ∈ B} ≤ walkLaw A * walkLaw B := by
  have hind : iIndepFun (fun i : ℕ => fun ξ : ℕ → WalkDriver => ξ i) wilsonRows :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (w : WalkDriver) => w) (fun _ => measurable_id)
  have h01 := (hind.indepFun (i := 0) (j := 1) (by decide)).measure_inter_preimage_eq_mul
    (toMeasurable walkLaw A) (toMeasurable walkLaw B) (measurableSet_toMeasurable _ _)
    (measurableSet_toMeasurable _ _)
  have hrow : ∀ (i : ℕ) (C : Set WalkDriver), MeasurableSet C →
      wilsonRows ((fun ξ : ℕ → WalkDriver => ξ i) ⁻¹' C) = walkLaw C := fun i C hC =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => walkLaw) i).measure_preimage
      hC.nullMeasurableSet
  calc wilsonRows {ξ | ξ 0 ∈ A ∧ ξ 1 ∈ B}
      ≤ wilsonRows ((fun ξ : ℕ → WalkDriver => ξ 0) ⁻¹' toMeasurable walkLaw A ∩
          (fun ξ : ℕ → WalkDriver => ξ 1) ⁻¹' toMeasurable walkLaw B) :=
        measure_mono fun ξ hξ =>
          ⟨subset_toMeasurable walkLaw A hξ.1, subset_toMeasurable walkLaw B hξ.2⟩
    _ = walkLaw A * walkLaw B := by
        rw [h01, hrow 0 _ (measurableSet_toMeasurable _ _),
          hrow 1 _ (measurableSet_toMeasurable _ _), measure_toMeasurable, measure_toMeasurable]

theorem walkLaw_eq_ofReal (A : Set WalkDriver) : walkLaw A = ENNReal.ofReal (prob A) := by
  rw [← FiniteAvalanches.External.Beurling.pathLaw_eq_walkLaw]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-! ### The box seen from a site -/

/-- The sum of the absolute coordinates of `x`. -/
def coordSum (x : Site 2) : ℕ := (x 0).natAbs + (x 1).natAbs

theorem abs_coord_le_coordSum (x : Site 2) (i : Fin 2) : |((x i : ℤ) : ℝ)| ≤ coordSum x := by
  have h0 : |((x 0 : ℤ) : ℝ)| = ((x 0).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h1 : |((x 1 : ℤ) : ℝ)| = ((x 1).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [coordSum, Nat.cast_add]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at h0 ⊢
    rw [h0]
    linarith [Nat.cast_nonneg (α := ℝ) (x 1).natAbs]
  · simp only [Fin.mk_one, Fin.isValue] at h1 ⊢
    rw [h1]
    linarith [Nat.cast_nonneg (α := ℝ) (x 0).natAbs]

theorem euclidNorm_le_abs_add_abs (w : Site 2) :
    euclidNorm w ≤ |((w 0 : ℤ) : ℝ)| + |((w 1 : ℤ) : ℝ)| := by
  rw [euclidNorm, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have h0 := sq_abs ((w 0 : ℤ) : ℝ)
  have h1 := sq_abs ((w 1 : ℤ) : ℝ)
  nlinarith [abs_nonneg ((w 0 : ℤ) : ℝ), abs_nonneg ((w 1 : ℤ) : ℝ)]

/-- Sites at distance less than `N - coordSum x` from `x` are in the box of size `N`. -/
theorem inBox_of_euclidNorm_lt {N : ℕ} {x w : Site 2}
    (hw : euclidNorm w < (N : ℝ) - coordSum x) : FiniteWired.inBox N (w + x) := by
  intro i
  have h1 := abs_coord_le_euclidNorm w i
  have h2 := abs_coord_le_coordSum x i
  have h3 : |(((w + x) i : ℤ) : ℝ)| < N := by
    rw [Pi.add_apply, Int.cast_add]
    calc |((w i : ℤ) : ℝ) + ((x i : ℤ) : ℝ)| ≤ |((w i : ℤ) : ℝ)| + |((x i : ℤ) : ℝ)| :=
          abs_add_le _ _
      _ < N := by linarith
  have h4 : |((w + x) i)| < (N : ℤ) := by exact_mod_cast h3
  constructor <;> linarith [abs_lt.1 h4]

/-- Sites in the box of size `N` are at distance at most `2 (N + coordSum x)` from `x`. -/
theorem euclidNorm_le_of_inBox {N : ℕ} {x w : Site 2} (hw : FiniteWired.inBox N (w + x)) :
    euclidNorm w ≤ 2 * ((N : ℝ) + coordSum x) := by
  have hc : ∀ i : Fin 2, |((w i : ℤ) : ℝ)| ≤ N + coordSum x := by
    intro i
    have h1 : |(((w + x) i : ℤ) : ℝ)| ≤ N := by
      have : |((w + x) i)| ≤ (N : ℤ) := abs_le.2 ⟨(hw i).1, (hw i).2⟩
      exact_mod_cast this
    have h2 := abs_coord_le_coordSum x i
    have h3 : ((w i : ℤ) : ℝ) = (((w + x) i : ℤ) : ℝ) - ((x i : ℤ) : ℝ) := by
      rw [Pi.add_apply, Int.cast_add]
      ring
    rw [h3]
    calc |(((w + x) i : ℤ) : ℝ) - ((x i : ℤ) : ℝ)| ≤
          |(((w + x) i : ℤ) : ℝ)| + |((x i : ℤ) : ℝ)| := abs_sub _ _
      _ ≤ N + coordSum x := by linarith
  have := euclidNorm_le_abs_add_abs w
  linarith [hc 0, hc 1]

/-! ### Event (a) -/

/-- **Event (a).** The branch of `x` returns to the disk of radius `r` after its first site at
distance `k` with probability at most `C r / k`. -/
theorem wilsonRows_reentryRows_le : ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ r₀ : ℕ, ∀ (x : Site 2) (k r N : ℕ),
    k₀ ≤ k → r₀ ≤ r → 64 * r ≤ k → k ^ 2 + 3 * coordSum x + 1 ≤ N →
      wilsonRows (reentryRows N x k r) ≤ ENNReal.ofReal (C * ((r : ℝ) / k)) := by
  obtain ⟨C, hC, k₀, r₀, h⟩ := reentry_le
  refine ⟨C, hC, k₀, r₀, fun x k r N hk hr hrk hN => ?_⟩
  have hN' : ((k : ℝ) ^ 2 + 3 * coordSum x + 1) ≤ N := by exact_mod_cast hN
  have hcs : (0 : ℝ) ≤ coordSum x := Nat.cast_nonneg _
  refine (wilsonRows_row_le 0 _).trans ?_
  rw [walkLaw_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  apply h (boxExterior N x) ((N : ℝ) - coordSum x) (2 * ((N : ℝ) + coordSum x) + 1)
  · intro w hw hin
    have := euclidNorm_le_of_inBox hin
    linarith
  · intro w hw
    by_contra hlt
    exact hw (inBox_of_euclidNorm_lt (not_le.1 hlt))
  · exact hk
  · exact hr
  · exact hrk
  · linarith
  · linarith
  · nlinarith [sq_nonneg (k : ℝ)]

/-! ### Event (b) -/

/-- The walk from the origin first visits `K` at time `T` and its loop erasure is `β`. -/
def firstHitErase (K : Set (Site 2)) (p : ℕ × List (Site 2)) : Set (ℕ → Dir 2) :=
  firstHit K p.1 ∩ {ω | walkErase 0 ω p.1 = p.2}

theorem measurableSet_firstHitErase (K : Set (Site 2)) (p : ℕ × List (Site 2)) :
    MeasurableSet (firstHitErase K p) := by
  apply DependsOnFirst.measurableSet (j := p.1)
  intro ω ω' h
  have hw : ∀ s ≤ p.1, walkPos 0 ω s = walkPos 0 ω' s := fun s hs => walkPos_congr_of_le 0 h hs
  simp only [firstHitErase, firstHit, Set.mem_inter_iff, Set.mem_setOf_eq,
    walkErase_congr h p.1 le_rfl, hw p.1 le_rfl]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, fun s hs => by rw [← hw s hs.le]; exact h2 s hs⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, fun s hs => by rw [hw s hs.le]; exact h2 s hs⟩, h3⟩

theorem pairwise_disjoint_firstHitErase (K : Set (Site 2)) :
    Pairwise (Function.onFun Disjoint (firstHitErase K)) := by
  intro p q hpq
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨⟨hp1, hp2⟩, hp3⟩ ⟨⟨hq1, hq2⟩, hq3⟩
  apply hpq
  have hT : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exact absurd hp1 (hq2 _ h)
    · exact h
    · exact absurd hq1 (hp2 _ h)
  refine Prod.ext hT ?_
  rw [← hp3, ← hq3, hT]

/-- A loop-erased path from the origin to a site at distance `m` crosses every annulus about a
neighbour `u` of the origin up to radius `m - 1`. -/
theorem walkErase_crosses (ω : ℕ → Dir 2) (T : ℕ) (u : Site 2) (hu : euclidNorm u = 1) (j : ℕ)
    (hj : 1 ≤ j) (hfar : (j : ℝ) + 1 ≤ euclidNorm (walkPos 0 ω T)) :
    ∃ z ∈ {z | z ∈ walkErase 0 ω T}, (j : ℝ) ≤ euclidNorm (z - u) ∧ euclidNorm (z - u) < j + 1 := by
  set β := walkErase 0 ω T with hβ
  have hne : β ≠ [] := walkErase_ne_nil 0 ω T
  have hlen : 0 < β.length := List.length_pos_of_ne_nil hne
  obtain ⟨l0, hl0⟩ := walkErase_start 0 ω T
  let f : ℕ → Site 2 := fun i => β.getD i 0
  have hf : ∀ i (hi : i < β.length), f i = β[i] := fun i hi => List.getD_eq_getElem _ _ hi
  have hchain := List.isChain_iff_getElem.1
    (show β.IsChain (fun a b => euclidNorm (b - a) ≤ 1) from walkErase_chain 0 ω T)
  have hstep : ∀ i < β.length - 1, euclidNorm (f (i + 1) - u) ≤ euclidNorm (f i - u) + 1 := by
    intro i hi
    rw [hf i (by omega), hf (i + 1) (by omega)]
    have h1 := hchain i (by omega)
    have h2 := euclidNorm_add_le (β[i] - u) (β[i + 1] - β[i])
    rw [show β[i] - u + (β[i + 1] - β[i]) = β[i + 1] - u by abel] at h2
    linarith
  have h0 : euclidNorm (f 0 - u) < j + 1 := by
    rw [hf 0 hlen]
    have : β[0] = 0 := by simp [hβ, hl0]
    rw [this, zero_sub, euclidNorm_neg, hu]
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hm : (j : ℝ) ≤ euclidNorm (f (β.length - 1) - u) := by
    rw [hf _ (by omega)]
    have hl : β[β.length - 1]'(by omega) = walkPos 0 ω T := by
      simpa [List.getLast_eq_getElem] using walkErase_getLast 0 ω T
    rw [hl]
    have := euclidNorm_sub_le (walkPos 0 ω T) u
    rw [hu] at this
    linarith
  obtain ⟨i, hi, h1, h2⟩ := exists_annulus_of_chain f u (β.length - 1) hstep j h0 hm
  refine ⟨f i, ?_, h1, h2⟩
  rw [hf i (by omega)]
  exact List.getElem_mem _

/-- **Event (b).** The walk from `y` reaches distance `r` from `x` before visiting the branch of
`x` with probability at most `c (8 / r) ^ (1/2)`. -/
theorem wilsonRows_escapeRows_le : ∃ c : ℝ, 0 < c ∧ ∀ (x y : Site 2) (k r N : ℕ),
    (lattice 2).Adj x y → 8 ≤ r → r ≤ k → k ^ 2 + 3 * coordSum x + 1 ≤ N →
      wilsonRows (escapeRows N x y r) ≤ ENNReal.ofReal (c * Real.sqrt (8 / r)) := by
  obtain ⟨c, hc, hB⟩ := beurling_crossing
  refine ⟨c, hc, fun x y k r N hxy hr hrk hN => ?_⟩
  set u := y - x with hu_def
  have hu : euclidNorm u = 1 := euclidNorm_sub_of_adj hxy
  set K := boxExterior N x with hK
  obtain ⟨j₁, hj₁⟩ : ∃ j, j = r / 4 := ⟨_, rfl⟩
  have hj₁2 : 2 ≤ j₁ := by omega
  have hj₁r : 4 * j₁ ≤ r := by omega
  have hr8 : (8 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : ((k : ℝ) ^ 2 + 3 * coordSum x + 1) ≤ N := by exact_mod_cast hN
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hcs : (0 : ℝ) ≤ coordSum x := Nat.cast_nonneg _
  have hj₁r' : 4 * (j₁ : ℝ) ≤ r := by exact_mod_cast hj₁r
  have hj₁8 : (r : ℝ) ≤ 8 * j₁ := by
    have : r ≤ 8 * j₁ := by omega
    exact_mod_cast this
  have hj₁pos : (0 : ℝ) < j₁ := by
    have : (0 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (by exact_mod_cast hj₁2)
  set ε := c * Real.sqrt (8 / r) with hε
  have hε0 : 0 ≤ ε := by positivity
  -- the escape bound for a branch that occurs
  have hesc : ∀ p : ℕ × List (Site 2), (firstHitErase K p).Nonempty →
      walkLaw (escapesList u r p.2) ≤ ENNReal.ofReal ε := by
    rintro ⟨T, β⟩ ⟨ω, ⟨hω1, -⟩, hω3⟩
    simp only at hω1 hω3
    subst hω3
    rw [walkLaw_eq_ofReal]
    apply ENNReal.ofReal_le_ofReal
    have hfar : (k : ℝ) ^ 2 + 1 ≤ euclidNorm (walkPos 0 ω T) := by
      by_contra hlt
      exact hω1 (inBox_of_euclidNorm_lt (by linarith))
    have hsub : escapesList u r (walkErase 0 ω T) ⊆
        escapesFrom (2 * (j₁ : ℝ)) {z | z ∈ walkErase 0 ω T} u := by
      rintro ω' ⟨t, ht, hav⟩
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [walkPos_zero', hu] at ht
        linarith
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht0
      refine ⟨t', ?_, fun s hs1 hs2 => hav s (by omega)⟩
      have h1 := euclidNorm_walkPos_succ_le' u ω' t'
      have h2 := euclidNorm_sub_le (walkPos u ω' t') u
      rw [hu] at h2
      linarith
    calc prob (escapesList u r (walkErase 0 ω T))
        ≤ prob (escapesFrom (2 * (j₁ : ℝ)) {z | z ∈ walkErase 0 ω T} u) :=
          measureReal_mono hsub
      _ ≤ c * Real.sqrt ((1 : ℕ) / (j₁ : ℝ)) := by
          apply hB _ u 1 j₁ one_pos (by omega)
          intro j hj hjj
          apply walkErase_crosses ω T u hu j hj
          have : (j : ℝ) + 1 ≤ j₁ := by exact_mod_cast hjj
          nlinarith
      _ ≤ ε := by
          rw [hε]
          apply mul_le_mul_of_nonneg_left _ hc.le
          apply Real.sqrt_le_sqrt
          rw [Nat.cast_one, div_le_div_iff₀ hj₁pos (by linarith)]
          linarith
  -- the decomposition over the first hitting time and the branch
  have hcover : escapeRows N x y r ⊆ ⋃ p : ℕ × List (Site 2),
      {ξ : ℕ → WalkDriver | ξ 0 ∈ firstHitErase K p ∧ ξ 1 ∈ escapesList u r p.2} := by
    rintro ξ ⟨T, hT, hesc'⟩
    exact Set.mem_iUnion.2 ⟨(T, walkErase 0 (ξ 0) T), ⟨hT, rfl⟩, hesc'⟩
  calc wilsonRows (escapeRows N x y r)
      ≤ ∑' p : ℕ × List (Site 2), wilsonRows
          {ξ : ℕ → WalkDriver | ξ 0 ∈ firstHitErase K p ∧ ξ 1 ∈ escapesList u r p.2} :=
        (measure_mono hcover).trans (measure_iUnion_le _)
    _ ≤ ∑' p : ℕ × List (Site 2), walkLaw (firstHitErase K p) * ENNReal.ofReal ε := by
        refine ENNReal.tsum_le_tsum fun p => (wilsonRows_rows_le _ _).trans ?_
        rcases (firstHitErase K p).eq_empty_or_nonempty with he | he
        · rw [he, measure_empty, zero_mul, zero_mul]
        · exact mul_le_mul_right (hesc p he) _
    _ = walkLaw (⋃ p : ℕ × List (Site 2), firstHitErase K p) * ENNReal.ofReal ε := by
        rw [ENNReal.tsum_mul_right, measure_iUnion (pairwise_disjoint_firstHitErase K)
          (measurableSet_firstHitErase K)]
    _ ≤ 1 * ENNReal.ofReal ε := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal ε := one_mul _

end

end FiniteAvalanches.Walk.BarlowMasson
