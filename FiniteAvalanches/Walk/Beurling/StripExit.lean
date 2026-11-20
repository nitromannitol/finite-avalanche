/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/StripExit.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: imports of the Beurling modules renamed to this repository's; namespace
`LatticeProb.Beurling` renamed to `FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added;
`Set.mem_ofPred_eq` replaced by `Set.mem_setOf_eq` (3 times); `measurableSet_setOfPred` replaced by
`measurableSet_setOf` (once).
-/
import FiniteAvalanches.Walk.Beurling.HalfLineProduct

/-!
# The strip exit from the real axis

For the simple random walk on `ℤ²` started at the origin, the probability of leaving the strip
`{|Im z| < n}` before a positive-time visit to the real axis is `1 / (2 n)`. This is the
gambler's ruin input of the Beurling estimate of G. F. Lawler and V. Limic, *The Beurling
estimate for a class of random walks*, Electron. J. Probab. 9 (2004): the event
`{ρ_n < T_ℤ}` has probability of order `1 / n`.

A horizontal first step puts the walk on the real axis, so the event fails. After a vertical first
step the imaginary part is `±1`. Let `g y` be the probability that a walk whose imaginary part
starts at `y` reaches `|Im| ≥ n` without visiting `Im = 0`. The Markov property at time one gives
`g y = (g (y - 1) + g (y + 1)) / 2` for `0 < |y| < n`, and `g 0 = 0`, `g y = 1` for `n ≤ |y|`.
A function on `0, …, n` with these properties is linear, which is the gambler's ruin computation
of G. F. Lawler and V. Limic, *Random walk: a modern introduction*, Cambridge University Press
(2010), Proposition 5.1.1; it gives `g (±1) = 1 / n`. The recursion determines `g`, so the
almost-sure absorption of the walk is not needed.

## Main statements

* `prob_verticalExit_harmonic`: the discrete harmonic equation for `g`.
* `eq_mul_of_harmonic`: a harmonic function on `0, …, n` vanishing at `0` is linear.
* `strip_exit_axis_eq`: the exit probability is `1 / (2 n)`.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb
open MeasureTheory

theorem prob_empty : prob ∅ = 0 := by simp [prob]

theorem prob_univ : prob Set.univ = 1 := by simp [prob]

/-! ### The vertical coordinate -/

/-- The vertical component of a step. -/
def vstep (a : Dir 2) : ℤ := dirVec a 1

/-- The walk, whose imaginary part started at `y`, reaches `|Im| ≥ n` at some time `t` without
having `Im = 0` at any time up to `t`. -/
def verticalExit (n : ℕ) (y : ℤ) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, (n : ℤ) ≤ |y + walkPos 0 ω t 1| ∧ ∀ s ≤ t, y + walkPos 0 ω s 1 ≠ 0}

theorem walkPos_one (ω : ℕ → Dir 2) : walkPos 0 ω 1 = dirVec (ω 0) := by
  simp [walkPos]

/-- The imaginary part after `1 + t` steps is the vertical part of the first step plus the
imaginary part of the walk driven by the later increments. -/
theorem walkPos_one_add_apply (ω : ℕ → Dir 2) (t : ℕ) :
    walkPos 0 ω (1 + t) 1 = vstep (ω 0) + walkPos 0 (shiftBy 1 ω) t 1 := by
  rw [walkPos_add_apply, walkPos_one]
  rfl

theorem measurableSet_verticalExit (n : ℕ) (y : ℤ) : MeasurableSet (verticalExit n y) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred 0 (fun z => (n : ℤ) ≤ |y + z 1|) t).and <| Measurable.forall fun s =>
      measurable_walkPos_pred 0 (fun z => s ≤ t → y + z 1 ≠ 0) s

/-- A walk whose imaginary part starts at `0` has visited `Im = 0` at time `0`. -/
theorem verticalExit_zero (n : ℕ) : verticalExit n 0 = ∅ := by
  ext ω
  refine ⟨fun hω => absurd hω ?_, fun hω => absurd hω (Set.notMem_empty ω)⟩
  simp only [verticalExit, Set.mem_setOf_eq, not_exists,
    not_and, not_forall]
  exact fun t _ => ⟨0, Nat.zero_le _, by simp [walkPos]⟩

/-- A walk that starts outside the strip has already left it. -/
theorem verticalExit_of_le {n : ℕ} (hn : 1 ≤ n) {y : ℤ} (hy : (n : ℤ) ≤ |y|) :
    verticalExit n y = Set.univ := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [abs_zero] at hy
    omega
  refine Set.eq_univ_of_forall fun ω => ⟨0, by simpa [walkPos] using hy, fun s hs => ?_⟩
  obtain rfl : s = 0 := by omega
  simpa [walkPos] using hy0

/-- The Markov property at time one for `verticalExit`. -/
theorem mem_verticalExit_iff {n : ℕ} {y : ℤ} (hy0 : y ≠ 0) (hyn : |y| < n) (ω : ℕ → Dir 2) :
    ω ∈ verticalExit n y ↔ shiftBy 1 ω ∈ verticalExit n (y + vstep (ω 0)) := by
  constructor
  · rintro ⟨t, ht, hs⟩
    obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · have h0 : walkPos 0 ω 0 1 = 0 := by simp [walkPos]
        rw [h0, add_zero] at ht
        exact absurd ht (not_le.2 hyn)
      · exact ⟨t - 1, by omega⟩
    refine ⟨t', ?_, fun s hs' => ?_⟩
    · rw [walkPos_one_add_apply, ← add_assoc] at ht
      exact ht
    · have := hs (1 + s) (by omega)
      rwa [walkPos_one_add_apply, ← add_assoc] at this
  · rintro ⟨t, ht, hs⟩
    refine ⟨1 + t, ?_, fun s hs' => ?_⟩
    · rw [walkPos_one_add_apply, ← add_assoc]
      exact ht
    · rcases Nat.eq_zero_or_pos s with rfl | h
      · simpa [walkPos] using hy0
      · obtain ⟨s', rfl⟩ : ∃ s', s = 1 + s' := ⟨s - 1, by omega⟩
        rw [walkPos_one_add_apply, ← add_assoc]
        exact hs s' (by omega)

/-! ### The first step -/

theorem pathLaw_firstStep (a : Dir 2) : pathLaw 2 {ω | ω 0 = a} = (4 : ENNReal)⁻¹ := by
  have h := congrArg (fun μ => μ {a}) (pathLaw_map_eval 2 0)
  rw [Measure.map_apply (measurable_pi_apply 0) (MeasurableSet.singleton a),
    stepLaw_singleton] at h
  rw [show {ω : ℕ → Dir 2 | ω 0 = a} = (fun ω => ω 0) ⁻¹' {a} from rfl, h]
  norm_num

theorem prob_firstStep (F : Dir 2 → Set (ℕ → Dir 2)) (hF : ∀ a, MeasurableSet (F a)) :
    prob {ω | shiftBy 1 ω ∈ F (ω 0)} = ∑ a : Dir 2, (1 / 4 : ℝ) * prob (F a) := by
  have hset : {ω | shiftBy 1 ω ∈ F (ω 0)} = ⋃ a, {ω | ω 0 = a} ∩ shiftBy 1 ⁻¹' F a := by
    ext ω
    simp
  have hA : ∀ a, DependsOnFirst 1 {ω : ℕ → Dir 2 | ω 0 = a} := fun a ω ω' h => by
    simp only [Set.mem_setOf_eq]
    rw [h 0 one_pos]
  have hm : ∀ a, MeasurableSet ({ω : ℕ → Dir 2 | ω 0 = a} ∩ shiftBy 1 ⁻¹' F a) := fun a =>
    (hA a).measurableSet.inter (measurable_shiftBy 1 (hF a))
  have hd : Pairwise (Function.onFun Disjoint fun a : Dir 2 =>
      {ω : ℕ → Dir 2 | ω 0 = a} ∩ shiftBy 1 ⁻¹' F a) := fun a b hab =>
    Set.disjoint_left.2 fun ω ha hb => hab (ha.1.symm.trans hb.1)
  have hp : ∀ a, prob ({ω : ℕ → Dir 2 | ω 0 = a} ∩ shiftBy 1 ⁻¹' F a) =
      (1 / 4 : ℝ) * prob (F a) := fun a => by
    rw [prob, markov_split (hA a) (hF a), pathLaw_firstStep, ENNReal.toReal_mul, prob]
    simp
  rw [hset]
  exact (measureReal_iUnion_fintype hd hm).trans (Finset.sum_congr rfl fun a _ => hp a)

/-! ### Gambler's ruin -/

/-- The discrete harmonic equation for the probability of leaving the strip before returning
to the axis. -/
theorem prob_verticalExit_harmonic {n : ℕ} {y : ℤ} (hy0 : y ≠ 0) (hyn : |y| < n) :
    prob (verticalExit n y) =
      (prob (verticalExit n (y + 1)) + prob (verticalExit n (y - 1))) / 2 := by
  have hset : verticalExit n y =
      {ω | shiftBy 1 ω ∈ verticalExit n (y + vstep (ω 0))} := by
    ext ω
    exact mem_verticalExit_iff hy0 hyn ω
  have h := prob_firstStep (fun a => verticalExit n (y + vstep a))
    (fun a => measurableSet_verticalExit n _)
  rw [← hset] at h
  have e : ∑ a : Dir 2, (1 / 4 : ℝ) * prob (verticalExit n (y + vstep a)) =
      (1 / 2) * prob (verticalExit n y) + (1 / 4) * prob (verticalExit n (y + 1)) +
        (1 / 4) * prob (verticalExit n (y - 1)) := by
    simp [Fintype.sum_prod_type, vstep, dirVec, sub_eq_add_neg]
    ring
  rw [e] at h
  linarith

/-- A function on `0, …, n` that vanishes at `0` and is the average of its neighbours at the
interior points is linear. -/
theorem eq_mul_of_harmonic (f : ℕ → ℝ) (n : ℕ) (h0 : f 0 = 0)
    (h : ∀ k, 1 ≤ k → k < n → f k = (f (k - 1) + f (k + 1)) / 2) :
    ∀ k, k ≤ n → f k = k * f 1 := by
  have key : ∀ k, k + 1 ≤ n → f k = k * f 1 ∧ f (k + 1) = (k + 1 : ℕ) * f 1 := by
    intro k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      have h3 := h (k + 1) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at h3
      refine ⟨h2, ?_⟩
      push_cast at h1 h2 ⊢
      linarith
  intro k hk
  rcases k with _ | k
  · simp [h0]
  · exact (key k hk).2

/-- From height `1`, the walk leaves the strip before returning to the axis with probability
`1 / n`. -/
theorem prob_verticalExit_one {n : ℕ} (hn : 1 ≤ n) : prob (verticalExit n 1) = 1 / n := by
  have h0 : prob (verticalExit n ((0 : ℕ) : ℤ)) = 0 := by
    rw [Nat.cast_zero, verticalExit_zero, prob_empty]
  have hh : ∀ k : ℕ, 1 ≤ k → k < n →
      prob (verticalExit n (k : ℤ)) = (prob (verticalExit n ((k - 1 : ℕ) : ℤ)) +
        prob (verticalExit n ((k + 1 : ℕ) : ℤ))) / 2 := by
    intro k hk1 hkn
    have h := prob_verticalExit_harmonic (n := n) (y := (k : ℤ)) (by omega)
      (by rw [abs_of_nonneg (Nat.cast_nonneg k)]; exact_mod_cast hkn)
    have e1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    have e2 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [h, e1, e2]
    ring
  have key := eq_mul_of_harmonic (fun k : ℕ => prob (verticalExit n (k : ℤ))) n h0 hh n le_rfl
  have hu : verticalExit n (n : ℤ) = Set.univ :=
    verticalExit_of_le hn (by rw [abs_of_nonneg (Nat.cast_nonneg n)])
  simp only [hu, prob_univ, Nat.cast_one] at key
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  rw [eq_div_iff hn0]
  linarith

/-- From height `-1`, the walk leaves the strip before returning to the axis with probability
`1 / n`. -/
theorem prob_verticalExit_neg_one {n : ℕ} (hn : 1 ≤ n) : prob (verticalExit n (-1)) = 1 / n := by
  have h0 : prob (verticalExit n (-((0 : ℕ) : ℤ))) = 0 := by
    rw [Nat.cast_zero, neg_zero, verticalExit_zero, prob_empty]
  have hh : ∀ k : ℕ, 1 ≤ k → k < n →
      prob (verticalExit n (-(k : ℤ))) = (prob (verticalExit n (-((k - 1 : ℕ) : ℤ))) +
        prob (verticalExit n (-((k + 1 : ℕ) : ℤ)))) / 2 := by
    intro k hk1 hkn
    have h := prob_verticalExit_harmonic (n := n) (y := -(k : ℤ)) (by omega)
      (by rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg k)]; exact_mod_cast hkn)
    have e1 : -((k - 1 : ℕ) : ℤ) = -(k : ℤ) + 1 := by omega
    have e2 : -((k + 1 : ℕ) : ℤ) = -(k : ℤ) - 1 := by push_cast; ring
    rw [h, e1, e2]
  have key := eq_mul_of_harmonic (fun k : ℕ => prob (verticalExit n (-(k : ℤ)))) n h0 hh n le_rfl
  have hu : verticalExit n (-(n : ℤ)) = Set.univ :=
    verticalExit_of_le hn (by rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)])
  simp only [hu, prob_univ, Nat.cast_one] at key
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  rw [eq_div_iff hn0]
  linarith

/-! ### The exit from the real axis -/

/-- The Markov property at time one for the strip exit: the first step is vertical, and the
walk driven by the later increments leaves the strip from height `±1` before visiting the
axis. -/
theorem stripExitsBefore_axis_eq {n : ℕ} (hn : 1 ≤ n) :
    stripExitsBefore (n : ℝ) (axisSet Set.univ) 0 =
      {ω | shiftBy 1 ω ∈ verticalExit n (vstep (ω 0))} := by
  ext ω
  rw [mem_stripExitsBefore_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht, hs⟩
    obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · have h0 : walkPos 0 ω 0 1 = 0 := by simp [walkPos]
        rw [h0] at ht
        simp only [abs_zero] at ht
        omega
      · exact ⟨t - 1, by omega⟩
    refine ⟨t', ?_, fun s hs' => ?_⟩
    · rw [walkPos_one_add_apply] at ht
      exact ht
    · intro h0
      refine hs (1 + s) (by omega) (by omega) ⟨?_, trivial⟩
      rw [walkPos_one_add_apply]
      exact h0
  · rintro ⟨t, ht, hs⟩
    refine ⟨1 + t, ?_, fun s h1 h2 => ?_⟩
    · rw [walkPos_one_add_apply]
      exact ht
    · obtain ⟨s', rfl⟩ : ∃ s', s = 1 + s' := ⟨s - 1, by omega⟩
      rintro ⟨h3, -⟩
      rw [walkPos_one_add_apply] at h3
      exact hs s' (by omega) h3

/-- The simple random walk on `ℤ²` started at the origin leaves the strip `{|Im z| < n}` before
a positive-time visit to the real axis with probability `1 / (2 n)`. -/
theorem strip_exit_axis_eq (n : ℕ) (hn : 1 ≤ n) :
    prob (stripExitsBefore n (axisSet Set.univ) 0) = 1 / (2 * (n : ℝ)) := by
  rw [stripExitsBefore_axis_eq hn, prob_firstStep (fun a => verticalExit n (vstep a))
    (fun a => measurableSet_verticalExit n _)]
  have e : ∑ a : Dir 2, (1 / 4 : ℝ) * prob (verticalExit n (vstep a)) =
      (1 / 4) * prob (verticalExit n 1) + (1 / 4) * prob (verticalExit n (-1)) := by
    simp [Fintype.sum_prod_type, vstep, dirVec, verticalExit_zero, prob_empty]
  rw [e, prob_verticalExit_one hn, prob_verticalExit_neg_one hn]
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  field_simp
  ring

end FiniteAvalanches.Walk.Beurling
