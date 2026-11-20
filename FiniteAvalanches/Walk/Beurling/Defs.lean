/-
Adapted from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/Beurling/Defs.lean` of the development of the Lawler-Limic Beurling estimate
for Lean v4.35 and its Mathlib.
Changes: import `LatticeProb.Walk.KilledGreenPlanarLower` replaced by
`LatticeProb.Walk.Harnack.Basics`, `LatticeProb.Walk.Lazy`, `LatticeProb.Walk.Ball`,
`LatticeProb.Network.MaximumPrinciple`, `LatticeProb.Network.KilledGreen`,
`FiniteAvalanches.Walk.EuclidNormCoord`; namespace `LatticeProb.Beurling` renamed to
`FiniteAvalanches.Walk.Beurling`, with `open LatticeProb` added; `measurableSet_setOfPred` replaced
by `measurableSet_setOf` (3 times); the end-of-line comments of `disk`, `shellPart`, `axisSet` and
`green` replaced by docstrings, docstrings added to `walkPos`, `IsDense`, `diskFinset`, `prob` and
`Asymp`, and the statement of `Asymp` broken over three lines.
-/
import LatticeProb.Walk.Harnack.Basics
import LatticeProb.Walk.Lazy
import LatticeProb.Walk.Ball
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Network.KilledGreen
import FiniteAvalanches.Walk.EuclidNormCoord
import LatticeProb.Walk.PotentialKernel
import LatticeProb.Walk.Infinite

/-!
# Definitions for the Beurling estimate

Notation for the Beurling estimate for the simple random walk on `ℤ²`, following
G. F. Lawler and V. Limic, *The Beurling estimate for a class of random walks*,
Electron. J. Probab. 9 (2004).

The walk started at `x` with increments `ω` is `walkPos x ω`. For a radius `r` the disk `C_r` is
`disk r`, and `A[a, b]` is the part of `A` in the annulus `a ≤ |z| < b`. A set `A` is dense when
it meets every annulus `j ≤ |z| < j + 1`. The events `exitsBefore`, `hitsBefore` and
`stripExitsBefore` are `{τ_r < T_B}`, `{T⁰_B < τ_r}` and `{ρ_r < T_B}`. The Green function of
`C_r` is `green r`, `prob` is the probability under the path law of the walk, and `Asymp E f`
states `P(E n) ≍ 1 / f n`.

## Main statements

* `measurableSet_exitsBefore`, `measurableSet_hitsBefore`, `measurableSet_stripExitsBefore`:
  the three events are measurable.
* `exitsBefore_anti`: `{τ_r < T_B}` is antitone in `B`.
* `IsDense.exists_minimal`: every dense set contains a minimal one, one point in each annulus.
-/

noncomputable section

namespace FiniteAvalanches.Walk.Beurling
open LatticeProb
open MeasureTheory

/-- The walk started at `x` with increments `ω`, at time `t`. -/
def walkPos (x : Site 2) (ω : ℕ → Dir 2) (t : ℕ) : Site 2 := x + ∑ j ∈ Finset.range t, dirVec (ω j)
/-- The disk `C_r = {z : |z| < r}`. -/
def disk (r : ℝ) : Set (Site 2) := {z | euclidNorm z < r}
/-- The part `A[a, b]` of `A` in the annulus `a ≤ |z| < b`. -/
def shellPart (A : Set (Site 2)) (a b : ℝ) : Set (Site 2) :=
  {z | z ∈ A ∧ a ≤ euclidNorm z ∧ euclidNorm z < b}
/-- `A` meets every annulus `j ≤ |z| < j + 1`. -/
def IsDense (A : Set (Site 2)) : Prop := ∀ j : ℕ, ∃ z ∈ A, (j : ℝ) ≤ euclidNorm z ∧ euclidNorm z < j + 1
/-- {tau_r < T_B}: leave C_r (time 0 allowed) with no visit to B at times 1..t. -/
def exitsBefore (r : ℝ) (B : Set (Site 2)) (x : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, r ≤ euclidNorm (walkPos x ω t) ∧ ∀ s, 1 ≤ s → s ≤ t → walkPos x ω s ∉ B}
/-- {T^0_B < tau_r}: visit B (time 0 allowed) while still inside C_r. -/
def hitsBefore (B : Set (Site 2)) (r : ℝ) (x : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, walkPos x ω t ∈ B ∧ ∀ s ≤ t, euclidNorm (walkPos x ω s) < r}
/-- {rho_r < T_B}: leave the strip L_r = {|Im z| < r} before a positive-time visit to B. -/
def stripExitsBefore (r : ℝ) (B : Set (Site 2)) (x : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, r ≤ |((walkPos x ω t) 1 : ℝ)| ∧ ∀ s, 1 ≤ s → s ≤ t → walkPos x ω s ∉ B}
/-- The points `(i, 0)` of the real axis with `i ∈ S`. -/
def axisSet (S : Set ℤ) : Set (Site 2) := {z | z 1 = 0 ∧ z 0 ∈ S}
/-- The sites of the disk `C_r`, as a finite set. -/
def diskFinset (r : ℝ) : Finset (Site 2) := (ballFinset 2 r).filter (fun z => euclidNorm z < r)
/-- The Green function `G_r = G_{C_r}` of the disk: the expected number of visits to `z` before
the walk from `w` leaves `C_r`. The killed Green function of the library is divided by the
degree `4`. -/
noncomputable def green (r : ℝ) (w z : Site 2) : ℝ :=
  4 * Graph.killedGreenReal (lattice 2) (diskFinset r : Set (Site 2)) w z
/-- The probability of an event of the increments under the path law of the walk. -/
noncomputable def prob (E : Set (ℕ → Dir 2)) : ℝ := (pathLaw 2 E).toReal
/-- `P(E n) ≍ 1 / f n` for all large `n`. -/
def Asymp (E : ℕ → Set (ℕ → Dir 2)) (f : ℕ → ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c₁ / f n ≤ prob (E n) ∧ prob (E n) ≤ c₂ / f n

/-- The position of the walk at a fixed time is a measurable function of the increments. -/
theorem measurable_walkPos (x : Site 2) (t : ℕ) :
    Measurable fun ω : ℕ → Dir 2 => walkPos x ω t := by
  induction t with
  | zero =>
    simp only [walkPos, Finset.range_zero, Finset.sum_empty, add_zero]
    exact measurable_const
  | succ t ih =>
    have h : (fun ω : ℕ → Dir 2 => walkPos x ω (t + 1)) =
        (fun p : Site 2 × Dir 2 => p.1 + dirVec p.2) ∘ fun ω => (walkPos x ω t, ω t) := by
      funext ω
      simp only [walkPos, Finset.sum_range_succ, Function.comp_apply, add_assoc]
    rw [h]
    exact (measurable_of_countable _).comp (ih.prodMk (measurable_pi_apply t))

/-- Any property of the position of the walk at a fixed time is a measurable event. -/
theorem measurable_walkPos_pred (x : Site 2) (p : Site 2 → Prop) (t : ℕ) :
    Measurable fun ω : ℕ → Dir 2 => p (walkPos x ω t) :=
  (measurable_of_countable p).comp (measurable_walkPos x t)

/-- The event `{τ_r < T_B}` is measurable. -/
theorem measurableSet_exitsBefore (r : ℝ) (B : Set (Site 2)) (x : Site 2) :
    MeasurableSet (exitsBefore r B x) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred x (fun z => r ≤ euclidNorm z) t).and <| Measurable.forall fun s =>
      measurable_walkPos_pred x (fun z => 1 ≤ s → s ≤ t → z ∉ B) s

/-- The event `{T⁰_B < τ_r}` is measurable. -/
theorem measurableSet_hitsBefore (B : Set (Site 2)) (r : ℝ) (x : Site 2) :
    MeasurableSet (hitsBefore B r x) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred x (· ∈ B) t).and <| Measurable.forall fun s =>
      measurable_walkPos_pred x (fun z => s ≤ t → euclidNorm z < r) s

/-- The event `{ρ_r < T_B}` is measurable. -/
theorem measurableSet_stripExitsBefore (r : ℝ) (B : Set (Site 2)) (x : Site 2) :
    MeasurableSet (stripExitsBefore r B x) :=
  measurableSet_setOf.2 <| Measurable.exists fun t =>
    (measurable_walkPos_pred x (fun z => r ≤ |((z 1 : ℤ) : ℝ)|) t).and <| Measurable.forall fun s =>
      measurable_walkPos_pred x (fun z => 1 ≤ s → s ≤ t → z ∉ B) s

/-- Enlarging `B` shrinks the event `{τ_r < T_B}`. -/
theorem exitsBefore_anti {B B' : Set (Site 2)} (h : B ⊆ B') (r : ℝ) (x : Site 2) :
    exitsBefore r B' x ⊆ exitsBefore r B x :=
  fun _ ⟨t, ht, hs⟩ => ⟨t, ht, fun s h₁ h₂ hB => hs s h₁ h₂ (h hB)⟩

/-- Every dense set contains a minimal one: a point in each annulus `j ≤ |z| < j + 1`. -/
theorem IsDense.exists_minimal {A : Set (Site 2)} (hA : IsDense A) :
    ∃ w : ℕ → Site 2, (∀ j, w j ∈ A) ∧ ∀ j : ℕ,
      (j : ℝ) ≤ euclidNorm (w j) ∧ euclidNorm (w j) < j + 1 :=
  ⟨fun j => (hA j).choose, fun j => (hA j).choose_spec.1, fun j => (hA j).choose_spec.2⟩

/-- The point `(j, 0)` of the real axis. -/
def axisPt (j : ℤ) : Site 2 := ![j, 0]
/-- The walk is at `z` at a positive time `t` with no visit to `B` at times 1..t-1; for `z ∈ B`
it enters `B` at `z`. -/
def entersAt (B : Set (Site 2)) (z x : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, 1 ≤ t ∧ walkPos x ω t = z ∧ ∀ s, 1 ≤ s → s < t → walkPos x ω s ∉ B}
/-- {tau_r <= T_B}: leave C_r (time 0 allowed) with no visit to B at times 1..t-1. -/
def exitsWeakBefore (r : ℝ) (B : Set (Site 2)) (x : Site 2) : Set (ℕ → Dir 2) :=
  {ω | ∃ t, r ≤ euclidNorm (walkPos x ω t) ∧ ∀ s, 1 ≤ s → s < t → walkPos x ω s ∉ B}

end FiniteAvalanches.Walk.Beurling
