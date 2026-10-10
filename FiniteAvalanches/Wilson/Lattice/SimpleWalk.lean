import FiniteAvalanches.Wilson.Lattice.ColoredForests
import FiniteAvalanches.Wilson.Lattice.Paths
import FiniteAvalanches.Trees.Lattice.WiredLaw
import Mathlib.Probability.ProductMeasure

/-! Literal simple random walk drivers and ordered hitting events. Independent
uniform choices of the four actual lattice directions, including hitting at time zero. -/
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

abbrev WalkDriver := ℕ → FiniteWired.Direction

def directionLaw : Measure FiniteWired.Direction :=
  FiniteAvalanches.uniformMeasure FiniteWired.Direction

instance directionLaw_probability : IsProbabilityMeasure directionLaw :=
  inferInstanceAs (IsProbabilityMeasure (FiniteAvalanches.uniformMeasure FiniteWired.Direction))

def walkLaw : Measure WalkDriver := Measure.infinitePi (fun _ : ℕ => directionLaw)
instance walkLaw_probability : IsProbabilityMeasure walkLaw := by
  unfold walkLaw
  infer_instance

def position (x : Site 2) (d : WalkDriver) : ℕ → Site 2
  | 0 => x
  | n + 1 => position x d n + FiniteWired.step (d n)

@[simp] theorem position_zero (x : Site 2) (d : WalkDriver) : position x d 0 = x := rfl
@[simp] theorem position_succ (x : Site 2) (d : WalkDriver) (n : ℕ) :
    position x d (n + 1) = position x d n + FiniteWired.step (d n) := rfl

theorem position_adjacent (x : Site 2) (d : WalkDriver) (n : ℕ) :
    (lattice 2).Adj (position x d n) (position x d (n + 1)) := by
  change ∃ i, position x d (n + 1) = position x d n + unit i ∨
    position x d n = position x d (n + 1) + unit i
  refine ⟨(d n).1, ?_⟩
  cases h : (d n).2
  · right
    rw [position_succ, FiniteWired.step, h]
    simp
  · left
    rw [position_succ, FiniteWired.step, h]
    simp

def driverWalk (x : Site 2) (d : WalkDriver) : InfiniteWalk :=
  ⟨position x d, position_adjacent x d⟩

/-- tau_C < tau_A: some C visit precedes every A visit, including time zero. -/
def hitBefore (A C : Set (Site 2)) (x : Site 2) : Set WalkDriver :=
  {d | ∃ n, position x d n ∈ C ∧ ∀ m ≤ n, position x d m ∉ A}

theorem measurable_position (x : Site 2) (n : ℕ) : Measurable (fun d => position x d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.add ((measurable_of_countable FiniteWired.step).comp (measurable_pi_apply n))

theorem measurableSet_hitBefore (A C : Set (Site 2)) (x : Site 2) :
    MeasurableSet (hitBefore A C x) := by
  have hC (n : ℕ) : MeasurableSet {d : WalkDriver | position x d n ∈ C} :=
    (measurable_position x n) (Set.to_countable C).measurableSet
  have hA (n : ℕ) : MeasurableSet {d : WalkDriver | position x d n ∉ A} :=
    ((measurable_position x n) (Set.to_countable A).measurableSet).compl
  simp only [hitBefore, Set.setOf_exists, Set.setOf_and, Set.setOf_forall]
  exact MeasurableSet.iUnion (fun n => (hC n).inter
    (MeasurableSet.iInter (fun m => MeasurableSet.iInter (fun _ => hA m))))

theorem hitBefore_of_one_root (R : RootPair) {x : Site 2} (hx : x ∈ R.one) :
    hitBefore R.zero R.one x = Set.univ := by
  ext d
  simp only [Set.mem_univ, iff_true]
  refine ⟨0, hx, ?_⟩
  intro m hm
  have he : m = 0 := Nat.eq_zero_of_le_zero hm
  subst m
  exact fun h => Set.disjoint_left.mp R.disjoint h hx

theorem hitBefore_of_zero_root (R : RootPair) {x : Site 2} (hx : x ∈ R.zero) :
    hitBefore R.zero R.one x = ∅ := by
  ext d
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨n, _, hn⟩
  exact hn 0 (Nat.zero_le n) hx

end
end FiniteAvalanches.Wilson.Lattice
