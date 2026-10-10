import FiniteAvalanches.Wilson.Lattice.HittingTimes
import FiniteAvalanches.Wilson.Lattice.WiredForestLaw

/-! Literal finite-query recurrent Wilson sampler. Partial colors retain unknown
values; complete stopped walks and their chronological erasures are distinguished. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Trees.Lattice MeasureTheory
open scoped Classical
noncomputable section

/-- The actual first T steps, including both endpoints and all nearest-neighbor steps. -/
def dirWalkFinite (x : Site 2) (w : WalkDriver) (T : ℕ) : FiniteWalk where
  length := T
  vertex i := position x w i.val
  adjacent i := by simpa using position_adjacent x w i.val

/-- A least genuine hit, or none exactly when the complete infinite word avoids S. -/
def hitTime (S : Set (Site 2)) (x : Site 2) (w : WalkDriver) : Option ℕ :=
  if h : ∃ n, position x w n ∈ S then some (Nat.find h) else none

theorem hitTime_eq_some_iff (S : Set (Site 2)) (x : Site 2) (w : WalkDriver) (T : ℕ) :
    hitTime S x w = some T ↔ position x w T ∈ S ∧ ∀ n < T, position x w n ∉ S := by
  unfold hitTime
  by_cases h : ∃ n, position x w n ∈ S
  · rw [dif_pos h, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨Nat.find_spec h, fun n hn => Nat.find_min h hn⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm (Nat.find_min' h h1)
        (not_lt.mp fun hlt => h2 _ hlt (Nat.find_spec h))
  · rw [dif_neg h]
    constructor
    · intro hh; cases hh
    · rintro ⟨h1, _⟩
      exact (h ⟨T, h1⟩).elim

theorem hitTime_eq_none_iff (S : Set (Site 2)) (x : Site 2) (w : WalkDriver) :
    hitTime S x w = none ↔ ∀ n, position x w n ∉ S := by
  unfold hitTime
  by_cases h : ∃ n, position x w n ∈ S
  · rw [dif_pos h]
    constructor
    · intro hh; cases hh
    · intro hn
      obtain ⟨n, hm⟩ := h
      exact (hn n hm).elim
  · rw [dif_neg h]
    exact ⟨fun _ n hn => h ⟨n, hn⟩, fun _ => rfl⟩

/-- Non-stopping retains its actual infinite walk, not a finite surrogate or default. -/
def stoppedTrace (S : Set (Site 2)) (x : Site 2) (w : WalkDriver) : StoppedTrace S x :=
  match h : hitTime S x w with
  | some T => StoppedTrace.hit (dirWalkFinite x w T)
      (by simp [FiniteWalk.start, dirWalkFinite])
      ((hitTime_eq_some_iff S x w T).mp h).1
      (fun i => ((hitTime_eq_some_iff S x w T).mp h).2 i.val i.isLt)
  | none => StoppedTrace.escape (driverWalk x w) rfl ((hitTime_eq_none_iff S x w).mp h)

/-- Online chronological erasure: truncate at a revisited vertex, append a new one. -/
def eraseStep (acc : List (Site 2)) (v : Site 2) : List (Site 2) :=
  acc.takeWhile (fun u => decide (u ≠ v)) ++ [v]

/-- Chronological erasure of the COMPLETE stopped word X_0,...,X_T. -/
def walkErase (x : Site 2) (w : WalkDriver) (T : ℕ) : List (Site 2) :=
  (List.range (T + 1)).foldl (fun acc n => eraseStep acc (position x w n)) []

/-- Consecutive unordered pairs. Actual NN walks give actual lattice branch edges. -/
def branchEdges (path : List (Site 2)) : Finset (Sym2 (Site 2)) :=
  ((path.zip path.tail).map fun p => s(p.1, p.2)).toFinset

/-- Partial colors and complete stopped histories. An unrevealed site has NO color. -/
structure SamplerState where
  colors : Site 2 → Option Bool
  edges : Finset (Sym2 (Site 2))
  history : List FiniteWalk

/-- Only the prescribed roots are colored initially, with their original colors. -/
def initialSampler (R : RootPair) : SamplerState where
  colors x := if x ∈ R.zero then some false else if x ∈ R.one then some true else none
  edges := ∅
  history := []

def SamplerState.covered (st : SamplerState) : Set (Site 2) :=
  {x | st.colors x ≠ none}

/-- A covered start consumes its row and changes nothing. A fresh start runs to the
FIRST actual hit and colors only the retained branch, excluding its old endpoint. -/
def samplerStep (st : SamplerState) (x : Site 2) (w : WalkDriver) : Option SamplerState :=
  if x ∈ st.covered then some st
  else match hitTime st.covered x w with
  | none => none
  | some T =>
    let branch := walkErase x w T
    some { colors := fun v => if v ∈ branch.dropLast then st.colors (position x w T) else st.colors v
           edges := st.edges ∪ branchEdges branch
           history := st.history ++ [dirWalkFinite x w T] }

/-- One independent row per slot, including repeated and already covered queries. -/
def samplerRun : SamplerState → List (Site 2) → (ℕ → WalkDriver) → Option SamplerState
  | st, [], _ => some st
  | st, x :: xs, ω => (samplerStep st x (ω 0)).bind fun st' =>
      samplerRun st' xs (fun i => ω (i + 1))

/-- Every row is an actual iid uniform four-direction infinite simple random walk. -/
def wilsonRows : Measure (ℕ → WalkDriver) := Measure.infinitePi (fun _ : ℕ => walkLaw)
instance wilsonRows_probability : IsProbabilityMeasure wilsonRows := by
  unfold wilsonRows
  infer_instance

theorem samplerRun_of_covered (st : SamplerState) (L : List (Site 2))
    (h : ∀ x ∈ L, x ∈ st.covered) (ω : ℕ → WalkDriver) : samplerRun st L ω = some st := by
  induction L generalizing ω with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ∈ st.covered := h x (by simp)
    simp only [samplerRun, samplerStep, if_pos hx, Option.bind_some]
    exact ih (fun y hy => h y (by simp [hy])) _

/-- The complete finite JOINT pattern, including absent as well as present edges. -/
def jointEvent (B : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) : Set ForestField :=
  {ω | (∀ e ∈ B, ω.1 e = pe e) ∧ ∀ d ∈ D, ω.2 d = pc d}

/-- The same full joint query of a genuinely successful finite Wilson run.
Unknown colors do not satisfy either Boolean observation. -/
def samplerEvent (R : RootPair) (L : List (Site 2)) (B : Finset LatticeEdge)
    (D : Finset (Site 2)) (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) :
    Set (ℕ → WalkDriver) :=
  {ξ | ∃ st, samplerRun (initialSampler R) L ξ = some st ∧
    (∀ e ∈ B, decide (e.val ∈ st.edges) = pe e) ∧
    ∀ d ∈ D, st.colors d = some (pc d)}

/-- Every finite original lattice edge/color pattern is characterized JOINTLY.
Coverage says precisely that the observed sites and edge endpoints were queried. -/
def IsWilsonLaw (R : RootPair) (ν : ProbabilityMeasure ForestField) : Prop :=
  (∀ᵐ ω ∂(ν : Measure ForestField), is_colored_forest R ω) ∧
  ∀ (L : List (Site 2)) (B : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool),
    (∀ e ∈ B, ∀ x ∈ e.val, x ∈ L) → (∀ d ∈ D, d ∈ L) →
    (ν : Measure ForestField) (jointEvent B D pe pc) =
      wilsonRows (samplerEvent R L B D pe pc)

end
end FiniteAvalanches.Wilson.Lattice
