import FiniteAvalanches.Wilson.Lattice.Law

set_option autoImplicit false
namespace LocalColorSwap
open LatticeProb FiniteAvalanches.Wilson.Lattice MeasureTheory
open scoped Classical
noncomputable section

/-- Interchange the two original root sets, preserving every root. -/
def roots (R : RootPair) : RootPair where
  zero := R.one
  one := R.zero
  disjoint := R.disjoint.symm
  zero_nonempty := R.one_nonempty
  one_nonempty := R.zero_nonempty

@[simp] theorem roots_involutive (R : RootPair) : roots (roots R) = R := by
  cases R
  rfl

/-- Complement the full Boolean field, including roots and exterior sites. -/
def colors (σ : ColorField) : ColorField := fun x => !(σ x)

@[simp] theorem colors_involutive (σ : ColorField) : colors (colors σ) = σ := by
  funext x
  exact Bool.not_not _

theorem measurable_colors : Measurable colors :=
  measurable_pi_lambda _ (fun x => (measurable_of_finite Bool.not).comp (measurable_pi_apply x))

/-- Unknown partial colors remain unknown; actual edges and histories are retained. -/
def state (st : SamplerState) : SamplerState where
  colors x := (st.colors x).map Bool.not
  edges := st.edges
  history := st.history

@[simp] theorem state_colors (st : SamplerState) (x : Site 2) :
    (state st).colors x = (st.colors x).map Bool.not := rfl

@[simp] theorem state_involutive (st : SamplerState) : state (state st) = st := by
  cases st with
  | mk c e h =>
    dsimp only [state]
    congr 1
    funext x
    cases c x <;> simp

@[simp] theorem state_covered (st : SamplerState) : (state st).covered = st.covered := by
  ext x
  cases h : st.colors x <;> simp [SamplerState.covered, state, h]

theorem initial_state (R : RootPair) : initialSampler (roots R) = state (initialSampler R) := by
  unfold initialSampler state roots
  congr 1
  funext x
  by_cases h0 : x ∈ R.zero
  · have h1 : x ∉ R.one := fun h => Set.disjoint_left.mp R.disjoint h0 h
    simp only [if_pos h0, if_neg h1, Option.map_some, Bool.not_false]
  · by_cases h1 : x ∈ R.one
    · simp only [if_neg h0, if_pos h1, Option.map_some, Bool.not_true]
    · simp only [if_neg h0, if_neg h1, Option.map_none]

/-- The same stopped walk and chronological erasure are used after swapping colors. -/
theorem step_state (st : SamplerState) (x : Site 2) (w : WalkDriver) :
    samplerStep (state st) x w = (samplerStep st x w).map state := by
  by_cases hx : x ∈ st.covered
  · simp only [samplerStep, state_covered, if_pos hx, Option.map_some]
  · simp only [samplerStep, state_covered, if_neg hx]
    cases h : hitTime st.covered x w with
    | none => rfl
    | some T =>
      dsimp only
      simp only [Option.map_some]
      apply congrArg some
      dsimp only [state]
      congr 1
      funext v
      by_cases hv : v ∈ (walkErase x w T).dropLast
      · simp only [if_pos hv]
      · simp only [if_neg hv]

/-- All finite query lists commute with complementation under unchanged iid rows. -/
theorem run_state (st : SamplerState) (L : List (Site 2)) (ξ : ℕ → WalkDriver) :
    samplerRun (state st) L ξ = (samplerRun st L ξ).map state := by
  induction L generalizing st ξ with
  | nil => rfl
  | cons x xs ih =>
    simp only [samplerRun, step_state]
    cases h : samplerStep st x (ξ 0) with
    | none => rfl
    | some mid =>
      simp only [Option.map_some, Option.bind_some]
      exact ih mid _

theorem run_initial (R : RootPair) (L : List (Site 2)) (ξ : ℕ → WalkDriver) :
    samplerRun (initialSampler (roots R)) L ξ =
      (samplerRun (initialSampler R) L ξ).map state := by
  rw [initial_state, run_state]

end
end LocalColorSwap
