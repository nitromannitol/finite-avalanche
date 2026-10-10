import FiniteAvalanches.Wilson.Lattice.Law
import FiniteAvalanches.Wilson.Lattice.ContinuityRoots
import Mathlib.MeasureTheory.Integral.Indicator

/-! Common-increment exploration under locally converging original roots.
Partial colors converge at each vertex; the finite revealed edges and complete
stopped histories eventually agree. Global equality of root fields is not used. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Trees.Lattice MeasureTheory Filter
open scoped Classical
noncomputable section

/-- Attach the erased first T increments, retaining the original endpoint color
and the complete word. This is the literal update in a successful sampler step. -/
def appendWalkBranch (st : SamplerState) (x : Site 2) (w : WalkDriver) (T : ℕ) : SamplerState :=
  { colors := fun v => if v ∈ (walkErase x w T).dropLast then st.colors (position x w T)
      else st.colors v
    edges := st.edges ∪ branchEdges (walkErase x w T)
    history := st.history ++ [dirWalkFinite x w T] }

theorem samplerStep_eq_appendWalkBranch (st : SamplerState) (x : Site 2)
    (w : WalkDriver) (T : ℕ) (hx : x ∉ st.covered) (hT : hitTime st.covered x w = some T) :
    samplerStep st x w = some (appendWalkBranch st x w T) := by
  simp only [samplerStep, if_neg hx, hT, appendWalkBranch]

/-- A genuine successful step preserves pointwise local agreement. Root membership
is stabilized on the FULL finite stopped word before identifying the first hit. -/
theorem samplerStep_local_colors (stj : ℕ → SamplerState) (st out : SamplerState)
    (hc : ∀ v, ∀ᶠ j in atTop, (stj j).colors v = st.colors v)
    (he : ∀ᶠ j in atTop, (stj j).edges = st.edges)
    (hh : ∀ᶠ j in atTop, (stj j).history = st.history)
    (x : Site 2) (w : WalkDriver) (hs : samplerStep st x w = some out) :
    ∃ outj : ℕ → SamplerState,
      (∀ᶠ j in atTop, samplerStep (stj j) x w = some (outj j)) ∧
      (∀ v, ∀ᶠ j in atTop, (outj j).colors v = out.colors v) ∧
      (∀ᶠ j in atTop, (outj j).edges = out.edges) ∧
      (∀ᶠ j in atTop, (outj j).history = out.history) := by
  by_cases hx : x ∈ st.covered
  · have hout : out = st := by simpa [samplerStep, hx] using hs.symm
    subst out
    refine ⟨stj, ?_, hc, he, hh⟩
    filter_upwards [hc x] with j hj
    have hxj : x ∈ (stj j).covered := by
      simpa only [SamplerState.covered, Set.mem_setOf_eq, hj] using hx
    simp only [samplerStep, if_pos hxj]
  · cases hT : hitTime st.covered x w with
    | none => simp [samplerStep, hx, hT] at hs
    | some T =>
      have hout : out = appendWalkBranch st x w T := by
        rw [samplerStep_eq_appendWalkBranch st x w T hx hT] at hs
        exact (Option.some.inj hs).symm
      subst out
      refine ⟨fun j => appendWalkBranch (stj j) x w T, ?_, ?_, ?_, ?_⟩
      · have hfinite : ∀ᶠ j in atTop, ∀ n : Fin (T + 1),
            (stj j).colors (position x w n.val) = st.colors (position x w n.val) :=
          eventually_all.mpr (fun n => hc (position x w n.val))
        filter_upwards [hfinite] with j hj
        have hcover (n : ℕ) (hn : n ≤ T) :
            position x w n ∈ (stj j).covered ↔ position x w n ∈ st.covered := by
          simp only [SamplerState.covered, Set.mem_setOf_eq, hj ⟨n, Nat.lt_succ_of_le hn⟩]
        have hxj : x ∉ (stj j).covered := by
          simpa only [position_zero] using (hcover 0 (Nat.zero_le T)).not.mpr hx
        have hTj : hitTime (stj j).covered x w = some T := by
          apply (hitTime_eq_some_iff _ _ _ _).mpr
          obtain ⟨ht, hf⟩ := (hitTime_eq_some_iff _ _ _ _).mp hT
          exact ⟨(hcover T le_rfl).mpr ht,
            fun n hn => (hcover n (Nat.le_of_lt hn)).not.mpr (hf n hn)⟩
        exact samplerStep_eq_appendWalkBranch _ _ _ _ hxj hTj
      · intro v
        filter_upwards [hc v, hc (position x w T)] with j hv ht
        simp only [appendWalkBranch, hv, ht]
      · filter_upwards [he] with j hj
        simp only [appendWalkBranch, hj]
      · filter_upwards [hh] with j hj
        simp only [appendWalkBranch, hj]

/-- Induction on the literal finite query list. No source continuity or successful
run of a perturbed root field is an input. -/
theorem samplerRun_local_colors (stj : ℕ → SamplerState) (st out : SamplerState)
    (hc : ∀ v, ∀ᶠ j in atTop, (stj j).colors v = st.colors v)
    (he : ∀ᶠ j in atTop, (stj j).edges = st.edges)
    (hh : ∀ᶠ j in atTop, (stj j).history = st.history)
    (L : List (Site 2)) (ξ : ℕ → WalkDriver) (hs : samplerRun st L ξ = some out) :
    ∃ outj : ℕ → SamplerState,
      (∀ᶠ j in atTop, samplerRun (stj j) L ξ = some (outj j)) ∧
      (∀ v, ∀ᶠ j in atTop, (outj j).colors v = out.colors v) ∧
      (∀ᶠ j in atTop, (outj j).edges = out.edges) ∧
      (∀ᶠ j in atTop, (outj j).history = out.history) := by
  induction L generalizing stj st out ξ with
  | nil =>
    have hout : out = st := (Option.some.inj hs).symm
    subst out
    exact ⟨stj, Eventually.of_forall (fun _ => rfl), hc, he, hh⟩
  | cons x xs ih =>
    cases hstep : samplerStep st x (ξ 0) with
    | none => simp [samplerRun, hstep] at hs
    | some mid =>
      have htail : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hstep, Option.bind_some] using hs
      obtain ⟨midj, hmid, hmc, hme, hmh⟩ :=
        samplerStep_local_colors stj st mid hc he hh x (ξ 0) hstep
      obtain ⟨outj, hout, hoc, hoe, hoh⟩ :=
        ih midj mid out hmc hme hmh (fun i => ξ (i + 1)) htail
      refine ⟨outj, ?_, hoc, hoe, hoh⟩
      filter_upwards [hmid, hout] with j hm ht
      simpa only [samplerRun, hm, Option.bind_some] using ht

/-- Actual source exploration: every original coordinate keeps its local root
meaning, while the finitely explored words/branches eventually match exactly. -/
theorem samplerRun_local_roots (Rj : ℕ → RootPair) (R : RootPair)
    (hl : ∀ x, ∀ᶠ j in atTop,
      (x ∈ (Rj j).zero ↔ x ∈ R.zero) ∧ (x ∈ (Rj j).one ↔ x ∈ R.one))
    (out : SamplerState) (L : List (Site 2)) (ξ : ℕ → WalkDriver)
    (hs : samplerRun (initialSampler R) L ξ = some out) :
    ∃ outj : ℕ → SamplerState,
      (∀ᶠ j in atTop, samplerRun (initialSampler (Rj j)) L ξ = some (outj j)) ∧
      (∀ v, ∀ᶠ j in atTop, (outj j).colors v = out.colors v) ∧
      (∀ᶠ j in atTop, (outj j).edges = out.edges) ∧
      (∀ᶠ j in atTop, (outj j).history = out.history) := by
  apply samplerRun_local_colors _ _ _ ?_ ?_ ?_ L ξ hs
  · intro v
    filter_upwards [hl v] with j hj
    simp only [initialSampler, hj.1, hj.2]
  · exact Eventually.of_forall (fun _ => rfl)
  · exact Eventually.of_forall (fun _ => rfl)

end
end FiniteAvalanches.Wilson.Lattice
