import FiniteAvalanches.Wilson.Lattice.RestartGeometry
import FiniteAvalanches.Wilson.Lattice.LocalizationUnion

/-! Deterministic retained-root geometry for a genuinely completed, confined
Wilson prefix. Complete stopped histories include both endpoints. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CurrentConfinedRestart
open LatticeProb FiniteAvalanches BatchRestart ConditionalIteration7
open scoped Classical
noncomputable section

/-- A site outside the retained branch keeps its actual previous partial color. -/
theorem samplerStep_color_eq_of_not_retained (st out : SamplerState)
    (x v : Site 2) (w : WalkDriver) (T : ℕ)
    (hs : samplerStep st x w = some out)
    (hT : hitTime st.covered x w = some T)
    (hv : v ∉ (walkErase x w T).dropLast) : out.colors v = st.colors v := by
  by_cases hx : x ∈ st.covered
  · have he : st = out := Option.some.inj (by
      simpa only [samplerStep, if_pos hx] using hs)
    exact he ▸ rfl
  · have he := Option.some.inj (by
      simpa only [samplerStep, if_neg hx, hT] using hs)
    rw [← he]
    exact if_neg hv

/-- Every newly colored site is retained and was visited by the original driver
strictly before its genuine first hit. The recorded walk still includes that hit. -/
theorem samplerStep_new_color_visited (st out : SamplerState) (x v : Site 2)
    (w : WalkDriver) (c : Bool) (hs : samplerStep st x w = some out)
    (hnew : st.colors v = none) (hc : out.colors v = some c) :
    ∃ T : ℕ, hitTime st.covered x w = some T ∧
      v ∈ (walkErase x w T).dropLast ∧ dirWalkFinite x w T ∈ out.history ∧
      ∃ n : ℕ, n < T ∧ position x w n = v := by
  by_cases hx : x ∈ st.covered
  · have he : st = out := Option.some.inj (by
      simpa only [samplerStep, if_pos hx] using hs)
    rw [← he, hnew] at hc
    cases hc
  · cases hT : hitTime st.covered x w with
    | none => simp only [samplerStep, if_neg hx, hT] at hs; cases hs
    | some T =>
      have he := Option.some.inj (by
        simpa only [samplerStep, if_neg hx, hT] using hs)
      have hv : v ∈ (walkErase x w T).dropLast := by
        by_contra hv
        rw [samplerStep_color_eq_of_not_retained st out x v w T hs hT hv, hnew] at hc
        cases hc
      obtain ⟨n, hn, hnv⟩ := walkErase_mem_visited x w T v (List.mem_of_mem_dropLast hv)
      have hne : n ≠ T := by
        intro heq
        have hh : position x w T ∈ st.covered := (hitTime_eq_some_iff _ _ _ _).mp hT |>.1
        rw [← heq, hnv] at hh
        exact hh hnew
      refine ⟨T, rfl, hv, ?_, n, by omega, hnv⟩
      rw [← he]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- The actual successful output and the complement of the actual escape event
supply confinement at every full-history index, including the terminal. -/
theorem full_history_confined_of_not_prefixExit (R : RootPair) (L : List (Site 2))
    (ξ : Rows) (out : SamplerState)
    (hs : samplerRun (initialSampler R) L ξ = some out) (h : ℕ)
    (hgood : ξ ∉ ActualLocalizationUnion.prefixExit R L h) :
    ∀ p ∈ out.history, ∀ t : Fin (p.length + 1), siteRadius 0 (p.vertex t) ≤ h := by
  intro p hp t
  by_contra ht
  exact hgood ⟨out, hs, p, hp, t, Nat.lt_of_not_ge ht⟩

/-- The two actual enlarged root sets preserve original colors; every added zero
root lies in the box confining the genuinely recorded full stopped histories. -/
theorem restarted_roots_of_confined_history (R : RootPair) (L : List (Site 2))
    (ξ : Rows) (out : SamplerState)
    (hs : samplerRun (initialSampler R) L ξ = some out) (h : ℕ)
    (hc : ∀ p ∈ out.history, ∀ t : Fin (p.length + 1), siteRadius 0 (p.vertex t) ≤ h) :
    R.zero ⊆ (restartedRoots R L ξ out hs).zero ∧
      (restartedRoots R L ξ out hs).zero ⊆ R.zero ∪ {v | siteRadius 0 v ≤ h} ∧
      R.one ⊆ (restartedRoots R L ξ out hs).one := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have h0 : (initialSampler R).colors v = some false := if_pos hv
    exact (samplerRun_preserves_covered_colors _ out L ξ hs v (by
      change (initialSampler R).colors v ≠ none
      rw [h0]
      exact Option.some_ne_none _)).trans h0
  · intro v hv
    rcases ActualRestartGeometry.samplerRun_colors_eq_or_visited
        (initialSampler R) out L ξ hs v with hsame | hvisit
    · apply Or.inl
      have h0 : out.colors v = some false := hv
      rw [hsame] at h0
      by_contra hz
      by_cases ho : v ∈ R.one
      · simp only [initialSampler, if_neg hz, if_pos ho] at h0; cases h0
      · simp only [initialSampler, if_neg hz, if_neg ho] at h0; cases h0
    · obtain ⟨p, hp, t, ht⟩ := hvisit
      exact Or.inr (ht ▸ hc p hp t)
  · intro v hv
    have hz : v ∉ R.zero := fun h0 => Set.disjoint_left.mp R.disjoint h0 hv
    have h1 : (initialSampler R).colors v = some true := by
      simp only [initialSampler, if_neg hz, if_pos hv]
    exact (samplerRun_preserves_covered_colors _ out L ξ hs v (by
      change (initialSampler R).colors v ≠ none
      rw [h1]
      exact Option.some_ne_none _)).trans h1

/-- The source good event produces all deterministic enlarged-root inclusions. -/
theorem restarted_roots_of_not_prefixExit (R : RootPair) (L : List (Site 2))
    (ξ : Rows) (out : SamplerState)
    (hs : samplerRun (initialSampler R) L ξ = some out) (h : ℕ)
    (hgood : ξ ∉ ActualLocalizationUnion.prefixExit R L h) :
    R.zero ⊆ (restartedRoots R L ξ out hs).zero ∧
      (restartedRoots R L ξ out hs).zero ⊆ R.zero ∪ {v | siteRadius 0 v ≤ h} ∧
      R.one ⊆ (restartedRoots R L ξ out hs).one :=
  restarted_roots_of_confined_history R L ξ out hs h
    (full_history_confined_of_not_prefixExit R L ξ out hs h hgood)

end
end FiniteAvalanches.Wilson.Lattice.CurrentConfinedRestart

#print FiniteAvalanches.Wilson.Lattice.CurrentConfinedRestart.restarted_roots_of_confined_history
#print FiniteAvalanches.Wilson.Lattice.CurrentConfinedRestart.restarted_roots_of_not_prefixExit
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentConfinedRestart.samplerStep_color_eq_of_not_retained
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentConfinedRestart.samplerStep_new_color_visited
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentConfinedRestart.full_history_confined_of_not_prefixExit
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentConfinedRestart.restarted_roots_of_confined_history
#print axioms FiniteAvalanches.Wilson.Lattice.CurrentConfinedRestart.restarted_roots_of_not_prefixExit
