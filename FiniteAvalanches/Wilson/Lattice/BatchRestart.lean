import FiniteAvalanches.Wilson.Lattice.Law
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.BatchRestart
open LatticeProb
open scoped Classical
noncomputable section

private theorem mem_erase_fold (vs acc : List (Site 2)) (v : Site 2)
    (hv : v ∈ vs.foldl eraseStep acc) : v ∈ acc ∨ v ∈ vs := by
  induction vs generalizing acc with
  | nil => exact Or.inl hv
  | cons x xs ih =>
    rcases ih (eraseStep acc x) hv with h | h
    · simp only [eraseStep, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact Or.inl (List.takeWhile_subset _ h)
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
    · exact Or.inr (List.mem_cons.mpr (Or.inr h))

/-- Every retained vertex was actually visited by the complete stopped word. -/
theorem walkErase_mem_visited (x : Site 2) (w : WalkDriver) (T : ℕ) (v : Site 2)
    (hv : v ∈ walkErase x w T) : ∃ n ≤ T, position x w n = v := by
  have he : walkErase x w T =
      ((List.range (T + 1)).map (position x w)).foldl eraseStep [] := List.foldl_map.symm
  rw [he] at hv
  rcases mem_erase_fold _ [] v hv with h | h
  · cases h
  · obtain ⟨n, hn, he⟩ := List.mem_map.mp h
    exact ⟨n, by have := List.mem_range.mp hn; omega, he⟩

/-- The last erasure step keeps the real hit vertex as its last vertex. -/
theorem walkErase_succ (x : Site 2) (w : WalkDriver) (T : ℕ) :
    walkErase x w (T + 1) = eraseStep (walkErase x w T) (position x w (T + 1)) := by
  simp only [walkErase, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- No previously colored vertex belongs to the newly colored branch. -/
theorem covered_not_mem_retained_branch (st : SamplerState) (x : Site 2)
    (w : WalkDriver) (T : ℕ) (hT : hitTime st.covered x w = some T)
    (v : Site 2) (hv : v ∈ st.covered) : v ∉ (walkErase x w T).dropLast := by
  cases T with
  | zero => simp [walkErase, eraseStep]
  | succ T =>
    rw [walkErase_succ, eraseStep, List.dropLast_concat]
    intro hmem
    have hvisited := walkErase_mem_visited x w T v (List.takeWhile_subset _ hmem)
    obtain ⟨n, hn, he⟩ := hvisited
    exact ((hitTime_eq_some_iff _ _ _ _).mp hT).2 n (by omega) (he.symm ▸ hv)

/-- Full stopped history is retained, while every existing root color stays fixed. -/
theorem samplerStep_preserves_covered_colors (st out : SamplerState) (x : Site 2)
    (w : WalkDriver) (hs : samplerStep st x w = some out)
    (v : Site 2) (hv : v ∈ st.covered) : out.colors v = st.colors v := by
  by_cases hx : x ∈ st.covered
  · have he : st = out := Option.some.inj (by simpa [samplerStep, hx] using hs)
    subst out
    rfl
  · cases hT : hitTime st.covered x w with
    | none => simp [samplerStep, hx, hT] at hs
    | some T =>
      have hb := covered_not_mem_retained_branch st x w T hT v hv
      have he := Option.some.inj (by simpa only [samplerStep, if_neg hx, hT] using hs)
      rw [← he]
      exact if_neg hb

/-- Successful finite batches preserve every original colored vertex. -/
theorem samplerRun_preserves_covered_colors (st out : SamplerState)
    (L : List (Site 2)) (ξ : ℕ → WalkDriver) (hs : samplerRun st L ξ = some out)
    (v : Site 2) (hv : v ∈ st.covered) : out.colors v = st.colors v := by
  induction L generalizing st ξ with
  | nil => exact congrArg (fun q : SamplerState => q.colors v) (Option.some.inj hs).symm
  | cons x xs ih =>
    cases hh : samplerStep st x (ξ 0) with
    | none => simp [samplerRun, hh] at hs
    | some mid =>
      have hm : mid.colors v = st.colors v := samplerStep_preserves_covered_colors st mid x (ξ 0) hh v hv
      have hv' : v ∈ mid.covered := by
        change mid.colors v ≠ none
        rw [hm]
        exact hv
      have ht : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hh, Option.bind_some] using hs
      exact (ih mid (fun i => ξ (i + 1)) ht hv').trans hm

/-- Actual successful state colors give the enlarged roots; full history is NOT roots. -/
def restartedRoots (R : RootPair) (L : List (Site 2)) (ξ : ℕ → WalkDriver)
    (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ = some out) : RootPair where
  zero := {v | out.colors v = some false}
  one := {v | out.colors v = some true}
  disjoint := Set.disjoint_left.mpr (by
    intro v hv hw
    have h0 : out.colors v = some false := hv
    have h1 : out.colors v = some true := hw
    rw [h0] at h1
    cases h1)
  zero_nonempty := by
    obtain ⟨v, hv⟩ := R.zero_nonempty
    have hc : (initialSampler R).colors v = some false := by simp [initialSampler, hv]
    refine ⟨v, ?_⟩
    exact (samplerRun_preserves_covered_colors _ out L ξ hs v (by
      change (initialSampler R).colors v ≠ none; simp [hc])).trans hc
  one_nonempty := by
    obtain ⟨v, hv⟩ := R.one_nonempty
    have hz : v ∉ R.zero := fun h => Set.disjoint_left.mp R.disjoint h hv
    have hc : (initialSampler R).colors v = some true := by simp [initialSampler, hv, hz]
    refine ⟨v, ?_⟩
    exact (samplerRun_preserves_covered_colors _ out L ξ hs v (by
      change (initialSampler R).colors v ≠ none; simp [hc])).trans hc

/-- Unknown colors remain unknown; only the two actual retained colors become roots. -/
theorem initial_restarted_colors (R : RootPair) (L : List (Site 2)) (ξ : ℕ → WalkDriver)
    (out : SamplerState) (hs : samplerRun (initialSampler R) L ξ = some out) :
    (initialSampler (restartedRoots R L ξ out hs)).colors = out.colors := by
  funext v
  cases hv : out.colors v with
  | none => simp [initialSampler, restartedRoots, hv]
  | some b => cases b <;> simp [initialSampler, restartedRoots, hv]

/-- The original batch semantics use exactly one driver row per list slot. -/
theorem samplerRun_append (st : SamplerState) (L Q : List (Site 2)) (ξ : ℕ → WalkDriver) :
    samplerRun st (L ++ Q) ξ = (samplerRun st L ξ).bind
      (fun out => samplerRun out Q (fun i => ξ (i + L.length))) := by
  induction L generalizing st ξ with
  | nil => simp [samplerRun]
  | cons x xs ih =>
    cases hh : samplerStep st x (ξ 0) with
    | none => simp [samplerRun, hh]
    | some mid =>
      simpa only [List.cons_append, samplerRun, hh, Option.bind_some,
        List.length_cons, Nat.add_assoc] using ih mid (fun i => ξ (i + 1))

/-- Colors of a single actual step depend only on the initial colors and fresh walk. -/
theorem samplerStep_map_colors_eq (st st' : SamplerState) (x : Site 2) (w : WalkDriver)
    (hc : st.colors = st'.colors) :
    (samplerStep st x w).map SamplerState.colors =
      (samplerStep st' x w).map SamplerState.colors := by
  have hcov : st.covered = st'.covered := by ext v; simp [SamplerState.covered, hc]
  by_cases hx : x ∈ st.covered
  · have hx' : x ∈ st'.covered := hcov ▸ hx
    simp [samplerStep, hx, hx', hc]
  · have hx' : x ∉ st'.covered := hcov ▸ hx
    simp only [samplerStep, hcov, if_neg hx']
    cases hT : hitTime st'.covered x w <;> simp [hc]

/-- Complete successful/failing continuations have the same full partial color field. -/
theorem samplerRun_map_colors_eq (st st' : SamplerState) (L : List (Site 2))
    (ξ : ℕ → WalkDriver) (hc : st.colors = st'.colors) :
    (samplerRun st L ξ).map SamplerState.colors =
      (samplerRun st' L ξ).map SamplerState.colors := by
  induction L generalizing st st' ξ with
  | nil => simp [samplerRun, hc]
  | cons x xs ih =>
    have hm := samplerStep_map_colors_eq st st' x (ξ 0) hc
    cases hs : samplerStep st x (ξ 0) <;> cases hs' : samplerStep st' x (ξ 0)
    · simp [samplerRun, hs, hs']
    · simp [hs, hs'] at hm
    · simp [hs, hs'] at hm
    · simp only [samplerRun, hs, hs', Option.bind_some]
      exact ih _ _ (fun i => ξ (i + 1)) (Option.some.inj (by simpa only [hs, hs', Option.map_some] using hm))

/-- Deterministic restart used by the source exploration, with no probability estimate assumed. -/
theorem continuation_colors_restart (R : RootPair) (L Q : List (Site 2))
    (ξ η : ℕ → WalkDriver) (out : SamplerState)
    (hs : samplerRun (initialSampler R) L ξ = some out) :
    (samplerRun out Q η).map SamplerState.colors =
      (samplerRun (initialSampler (restartedRoots R L ξ out hs)) Q η).map SamplerState.colors :=
  samplerRun_map_colors_eq out _ Q η (initial_restarted_colors R L ξ out hs).symm


/-- Complete color-pattern events agree for two states with the same partial colors. -/
theorem continuation_pattern_event_eq (st st' : SamplerState) (Q : List (Site 2))
    (D : Finset (Site 2)) (pc : Site 2 → Bool) (hc : st.colors = st'.colors) :
    {η | ∃ out, samplerRun st Q η = some out ∧ ∀ d ∈ D, out.colors d = some (pc d)} =
      {η | ∃ out, samplerRun st' Q η = some out ∧ ∀ d ∈ D, out.colors d = some (pc d)} := by
  ext η
  have hm := samplerRun_map_colors_eq st st' Q η hc
  constructor
  · rintro ⟨out, hout, hp⟩
    cases hs' : samplerRun st' Q η with
    | none => simp [hout, hs'] at hm
    | some out' =>
      have he : out.colors = out'.colors := Option.some.inj
        (by simpa only [hout, hs', Option.map_some] using hm)
      exact ⟨out', hs', fun d hd => by rw [← he]; exact hp d hd⟩
  · rintro ⟨out', hout', hp⟩
    cases hs : samplerRun st Q η with
    | none => simp [hs, hout'] at hm
    | some out =>
      have he : out.colors = out'.colors := Option.some.inj
        (by simpa only [hs, hout', Option.map_some] using hm)
      exact ⟨out, hs, fun d hd => by rw [he]; exact hp d hd⟩

/-- The actual fresh-driver continuation has the genuine enlarged-root color law.
The preceding history is fixed here; no conditional-probability estimate is assumed. -/
theorem fresh_continuation_color_pattern_law (R : RootPair) (L Q : List (Site 2))
    (ξ : ℕ → WalkDriver) (out : SamplerState)
    (hs : samplerRun (initialSampler R) L ξ = some out)
    (D : Finset (Site 2)) (pc : Site 2 → Bool) (hD : ∀ d ∈ D, d ∈ Q) :
    wilsonColorLaw (restartedRoots R L ξ out hs) {σ | ∀ d ∈ D, σ d = pc d} =
      wilsonRows {η | ∃ next, samplerRun out Q η = some next ∧
        ∀ d ∈ D, next.colors d = some (pc d)} := by
  rw [wilsonColorLaw_apply_sampler _ Q D pc hD]
  rw [continuation_pattern_event_eq _ out Q D pc
    (initial_restarted_colors R L ξ out hs)]

#print axioms fresh_continuation_color_pattern_law

#print axioms continuation_colors_restart
#print axioms samplerRun_append
end
end FiniteAvalanches.Wilson.Lattice.BatchRestart
