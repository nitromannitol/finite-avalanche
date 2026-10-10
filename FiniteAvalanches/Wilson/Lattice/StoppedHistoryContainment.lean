import FiniteAvalanches.Wilson.Lattice.BatchRestart
import FiniteAvalanches.Wilson.Lattice.BeurlingLocalization

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.StoppedHistoryLocalization
open LatticeProb MeasureTheory FiniteAvalanches.BeurlingConnected BatchRestart
open scoped Classical
noncomputable section

/-- A successful step retains the old history or records its complete stopped row,
including the terminal root. The fixed obstacle remains avoided before that time. -/
theorem samplerStep_history_exit (K : Set (Site 2)) (st out : SamplerState)
    (x : Site 2) (w : WalkDriver) (h : ℕ) (hK : K ⊆ st.covered)
    (hs : samplerStep st x w = some out)
    (hex : ∃ p ∈ out.history, ∃ j : Fin (p.length + 1),
      h < FiniteAvalanches.siteRadius 0 (p.vertex j)) :
    (∃ p ∈ st.history, ∃ j : Fin (p.length + 1),
      h < FiniteAvalanches.siteRadius 0 (p.vertex j)) ∨
    ∃ t : ℕ, h < FiniteAvalanches.siteRadius 0 (position x w t) ∧
      (t : WithTop ℕ) ≤ firstHit K (position x w) := by
  by_cases hx : x ∈ st.covered
  · have he : st = out := Option.some.inj (by
      simpa only [samplerStep, if_pos hx] using hs)
    exact Or.inl (he ▸ hex)
  · cases hT : hitTime st.covered x w with
    | none => simp only [samplerStep, if_neg hx, hT] at hs; cases hs
    | some T =>
      have he := Option.some.inj (by
        simpa only [samplerStep, if_neg hx, hT] using hs)
      rw [← he] at hex
      obtain ⟨p, hp, j, hj⟩ := hex
      change p ∈ st.history ++ [dirWalkFinite x w T] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact Or.inl ⟨p, hp, j, hj⟩
      · have hp' : p = dirWalkFinite x w T := List.mem_singleton.mp hp
        subst p
        refine Or.inr ⟨j.val, hj, ?_⟩
        apply (prefix_avoidance_iff K (position x w) j.val).mp
        intro s hs'
        have hsj : s < T := by
          have hle : j.val < T + 1 := j.isLt
          omega
        exact fun hk => ((hitTime_eq_some_iff _ _ _ _).mp hT).2 s hsj (hK hk)

/-- Every escape in an actual successful batch comes from its old history or a
fixed-obstacle stopped exit of the actual row at an actual start-list slot. -/
theorem samplerRun_history_exit (K : Set (Site 2)) (st out : SamplerState)
    (L : List (Site 2)) (ξ : ℕ → WalkDriver) (h : ℕ) (hK : K ⊆ st.covered)
    (hs : samplerRun st L ξ = some out)
    (hex : ∃ p ∈ out.history, ∃ j : Fin (p.length + 1),
      h < FiniteAvalanches.siteRadius 0 (p.vertex j)) :
    (∃ p ∈ st.history, ∃ j : Fin (p.length + 1),
      h < FiniteAvalanches.siteRadius 0 (p.vertex j)) ∨
    ∃ i : Fin L.length, ∃ t : ℕ,
      h < FiniteAvalanches.siteRadius 0 (position (L.get i) (ξ i.val) t) ∧
      (t : WithTop ℕ) ≤ firstHit K (position (L.get i) (ξ i.val)) := by
  induction L generalizing st ξ with
  | nil =>
    have he : st = out := Option.some.inj hs
    exact Or.inl (he ▸ hex)
  | cons x xs ih =>
    cases hstep : samplerStep st x (ξ 0) with
    | none => simp only [samplerRun, hstep, Option.bind_none] at hs; cases hs
    | some mid =>
      have hKmid : K ⊆ mid.covered := by
        intro v hv
        change mid.colors v ≠ none
        rw [samplerStep_preserves_covered_colors st mid x (ξ 0) hstep v (hK hv)]
        exact hK hv
      have htail : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hstep, Option.bind_some] using hs
      rcases ih mid (fun i => ξ (i + 1)) hKmid htail with hold | hrow
      · rcases samplerStep_history_exit K st mid x (ξ 0) h hK hstep hold with
          hold | hrow
        · exact Or.inl hold
        · refine Or.inr ⟨⟨0, by simp only [List.length_cons]; omega⟩, ?_⟩
          exact hrow
      · obtain ⟨i, t, ht, hav⟩ := hrow
        refine Or.inr ⟨⟨i.val + 1, by simp only [List.length_cons]; omega⟩, t, ?_, ?_⟩
        · simpa only [List.get_cons_succ] using ht
        · simpa only [List.get_cons_succ] using hav

/-- Literal actual successful-history exits are contained in a finite union of
actual fixed-obstacle stopped-row exits. Initial roots and their preservation
are derived from the sampler, rather than supplied as step estimates. -/
theorem actual_history_exit_subset (K : Set (Site 2)) (R : RootPair)
    (L : List (Site 2)) (h : ℕ) (hKR : K ⊆ R.zero) :
    {ξ : ℕ → WalkDriver | ∃ out, samplerRun (initialSampler R) L ξ = some out ∧
      ∃ p ∈ out.history, ∃ j : Fin (p.length + 1),
        h < FiniteAvalanches.siteRadius 0 (p.vertex j)} ⊆
    ⋃ i : Fin L.length, {ξ : ℕ → WalkDriver | ∃ t : ℕ,
      h < FiniteAvalanches.siteRadius 0 (position (L.get i) (ξ i.val) t) ∧
      (t : WithTop ℕ) ≤ firstHit K (position (L.get i) (ξ i.val))} := by
  rintro ξ ⟨out, hs, hex⟩
  have hK : K ⊆ (initialSampler R).covered := by
    intro v hv
    change (initialSampler R).colors v ≠ none
    simp only [initialSampler, if_pos (hKR hv), ne_eq, Option.some_ne_none, not_false_eq_true]
  rcases samplerRun_history_exit K (initialSampler R) out L ξ h hK hs hex with
      hold | hrow
  · obtain ⟨p, hp, _⟩ := hold
    exact (List.not_mem_nil hp).elim
  · obtain ⟨i, hi⟩ := hrow
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

end
end FiniteAvalanches.Wilson.Lattice.StoppedHistoryLocalization
