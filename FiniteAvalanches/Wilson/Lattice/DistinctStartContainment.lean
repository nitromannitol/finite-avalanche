import FiniteAvalanches.Wilson.Lattice.StoppedHistoryContainment
import FiniteAvalanches.Wilson.Lattice.ColorMarginal

/-! Actual recorded walks arise only at the first query of their start. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.DistinctStartContainment
open LatticeProb FiniteAvalanches BeurlingConnected BatchRestart
open StoppedHistoryLocalization
open scoped Classical
noncomputable section

/-- A successful query colors its start, even when it was already colored. -/
theorem samplerStep_start_covered (st out : SamplerState) (x : Site 2)
    (w : WalkDriver) (hs : samplerStep st x w = some out) : x ∈ out.covered := by
  by_cases hx : x ∈ st.covered
  · change out.colors x ≠ none
    rw [samplerStep_preserves_covered_colors st out x w hs x hx]
    exact hx
  · cases hT : hitTime st.covered x w with
    | none => simp only [samplerStep, if_neg hx, hT] at hs; cases hs
    | some T =>
      have hhit := ((hitTime_eq_some_iff _ _ _ _).mp hT).1
      have hne : x ≠ position x w T := fun he => hx (he ▸ hhit)
      have hb := walkErase_start_mem_dropLast x w T hne
      have he := Option.some.inj (by
        simpa only [samplerStep, if_neg hx, hT] using hs)
      rw [← he]
      change (if x ∈ (walkErase x w T).dropLast then
        st.colors (position x w T) else st.colors x) ≠ none
      rw [if_pos hb]
      exact hhit

/-- Any new recorded escape uses the deterministic first occurrence row of a
start that was uncolored before the batch. Every terminal position is retained. -/
theorem samplerRun_history_exit_first (K : Set (Site 2)) (st out : SamplerState)
    (L : List (Site 2)) (ξ : ℕ → WalkDriver) (h : ℕ) (hK : K ⊆ st.covered)
    (hs : samplerRun st L ξ = some out)
    (hex : ∃ p ∈ out.history, ∃ j : Fin (p.length + 1), h < siteRadius 0 (p.vertex j)) :
    (∃ p ∈ st.history, ∃ j : Fin (p.length + 1), h < siteRadius 0 (p.vertex j)) ∨
    ∃ x ∈ L, x ∉ st.covered ∧ ∃ t : ℕ,
      h < siteRadius 0 (position x (ξ (L.idxOf x)) t) ∧
      (t : WithTop ℕ) ≤ firstHit K (position x (ξ (L.idxOf x))) := by
  induction L generalizing st ξ with
  | nil =>
    have he : st = out := Option.some.inj hs
    exact Or.inl (he ▸ hex)
  | cons x xs ih =>
    cases hstep : samplerStep st x (ξ 0) with
    | none => simp only [samplerRun, hstep, Option.bind_none] at hs; cases hs
    | some mid =>
      have hpersist (v : Site 2) (hv : v ∈ st.covered) : v ∈ mid.covered := by
        change mid.colors v ≠ none
        rw [samplerStep_preserves_covered_colors st mid x (ξ 0) hstep v hv]
        exact hv
      have htail : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hstep, Option.bind_some] using hs
      rcases ih mid (fun i => ξ (i + 1)) (fun v hv => hpersist v (hK hv)) htail with hold | hrow
      · by_cases hx : x ∈ st.covered
        · have he : st = mid := Option.some.inj (by
            simpa only [samplerStep, if_pos hx] using hstep)
          exact Or.inl (he ▸ hold)
        · rcases samplerStep_history_exit K st mid x (ξ 0) h hK hstep hold with hold | hrow
          · exact Or.inl hold
          · refine Or.inr ⟨x, List.mem_cons_self, hx, ?_⟩
            simpa only [List.idxOf_cons_self] using hrow
      · obtain ⟨y, hy, hfresh, t, ht, hav⟩ := hrow
        have hyx : x ≠ y := by
          intro he
          subst y
          exact hfresh (samplerStep_start_covered st mid x (ξ 0) hstep)
        refine Or.inr ⟨y, List.mem_cons_of_mem x hy, fun hv => hfresh (hpersist y hv), t, ?_, ?_⟩
        · simpa only [List.idxOf_cons, beq_iff_eq, cond_eq_ite, if_neg hyx] using ht
        · simpa only [List.idxOf_cons, beq_iff_eq, cond_eq_ite, if_neg hyx] using hav

/-- Union only over distinct starts, with their original fixed first-index rows. -/
theorem actual_history_exit_subset_distinct (K : Set (Site 2)) (R : RootPair)
    (L : List (Site 2)) (h : ℕ) (hKR : K ⊆ R.zero) :
    {ξ : ℕ → WalkDriver | ∃ out, samplerRun (initialSampler R) L ξ = some out ∧
      ∃ p ∈ out.history, ∃ j : Fin (p.length + 1), h < siteRadius 0 (p.vertex j)} ⊆
    ⋃ x : {x // x ∈ L.toFinset}, {ξ : ℕ → WalkDriver | ∃ t : ℕ,
      h < siteRadius 0 (position x.val (ξ (L.idxOf x.val)) t) ∧
      (t : WithTop ℕ) ≤ firstHit K (position x.val (ξ (L.idxOf x.val)))} := by
  rintro ξ ⟨out, hs, hex⟩
  have hK : K ⊆ (initialSampler R).covered := by
    intro v hv
    rw [initialSampler_covered]
    exact Or.inl (hKR hv)
  rcases samplerRun_history_exit_first K (initialSampler R) out L ξ h hK hs hex with hold | hrow
  · obtain ⟨p, hp, _⟩ := hold
    exact (List.not_mem_nil hp).elim
  · obtain ⟨x, hx, _, ht⟩ := hrow
    exact Set.mem_iUnion.mpr ⟨⟨x, List.mem_toFinset.mpr hx⟩, ht⟩

end
end FiniteAvalanches.Wilson.Lattice.DistinctStartContainment
