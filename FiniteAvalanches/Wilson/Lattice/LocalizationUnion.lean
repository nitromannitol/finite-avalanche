import FiniteAvalanches.Wilson.Lattice.QueryPrefixes

/-! The finite union of actual terminal-inclusive localization errors. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ActualLocalizationUnion
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualContactHistory ActualQueryPrefixes
open scoped Classical
noncomputable section

/-- The source's complete stopped-prefix escape event, including terminal hits. -/
def prefixExit (R : RootPair) (L : List (Site 2)) (h : ℕ) : Set Rows :=
  {ξ | ∃ out, samplerRun (initialSampler R) L ξ = some out ∧
    ∃ p ∈ out.history, ∃ j : Fin (p.length + 1), h < siteRadius 0 (p.vertex j)}

theorem measurable_prefixExit (R : RootPair) (L : List (Site 2)) (h : ℕ) :
    MeasurableSet (prefixExit R L h) :=
  fullHistory_le R L _ (measurable_completed_observation R L _)

/-- All actual contact failures lie in the localized iteration event or in one
of the genuine stopped-prefix escape events, apart from proved null nontermination. -/
theorem actual_failures_le_surviving_add_exits (R : RootPair)
    (Q : ℕ → List (Site 2)) (F : ℕ → Finset (Site 2)) (h : ℕ → ℕ) (t : ℝ) (n : ℕ) :
    wilsonRows.real {ξ : Rows | ∀ i < n,
      ξ ∉ continuationContactEvent (initialSampler R) (queryPrefix Q (i + 1)) (F i) t} ≤
      wilsonRows.real (survivingPrefixes R Q F h t n) +
        ∑ i : Fin n, wilsonRows.real (prefixExit R (queryPrefix Q i.val) (h i.val)) := by
  let A := {ξ : Rows | ∀ i < n,
    ξ ∉ continuationContactEvent (initialSampler R) (queryPrefix Q (i + 1)) (F i) t}
  let B := survivingPrefixes R Q F h t n
  let E := fun i : Fin n => prefixExit R (queryPrefix Q i.val) (h i.val)
  have hs : ∀ᵐ ξ ∂wilsonRows, ∀ i : Fin n,
      ∃ out, samplerRun (initialSampler R) (queryPrefix Q i.val) ξ = some out :=
    ae_all_iff.mpr (fun i => wilson_sampler_success_conull R (queryPrefix Q i.val))
  have hsub : ∀ᵐ ξ ∂wilsonRows, ξ ∈ A → ξ ∈ B ∪ ⋃ i : Fin n, E i := by
    filter_upwards [hs] with ξ hξ ha
    by_cases hb : ξ ∈ B
    · exact Or.inl hb
    · apply Or.inr
      by_contra he
      apply hb
      apply (mem_survivingPrefixes_iff R Q F h t n ξ).mpr
      intro i hi
      refine ⟨?_, ha i hi⟩
      obtain ⟨out, hout⟩ := hξ ⟨i, hi⟩
      refine ⟨out, hout, ?_⟩
      intro p hp j
      by_contra hj
      apply he
      refine Set.mem_iUnion.mpr ⟨⟨i, hi⟩, out, hout, p, hp, j, ?_⟩
      exact Nat.lt_of_not_ge (fun hr => hj ((site_radius_zero_le_iff _ _).mp hr))
  calc
    _ ≤ wilsonRows.real (B ∪ ⋃ i : Fin n, E i) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ wilsonRows.real B + wilsonRows.real (⋃ i : Fin n, E i) := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (measureReal_iUnion_fintype_le (μ := wilsonRows) E)

end
end FiniteAvalanches.Wilson.Lattice.ActualLocalizationUnion
