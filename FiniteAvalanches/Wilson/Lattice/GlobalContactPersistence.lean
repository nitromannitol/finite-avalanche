import FiniteAvalanches.Wilson.Lattice.GlobalContactObservation
import FiniteAvalanches.Wilson.Lattice.QueryPrefixes

/-! Whole-set low contact observations force every earlier local observation to fail. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.GlobalContactPersistence
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualContactHistory ActualQueryPrefixes
open GlobalContactObservation
open scoped Classical
noncomputable section

theorem contactSites_mono {F K : Finset (Site 2)} (hFK : F ⊆ K) :
    contactSites F ⊆ contactSites K := by
  intro d hd
  obtain ⟨x, hx, hd⟩ := Finset.mem_biUnion.mp hd
  exact Finset.mem_biUnion.mpr ⟨x, hFK hx, hd⟩

theorem contacts_le_contacts_of_subset {F K : Finset (Site 2)}
    (hFK : F ⊆ K) (σ : ColorField) : contacts F σ ≤ contacts K σ :=
  Finset.sum_le_sum_of_subset hFK

theorem queryPrefix_exists_suffix (Q : ℕ → List (Site 2)) {i n : ℕ} (hin : i ≤ n) :
    ∃ T, queryPrefix Q n = queryPrefix Q i ++ T := by
  induction n generalizing i with
  | zero =>
    have hi : i = 0 := Nat.eq_zero_of_le_zero hin
    subst i
    exact ⟨[], rfl⟩
  | succ n ih =>
    by_cases hi : i = n + 1
    · subst i
      exact ⟨[], (List.append_nil _).symm⟩
    · obtain ⟨T, hT⟩ := ih (show i ≤ n by omega)
      refine ⟨T ++ Q n, ?_⟩
      rw [queryPrefix, hT, List.append_assoc]

/-- A successful extension retains every genuinely known prefix color. -/
theorem samplerRun_prefix_known_colors (st out : SamplerState)
    (L T : List (Site 2)) (ξ : Rows) (hs : samplerRun st (L ++ T) ξ = some out) :
    ∃ mid, samplerRun st L ξ = some mid ∧
      ∀ (v : Site 2) (b : Bool), mid.colors v = some b → out.colors v = some b := by
  rw [samplerRun_append] at hs
  cases hm : samplerRun st L ξ with
  | none => simp only [hm, Option.bind_none] at hs; cases hs
  | some mid =>
    have ht : samplerRun mid T (fun j => ξ (j + L.length)) = some out := by
      simpa only [hm, Option.bind_some] using hs
    refine ⟨mid, rfl, ?_⟩
    intro v b hv
    have hcov : v ∈ mid.covered := by
      change mid.colors v ≠ none
      rw [hv]
      exact Option.some_ne_none b
    exact (samplerRun_preserves_covered_colors mid out T _ ht v hcov).trans hv

/-- The global count uses every original incidence; its low observed pattern
cannot coexist with a successful earlier local contact pattern. -/
theorem low_observation_subset_all_failures (R : RootPair)
    (K : Finset (Site 2)) (Q : ℕ → List (Site 2)) (F : ℕ → Finset (Site 2))
    (n : ℕ) (t : ℝ) (hF : ∀ i < n, F i ⊆ K) :
    lowContactObservation (initialSampler R)
      (queryPrefix Q n ++ (contactSites K).toList) K t ⊆
      {ξ : Rows | ∀ i < n,
        ξ ∉ continuationContactEvent (initialSampler R) (queryPrefix Q (i + 1)) (F i) t} := by
  rintro ξ ⟨out, hs, σ, hσ, hc⟩ i hi ⟨next, hn, τ, hτ, ht⟩
  obtain ⟨T, hT⟩ := queryPrefix_exists_suffix Q (show i + 1 ≤ n by omega)
  have hs' : samplerRun (initialSampler R)
      (queryPrefix Q (i + 1) ++ (T ++ (contactSites K).toList)) ξ = some out := by
    rw [← List.append_assoc, ← hT]
    exact hs
  obtain ⟨mid, hm, hpersist⟩ := samplerRun_prefix_known_colors _ out _ _ ξ hs'
  have he : mid = next := Option.some.inj (hm.symm.trans hn)
  subst mid
  have hagree : ∀ d ∈ contactSites (F i), τ d = σ d := by
    intro d hd
    exact Option.some.inj ((hpersist d (τ d) (ht d hd)).symm.trans
      (hc d (contactSites_mono (hF i hi) hd)))
  have hcount : contacts (F i) τ ≤ contacts K σ := by
    rw [contacts_of_agree (F i) hagree]
    exact contacts_le_contacts_of_subset (hF i hi) σ
  exact (not_le_of_gt hσ) (hτ.trans (by exact_mod_cast hcount))

/-- Exact source-law mass transfers to simultaneous actual local failures.
Termination is a consequence of the registered finite-pattern Wilson law. -/
theorem global_low_mass_le_all_failures (R : RootPair) (K : Finset (Site 2))
    (Q : ℕ → List (Site 2)) (F : ℕ → Finset (Site 2)) (n : ℕ) (t : ℝ)
    (hF : ∀ i < n, F i ⊆ K) :
    (wilsonColorLaw R).real {σ : ColorField | (contacts K σ : ℝ) < t} ≤
      wilsonRows.real {ξ : Rows | ∀ i < n,
        ξ ∉ continuationContactEvent (initialSampler R) (queryPrefix Q (i + 1)) (F i) t} := by
  have hL : ∀ d ∈ contactSites K,
      d ∈ queryPrefix Q n ++ (contactSites K).toList :=
    fun d hd => List.mem_append.mpr (Or.inr (Finset.mem_toList.mpr hd))
  change (wilsonColorLaw R {σ : ColorField | (contacts K σ : ℝ) < t}).toReal ≤ _
  rw [wilsonColorLaw_low_eq_sampler_low R _ K t hL]
  exact measureReal_mono (low_observation_subset_all_failures R K Q F n t hF)

/-- Successful complete queries and all their earlier prefixes occur almost surely. -/
theorem full_contact_query_success_conull (R : RootPair) (K : Finset (Site 2))
    (Q : ℕ → List (Site 2)) (n : ℕ) :
    ∀ᵐ ξ ∂wilsonRows,
      (∃ out, samplerRun (initialSampler R)
        (queryPrefix Q n ++ (contactSites K).toList) ξ = some out) ∧
      ∀ i ≤ n, ∃ mid, samplerRun (initialSampler R) (queryPrefix Q i) ξ = some mid := by
  filter_upwards [wilson_sampler_success_conull R
    (queryPrefix Q n ++ (contactSites K).toList)] with ξ hξ
  refine ⟨hξ, ?_⟩
  intro i hi
  obtain ⟨T, hT⟩ := queryPrefix_exists_suffix Q hi
  obtain ⟨out, hs⟩ := hξ
  have hs' : samplerRun (initialSampler R)
      (queryPrefix Q i ++ (T ++ (contactSites K).toList)) ξ = some out := by
    rw [← List.append_assoc, ← hT]
    exact hs
  obtain ⟨mid, hm, _⟩ := samplerRun_prefix_known_colors _ out _ _ ξ hs'
  exact ⟨mid, hm⟩

end
end FiniteAvalanches.Wilson.Lattice.GlobalContactPersistence
