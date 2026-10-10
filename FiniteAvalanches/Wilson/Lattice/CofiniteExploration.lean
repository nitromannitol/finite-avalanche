import FiniteAvalanches.Wilson.Lattice.WarmContactPrefixes
import FiniteAvalanches.Wilson.Lattice.CofiniteContactScales
import FiniteAvalanches.Wilson.Lattice.NestedBoxStepThree

/-! Colors, distinct starts, and literal endpoints of the actual cofinite exploration. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CofiniteExploration
open LatticeProb FiniteAvalanches Sandpile MeasureTheory
open BatchRestart ConditionalIteration7 ActualContactHistory ActualQueryPrefixes
open WarmContactPrefixes CofiniteContactScales NestedBoxStepThree CofiniteHistorySuccess
open scoped Classical
noncomputable section

/-- Every queried site has an actual color in the completed sampler state. -/
theorem samplerRun_queries_covered (st out : SamplerState) (L : List (Site 2)) (ξ : Rows)
    (hs : samplerRun st L ξ = some out) : ∀ x ∈ L, x ∈ out.covered := by
  induction L generalizing st ξ with
  | nil => intro x hx; cases hx
  | cons x xs ih =>
    cases hstep : samplerStep st x (ξ 0) with
    | none => simp only [samplerRun, hstep, Option.bind_none] at hs; cases hs
    | some mid =>
      have htail : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hstep, Option.bind_some] using hs
      intro y hy
      rcases List.mem_cons.mp hy with he | hy
      · subst y
        change out.colors x ≠ none
        rw [samplerRun_preserves_covered_colors mid out xs _ htail x
          (DistinctStartContainment.samplerStep_start_covered st mid x (ξ 0) hstep)]
        exact DistinctStartContainment.samplerStep_start_covered st mid x (ξ 0) hstep
      · exact ih mid _ htail y hy

/-- The first queried history is the completed r_(n-1) box, including when n=1. -/
theorem warmup_query (κ n : ℕ) :
    warmPrefix (fun i => (boxSites (3 * sourceScale κ (n - 1 + i) + 1)).toList) 0 =
      (boxSites (3 * sourceScale κ (n - 1) + 1)).toList := by
  simp only [warmPrefix, queryPrefix, List.nil_append, Nat.add_zero]

theorem actual_warmup_colors (κ n : ℕ) (R : RootPair) (ξ : Rows) (out : SamplerState)
    (hs : samplerRun (initialSampler R)
      (warmPrefix (fun i => (boxSites (3 * sourceScale κ (n - 1 + i) + 1)).toList) 0) ξ = some out) :
    ∀ x ∈ boxSites (3 * sourceScale κ (n - 1) + 1), ∃ b : Bool, out.colors x = some b := by
  rw [warmup_query] at hs
  intro x hx
  have hcov := samplerRun_queries_covered (initialSampler R) out _ ξ hs x (Finset.mem_toList.mpr hx)
  exact Option.ne_none_iff_exists'.mp hcov

/-- The actual prefix retains earlier walks, while its distinct starts are exactly the last box. -/
theorem actual_prefix_distinct_starts (κ n i : ℕ) (hκ : 30 ≤ κ) :
    (warmPrefix (fun j => (boxSites (3 * sourceScale κ (n - 1 + j) + 1)).toList) i).toFinset.card =
      (6 * sourceScale κ (n - 1 + i) + 3) ^ 2 :=
  queryPrefix_box_card (fun j => sourceScale κ (n - 1 + j))
    (fun _ _ hab => sourceScale_mono κ hκ (Nat.add_le_add_left hab (n - 1))) i

/-- Every local source and neighbor endpoint is queried by its actual next batch. -/
theorem actual_step_query_endpoints (K : Finset (Site 2)) (κ n i : ℕ) (hn : 1 ≤ n) :
    let F := K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (sourceScale κ (n + i) : ℝ))
    ∀ d ∈ F ∪ contactSites F,
      d ∈ (boxSites (3 * sourceScale κ (n - 1 + (i + 1)) + 1)).toList := by
  have he : n - 1 + (i + 1) = n + i := by omega
  rw [he]
  exact source_and_contact_endpoints_queried K (sourceScale κ (n + i))

theorem actual_escape_indices (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    n - 1 ≤ n - 1 + i.val ∧ n - 1 + i.val ≤ 2 * n - 2 := by omega

/-- The closed-tail schedule still begins with the literal unpadded warm-up. -/
theorem closed_warmup_query (κ n : ℕ) :
    warmPrefix (fun j => (boxSites
      (3 * (sourceScale κ (n - 1 + j) + if j = 1 then 1 else 0) + 1)).toList) 0 =
      (boxSites (3 * sourceScale κ (n - 1) + 1)).toList := by
  simp only [warmPrefix, queryPrefix, List.nil_append,
    if_neg (by omega : (0 : ℕ) ≠ 1), Nat.add_zero]

/-- In the closed-tail schedule both incidence endpoints use the explicitly
padded first test and the unchanged later literal scales. -/
theorem closed_step_query_endpoints (K : Finset (Site 2)) (κ n i : ℕ) (hn : 1 ≤ n) :
    let b := sourceScale κ (n + i) + if i = 0 then 1 else 0
    let F := K.filter (fun x => (siteRadius 0 x : ℝ) ≤ 3 * (b : ℝ))
    ∀ d ∈ F ∪ contactSites F,
      d ∈ (boxSites (3 * (sourceScale κ (n - 1 + (i + 1)) +
        if i + 1 = 1 then 1 else 0) + 1)).toList := by
  have he : n - 1 + (i + 1) = n + i := by omega
  have hi : (i + 1 = 1) ↔ i = 0 := by omega
  rw [he]
  simp only [hi]
  exact source_and_contact_endpoints_queried K (sourceScale κ (n + i) + if i = 0 then 1 else 0)

end
end FiniteAvalanches.Wilson.Lattice.CofiniteExploration
