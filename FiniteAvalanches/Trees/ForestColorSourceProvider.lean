import FiniteAvalanches.Trees.ForestColorMonotonicity

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.External

private theorem nested_original_forest_coupling {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (R R' : Set V) (hR : R.Nonempty) (hR' : R'.Nonempty) (hRR' : R ⊆ R') :
    ∃ q : Finset E → Finset E → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = G.uniformRootedForestMass R' hR' hconn S) ∧
      (∀ T, ∑ S, q S T = G.uniformRootedForestMass R hR hconn T) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, q S T ≠ 0 →
        G.is_rooted_forest R' S ∧ G.is_rooted_forest R T ∧ S ⊆ T) := by
  letI : Fintype {v : V // v ∈ R} :=
    @Subtype.fintype V (fun v => v ∈ R)
      (fun v => Classical.propDecidable (v ∈ R)) inferInstance
  letI : Fintype {v : V // v ∈ R'} :=
    @Subtype.fintype V (fun v => v ∈ R')
      (fun v => Classical.propDecidable (v ∈ R')) inferInstance
  have hc := G.supportGraph_preconnected_of_reaches hconn
  have hi := G.range_rootProjection_antitone
    (Set.toFinset_subset_toFinset.mpr hRR')
    (Set.toFinset_nonempty.mpr hR) (Set.toFinset_nonempty.mpr hR') hc
  obtain ⟨q, hq, hrow, hcol, htotal, hsupport⟩ :=
    (lyons_nestedProjectionDomination
      (G.rootProjection R'.toFinset (Set.toFinset_nonempty.mpr hR') hc)
      (G.rootProjection R.toFinset (Set.toFinset_nonempty.mpr hR) hc)
      (G.rootProjection_transpose R'.toFinset (Set.toFinset_nonempty.mpr hR') hc)
      (G.rootProjection_idempotent R'.toFinset (Set.toFinset_nonempty.mpr hR') hc)
      (G.rootProjection_transpose R.toFinset (Set.toFinset_nonempty.mpr hR) hc)
      (G.rootProjection_idempotent R.toFinset (Set.toFinset_nonempty.mpr hR) hc) hi
      (G.uniformRootedForestMass R' hR' hconn)
      (G.uniformRootedForestMass R hR hconn)
      (G.uniformRootedForestMass_nonneg R' hR' hconn)
      (G.uniformRootedForestMass_nonneg R hR hconn)
      (G.uniformRootedForestMass_set_inclusion_det R' hR' hconn)
      (G.uniformRootedForestMass_set_inclusion_det R hR hconn)).2
  refine ⟨q, hq, hrow, hcol, htotal, ?_⟩
  intro S T hne
  have hpos : 0 < q S T := lt_of_le_of_ne (hq S T) hne.symm
  have hr : q S T ≤ G.uniformRootedForestMass R' hR' hconn S := by
    rw [← hrow S]
    exact Finset.single_le_sum (fun U _ => hq S U) (Finset.mem_univ T)
  have hc' : q S T ≤ G.uniformRootedForestMass R hR hconn T := by
    rw [← hcol T]
    exact Finset.single_le_sum (fun U _ => hq U T) (Finset.mem_univ S)
  have hS : G.is_rooted_forest R' S := by
    by_contra hn
    simp only [uniformRootedForestMass, if_neg hn] at hr
    exact (not_lt_of_ge hr) hpos
  have hT : G.is_rooted_forest R T := by
    by_contra hn
    simp only [uniformRootedForestMass, if_neg hn] at hc'
    exact (not_lt_of_ge hc') hpos
  exact ⟨hS, hT, by by_contra hn; exact hne (hsupport S T hn)⟩

/-- Both stochastic color comparisons and actual uniform-forest monotone couplings. -/
theorem finite_color_monotonicity_with_couplings
    {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
    (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (A C : Set V) (hAC : Disjoint A C) (hA : A.Nonempty) (hC : C.Nonempty) :
  (∀ (C' : Set V), C' ⊆ C → C'.Nonempty →
    (∀ (H : Set (Set V)), (∀ U ∈ H, ∀ W : Set V, U ⊆ W → W ∈ H) →
      (Nat.card {F : G.RootedForest (A ∪ C') | G.oneVertices F.val C' ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A ∪ C')) ≤
        (Nat.card {F : G.RootedForest (A ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A ∪ C))) ∧
    (∃ q : Finset E → Finset E → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = if G.is_rooted_forest (A ∪ C') S then
        (Nat.card (G.RootedForest (A ∪ C')) : ℝ)⁻¹ else 0) ∧
      (∀ T, ∑ S, q S T = if G.is_rooted_forest (A ∪ C) T then
        (Nat.card (G.RootedForest (A ∪ C)) : ℝ)⁻¹ else 0) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, q S T ≠ 0 → G.is_rooted_forest (A ∪ C') S ∧
        G.is_rooted_forest (A ∪ C) T ∧ G.oneVertices S C' ⊆ G.oneVertices T C))) ∧
  (∀ (A' : Set V), A ⊆ A' → Disjoint A' C →
    (∀ (H : Set (Set V)), (∀ U ∈ H, ∀ W : Set V, U ⊆ W → W ∈ H) →
      (Nat.card {F : G.RootedForest (A' ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A' ∪ C)) ≤
        (Nat.card {F : G.RootedForest (A ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
          Nat.card (G.RootedForest (A ∪ C))) ∧
    (∃ q : Finset E → Finset E → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = if G.is_rooted_forest (A' ∪ C) S then
        (Nat.card (G.RootedForest (A' ∪ C)) : ℝ)⁻¹ else 0) ∧
      (∀ T, ∑ S, q S T = if G.is_rooted_forest (A ∪ C) T then
        (Nat.card (G.RootedForest (A ∪ C)) : ℝ)⁻¹ else 0) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, q S T ≠ 0 → G.is_rooted_forest (A' ∪ C) S ∧
        G.is_rooted_forest (A ∪ C) T ∧ G.oneVertices S C ⊆ G.oneVertices T C))) := by
  have hstoch := G.finite_forest_color_monotonicity hconn A C hAC hA hC
  have hR : (A ∪ C).Nonempty := hA.mono Set.subset_union_left
  constructor
  · intro C' hCC' hC'
    refine ⟨hstoch.1 C' hCC' hC', ?_⟩
    have hR' : (A ∪ C').Nonempty := hA.mono Set.subset_union_left
    obtain ⟨q, hq, hrow, hcol, htotal, hs⟩ :=
      nested_original_forest_coupling G hconn (A ∪ C') (A ∪ C) hR' hR
        (Set.union_subset_union (by rfl) hCC')
    refine ⟨fun S T => q T S, fun S T => hq T S, hcol, hrow, ?_, ?_⟩
    · rw [Finset.sum_comm]
      exact htotal
    · intro S T hne
      obtain ⟨hT, hS, hTS⟩ := hs T S hne
      exact ⟨hS, hT, G.oneVertices_subset_of_one_roots_removed A C C' hAC hCC'
        ⟨T, hT⟩ ⟨S, hS⟩ hTS⟩
  · intro A' hAA' hA'C
    refine ⟨hstoch.2 A' hAA' hA'C, ?_⟩
    have hR' : (A' ∪ C).Nonempty := (hA.mono hAA').mono Set.subset_union_left
    obtain ⟨q, hq, hrow, hcol, htotal, hs⟩ :=
      nested_original_forest_coupling G hconn (A ∪ C) (A' ∪ C) hR hR'
        (Set.union_subset_union hAA' (by rfl))
    refine ⟨q, hq, hrow, hcol, htotal, ?_⟩
    intro S T hne
    obtain ⟨hS, hT, hST⟩ := hs S T hne
    exact ⟨hS, hT, G.oneVertices_subset_of_edges_subset A A' C ⟨T, hT⟩ ⟨S, hS⟩ hST⟩

end FiniteAvalanches.Trees.Multigraph
