import FiniteAvalanches.Paper.Current.DFConsumers
import FiniteAvalanches.Paper.Current.FiniteExtendedContactLaw
import FiniteAvalanches.Trees.Lattice.CurrentSourceReciprocal
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual same-volume conditional means of the guarded source reciprocal. -/
namespace CountDictionaryReview
open FiniteAvalanches
open LatticeProb MeasureTheory FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.ConditioningConsumer TreeMeasurability11
open TreeMeasurability11.CurrentDomain
open scoped Classical ENNReal
noncomputable section

/-- The graph utility agrees with the paper object on its entire guarded source carrier. -/
theorem extended_count_eq_guarded (N : ℕ) (S : Finset (Site 2))
    (hS : S.Nonempty) (hN : ∀ x ∈ S, FiniteWired.inBox N x)
    (t : (graph N).SpanningTree) :
    Paper.CurrentDF176.finiteExtendedContacts N (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) t = sourceContactCount N S hS hN t := by
  by_cases hne : (graph N).ancestorOf t none (finiteMarks N S)
      (finiteMarks_nonempty N S hS hN) ≠ none
  · rw [Paper.CurrentDF176.finiteExtendedContacts_of_ne _ _ _ _ hne,
      sourceContactCount_of_nonsink _ _ _ _ _ hne,
      sourceContactCopies_eq_past _ _ _ _ _ hne]
  · rw [Paper.CurrentDF176.finiteExtendedContacts_of_sink _ _ _ _ (not_not.mp hne),
      sourceContactCount_of_sink _ _ _ _ _ (not_not.mp hne)]

theorem extended_count_congr (N : ℕ) (A B : Set (FiniteWired.Vertex N))
    (hA : A.Nonempty) (hB : B.Nonempty) (h : A = B)
    (t : (graph N).SpanningTree) :
    Paper.CurrentDF176.finiteExtendedContacts N A hA t =
      Paper.CurrentDF176.finiteExtendedContacts N B hB t := by
  subst B
  rfl

theorem source_marks_extended_eq_guarded {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t : (graph N).SpanningTree) :
    Paper.CurrentDF176.finiteExtendedContacts N (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t =
      sourceContactCount N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t := by
  exact (extended_count_congr N _ _ _ _
    (FiniteAvalanches.Sandpile.Source.finite_marks_eq N r) t).trans
      (extended_count_eq_guarded _ _ _ _ _)

/-- Conditional support excludes the sink-infinity branch and retains a counted copy. -/
theorem actual_conditional_nonsink_count {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    ∀ᵐ t ∂ProbabilityTheory.cond (law N)
      {t | (graph N).copiedConnectorObservation t₀ t none S hS},
      1 ≤ Paper.CurrentDF176.finiteExtendedContacts N S hS t ∧
        Paper.CurrentDF176.finiteExtendedContacts N S hS t ≠ ⊤ := by
  dsimp only
  apply ProbabilityTheory.ae_cond_of_forall_mem ((Set.toFinite _).measurableSet)
  intro t ht
  have hne : (graph N).ancestorOf t none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none := by
    rw [ht.2.2.1]
    exact hne₀
  constructor
  · rw [source_marks_extended_eq_guarded hr hrN t]
    exact sourceContactCount_ge_one _ _ _ _ _
  · rw [Paper.CurrentDF176.finiteExtendedContacts_of_ne _ _ _ _ hne]
    exact ENNReal.natCast_ne_top _

/-- The literal count law is an equality of full pushforward measures. -/
theorem actual_conditional_count_map {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let K := activeSites N ((graph N).span t₀ S)
    let R := observationRootPair N S hS t₀ hne₀
    (ProbabilityTheory.cond (law N)
      {t | (graph N).copiedConnectorObservation t₀ t none S hS}).map
      (Paper.CurrentDF176.finiteExtendedContacts N S hS) =
        (wilsonColorLaw R).map (unorderedContacts (K : Set (Site 2))) := by
  dsimp only
  ext D hD
  rw [Measure.map_apply (measurable_of_finite _) hD,
    Measure.map_apply (measurable_unorderedContacts _) hD]
  exact Paper.CurrentDF176.finite_source_extended_unordered_contact_law hr hrN t₀ hne₀ D

/-- Actual reciprocal expectations are transported through the complete count law. -/
theorem actual_conditional_guarded_mean {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let K := activeSites N ((graph N).span t₀ S)
    let R := observationRootPair N S hS t₀ hne₀
    (∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
      (fun _ hx => sourceMarks_inBox hr hrN hx) t
      ∂ProbabilityTheory.cond (law N)
        {t | (graph N).copiedConnectorObservation t₀ t none S hS}) =
      ∫ σ, (unorderedContacts (K : Set (Site 2)) σ)⁻¹.toReal ∂wilsonColorLaw R := by
  dsimp only
  let S := markedVertices (activeMarks N r)
  let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
  let K := activeSites N ((graph N).span t₀ S)
  let R := observationRootPair N S hS t₀ hne₀
  let μ := ProbabilityTheory.cond (law N)
    {t | (graph N).copiedConnectorObservation t₀ t none S hS}
  let f := Paper.CurrentDF176.finiteExtendedContacts N S hS
  have hm : Measurable f := measurable_of_finite _
  have hi : Measurable (fun z : ℝ≥0∞ => z⁻¹.toReal) :=
    ENNReal.measurable_toReal.comp measurable_inv
  have hmap := actual_conditional_count_map hr hrN t₀ hne₀
  dsimp only at hmap
  calc
    _ = ∫ t, (f t)⁻¹.toReal ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        rw [sourceFiniteReciprocal, ← source_marks_extended_eq_guarded hr hrN t]
    _ = ∫ z, z⁻¹.toReal ∂μ.map f := (integral_map hm.aemeasurable hi.aestronglyMeasurable).symm
    _ = ∫ z, z⁻¹.toReal ∂(wilsonColorLaw R).map (unorderedContacts (K : Set (Site 2))) := by
      rw [hmap]
    _ = _ := integral_map (measurable_unorderedContacts _).aemeasurable hi.aestronglyMeasurable

/-- The actual observed geometry and positive atom accompany the same mean identity. -/
theorem actual_mean_main_inputs {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let K := activeSites N ((graph N).span t₀ S)
    let R := observationRootPair N S hS t₀ hne₀
    0 < law N {t | (graph N).copiedConnectorObservation t₀ t none S hS} ∧
      ((lattice 2).induce (K : Set (Site 2))).Connected ∧
      ((lattice 2).induce R.one).Connected ∧ R.oneᶜ.Finite ∧
      Disjoint (K : Set (Site 2)) R.one ∧
      (∃ k ∈ K, ∃ y ∈ R.one, (lattice 2).Adj k y) ∧
      R.zero = (K : Set (Site 2)) ∧
      r ≤ K.sup (fun x => K.sup (fun y => FiniteAvalanches.siteRadius x y)) ∧
      (∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
        (fun _ hx => sourceMarks_inBox hr hrN hx) t
        ∂ProbabilityTheory.cond (law N)
          {t | (graph N).copiedConnectorObservation t₀ t none S hS}) =
        ∫ σ, (unorderedContacts (K : Set (Site 2)) σ)⁻¹.toReal ∂wilsonColorLaw R := by
  dsimp only
  obtain ⟨hK, hΓ, hfin, hd, hadj, hzero, hdiam⟩ :=
    source_marks_observed_cofinite_geometry hr hrN t₀ hne₀
  exact ⟨finite_whole_observation_pos _ _ _ t₀, hK, hΓ, hfin, hd, hadj,
    hzero, hdiam, actual_conditional_guarded_mean hr hrN t₀ hne₀⟩

end
end CountDictionaryReview

#print axioms CountDictionaryReview.extended_count_eq_guarded
#print axioms CountDictionaryReview.source_marks_extended_eq_guarded
#print axioms CountDictionaryReview.actual_conditional_nonsink_count
#print axioms CountDictionaryReview.actual_conditional_count_map
#print axioms CountDictionaryReview.actual_conditional_guarded_mean
#print axioms CountDictionaryReview.actual_mean_main_inputs
