import FiniteAvalanches.Paper.Current.DFRootOperations
import FiniteAvalanches.Paper.Current.ConditionalUnorderedContacts
import FiniteAvalanches.Sandpile.SourceCounting.ObservedCofiniteGeometry
import FiniteAvalanches.Trees.Lattice.OriginalContactCount

/-! Independent concrete source applications. No monotonicity, conditional-law,
positive-atom, copy-count or cofinite-intermediate conclusion is a premise. -/
namespace FiniteAvalanches.Paper.CurrentDF176.Consumers
open LatticeProb MeasureTheory FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.SourceCounting
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.ConditioningConsumer
open scoped Classical ENNReal
noncomputable section

/-- Every original ambient wired copy is counted once by the unordered lattice statistic. -/
theorem original_unordered_contact_dictionary (N : ℕ) (K C : Finset (Site 2))
    (hKC : K ⊆ C) (hbox : ∀ z ∈ C, FiniteWired.inBox N z) :
    (((graph N).admissibleEdges (FiniteAvalanches.Trees.Lattice.activeLift N C)
      (FiniteAvalanches.Trees.Lattice.activeLift N K)).card : ℝ≥0∞) =
      unorderedContacts (K : Set (Site 2)) (fun y => decide (y ∉ C)) := by
  have hz : ∀ x ∈ K, (fun y => decide (y ∉ C)) x = false := by
    intro x hx
    simp only [decide_eq_false_iff_not, not_not]
    exact hKC hx
  rw [ReciprocalCertificate14.original_contact_count N K C hKC hbox]
  exact (unorderedContacts_eq_contacts K _ hz).symm

private theorem zero_ne_unit : (0 : Site 2) ≠ unit (0 : Fin 2) :=
  (unit_ne_zero (0 : Fin 2)).symm

def initialRoots : RootPair :=
  ⟨{0}, {0}ᶜ, disjoint_compl_right, Set.singleton_nonempty _,
    ⟨unit 0, by simpa using (unit_ne_zero (0 : Fin 2))⟩⟩

def finalRoots : RootPair :=
  ⟨{unit 0}ᶜ, {unit 0}, disjoint_compl_left,
    ⟨0, by simpa using zero_ne_unit⟩, Set.singleton_nonempty _⟩

/-- Literal source comparison with infinite V. Both actual root unions are univ. -/
theorem concrete_four_set_infinite_tail (t : ℝ≥0∞) :
    (wilsonColorLaw finalRoots).real {σ | t ≤ unorderedContacts Set.univ σ} ≤
      (wilsonColorLaw initialRoots).real {σ | t ≤ unorderedContacts Set.univ σ} := by
  have hz : ({0} : Set (Site 2)) ⊆ {unit 0}ᶜ := by
    intro x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    simpa using zero_ne_unit
  have ho : ({unit 0} : Set (Site 2)) ⊆ {0}ᶜ := by
    intro x hx
    have hx0 : x = unit 0 := Set.mem_singleton_iff.mp hx
    subst x
    simpa using unit_ne_zero (0 : Fin 2)
  have hf0 : (({0} : Set (Site 2)) ∪ {0}ᶜ)ᶜ.Finite := by simp
  have hf1 : (({unit 0} : Set (Site 2))ᶜ ∪ {unit 0})ᶜ.Finite := by
    rw [Set.union_comm, Set.union_compl_self, Set.compl_univ]
    exact Set.finite_empty
  exact FiniteAvalanches.Paper.Current.source_unordered_contact_tail_mono
    {0} {unit 0}ᶜ {0}ᶜ {unit 0} (Set.singleton_nonempty _) (Set.singleton_nonempty _)
    hz ho disjoint_compl_right disjoint_compl_left hf0 hf1 Set.univ t

/-- The naive intermediate of the old one-line proof fails the actual source domain. -/
theorem naive_intermediate_not_cofinite :
    ¬ (({0} : Set (Site 2)) ∪ {unit 0})ᶜ.Finite := by
  exact ((Set.finite_singleton (0 : Site 2)).union
    (Set.finite_singleton (unit (0 : Fin 2)))).infinite_compl

/-- Finite zero roots ensure the unordered statistic has no mass at infinity. -/
theorem unordered_finite_zero_roots_no_infinity (R : RootPair) (K : Finset (Site 2))
    (hK : (K : Set (Site 2)) ⊆ R.zero) :
    wilsonColorLaw R {σ | unorderedContacts (K : Set (Site 2)) σ = ⊤} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [FiniteAvalanches.Paper.Current.ae_unorderedContacts_eq_contacts R K hK]
    with σ hσ
  change unorderedContacts (K : Set (Site 2)) σ ≠ ⊤
  rw [hσ]
  exact ENNReal.natCast_ne_top _

/-- The full positive copied-history atom and both literal root dictionaries
are produced together with the current unordered law at the same observation. -/
theorem actual_marks_positive_atom_and_unordered_law {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let G := graph N
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let Ksites := activeSites N (G.span t₀ S)
    let roots := observationRootPair N S hS t₀ hne₀
    roots.zero = (Ksites : Set (Site 2)) ∧
    roots.one = {x | ¬FiniteWired.inBox N x} ∪
      {x | FiniteWired.inBox N x ∧ wiredSite N x ∈ G.orderedAncestorTail t₀ none S hS} ∧
    Disjoint (Ksites : Set (Site 2)) roots.one ∧
    (roots.zero ∪ roots.one)ᶜ.Finite ∧
    0 < law N {t | G.copiedConnectorObservation t₀ t none S hS} ∧
    ∀ D : Set ℝ≥0∞, ProbabilityTheory.cond (law N)
      {t | G.copiedConnectorObservation t₀ t none S hS}
      {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
        (((G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
          (G.span t S)).card : ℕ) : ℝ≥0∞) ∈ D} =
      wilsonColorLaw roots {σ | unorderedContacts (Ksites : Set (Site 2)) σ ∈ D} := by
  dsimp only
  obtain ⟨_, hzero, hone, hpos, _⟩ :=
    source_marks_conditional_contact_law hr hrN t₀ hne₀ ∅
  refine ⟨hzero, hone, ?_, ?_, hpos, ?_⟩
  · rw [← hzero]
    exact (observationRootPair N _ _ t₀ hne₀).disjoint
  · exact (observationRootPair_one_connected_cofinite N _ _ t₀ hne₀).2.subset
      (Set.compl_subset_compl.mpr Set.subset_union_right)
  · intro D
    exact (FiniteAvalanches.Paper.Current.finite_conditional_unordered_contact_law
      hr hrN t₀ hne₀ D).2

/-- The actual conditional event of an infinite contact count has probability zero. -/
theorem actual_marks_conditional_infinity_zero {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let G := graph N
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    ProbabilityTheory.cond (law N)
      {t | G.copiedConnectorObservation t₀ t none S hS}
      {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
        (((G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
          (G.span t S)).card : ℕ) : ℝ≥0∞) ∈ ({⊤} : Set ℝ≥0∞)} = 0 := by
  dsimp only
  rw [(FiniteAvalanches.Paper.Current.finite_conditional_unordered_contact_law
    hr hrN t₀ hne₀ ({⊤} : Set ℝ≥0∞)).2]
  exact unordered_finite_zero_roots_no_infinity _ _
    (by rw [observationRootPair_zero_eq_activeSites])

/-- A source-active corner of the actual N=2 wired graph. -/
def corner : FiniteWired.Active 2 := fun _ => ⟨2, by norm_num⟩

theorem original_corner_sink_copies_distinct :
    FiniteWired.directionEdge corner (0, true) ≠
      FiniteWired.directionEdge corner (1, true) ∧
    FiniteWired.endpoints (FiniteWired.directionEdge corner (0, true)) = (some corner, none) ∧
    FiniteWired.endpoints (FiniteWired.directionEdge corner (1, true)) = (some corner, none) := by
  have h0 : ¬FiniteWired.inBox 2 (FiniteWired.site corner + FiniteWired.step (0, true)) := by
    intro h
    have hb := (h 0).2
    norm_num [FiniteWired.site, corner, FiniteWired.step, unit] at hb
  have h1 : ¬FiniteWired.inBox 2 (FiniteWired.site corner + FiniteWired.step (1, true)) := by
    intro h
    have hb := (h 1).2
    norm_num [FiniteWired.site, corner, FiniteWired.step, unit] at hb
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hd := FiniteWired.direction_edge_exit_injective corner h0 h1 he
    have hi := congrArg Prod.fst hd
    norm_num at hi
  · rw [FiniteWired.direction_edge_exit corner (0, true) h0]
    rfl
  · rw [FiniteWired.direction_edge_exit corner (1, true) h1]
    rfl

end
end FiniteAvalanches.Paper.CurrentDF176.Consumers

#print axioms FiniteAvalanches.Paper.CurrentDF176.Consumers.concrete_four_set_infinite_tail
#print axioms FiniteAvalanches.Paper.CurrentDF176.Consumers.naive_intermediate_not_cofinite
#print axioms FiniteAvalanches.Paper.CurrentDF176.Consumers.unordered_finite_zero_roots_no_infinity
#print axioms FiniteAvalanches.Paper.CurrentDF176.Consumers.actual_marks_positive_atom_and_unordered_law
#print axioms FiniteAvalanches.Paper.CurrentDF176.Consumers.actual_marks_conditional_infinity_zero
#print axioms FiniteAvalanches.Paper.CurrentDF176.Consumers.original_corner_sink_copies_distinct

#print axioms FiniteAvalanches.Paper.CurrentDF176.Consumers.original_unordered_contact_dictionary
