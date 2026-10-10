import FiniteAvalanches.Trees.OrderedConnectorObservation
import FiniteAvalanches.Trees.Lattice.ConnectorPastContacts

/-! Finite conditioning on the actual whole copied observation, followed by the
literal past-boundary statistic on the original wired multigraph. -/
namespace FiniteAvalanches.ConditioningConsumer
open FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees
open MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- On the whole observation atom, deletion of its fixed copied connector gives
the actual past-boundary count for each admitted tree. -/
theorem ambient_count_eq_past_on_observation (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ t : (graph N).SpanningTree)
    (h : (graph N).copiedConnectorObservation t₀ t none S hS)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    ambientColorContacts (graph N) ((graph N).span t₀ S)
      ((graph N).connectorRootSupport t₀ none S hS \ (graph N).span t₀ S)
      (t.val \ (graph N).connectorCopies t₀ none S hS) =
        ((graph N).admissibleEdges
          ((graph N).past t none ((graph N).ancestorOf t none S hS) hne)
          ((graph N).span t S)).card := by
  rw [← h.1,
    ← (graph N).connectorRootSupport_eq_of_copiedConnectorObservation t₀ t none S hS h,
    ← (graph N).connectorCopies_eq_of_copiedConnectorObservation t₀ t none S hS h]
  exact finite_ambient_contacts_eq_past_admissible N S hS t hne

/-- The exact finite conditional distribution of the source past-boundary count.
The connector geometry, its tree proof, and the positive atom are constructed
from the observed ordinary tree inside the proof. -/
theorem finite_whole_observation_past_count (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none) (D : Set ℕ) :
    let G := graph N
    let K := G.span t₀ S
    let R := G.connectorRootSupport t₀ none S hS
    let Γ := R \ K
    ProbabilityTheory.cond (law N)
        {t | G.copiedConnectorObservation t₀ t none S hS}
        {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
          (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
            (G.span t S)).card ∈ D} =
      (Nat.card {F : G.RootedForest R // ambientColorContacts G K Γ F.val ∈ D} : ℝ≥0∞) /
        Nat.card (G.RootedForest R) := by
  dsimp only
  let G := graph N
  let K := G.span t₀ S
  let R := G.connectorRootSupport t₀ none S hS
  let H := G.connectorCopies t₀ none S hS
  let Γ := R \ K
  let P : Set G.SpanningTree := {t | G.copiedConnectorObservation t₀ t none S hS}
  let B : Set G.SpanningTree := {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
    (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
      (G.span t S)).card ∈ D}
  let A : Set (Finset (FiniteWired.Edge N)) :=
    {F | ambientColorContacts G K Γ F ∈ D}
  have hP : P = {t | H ⊆ t.val} := by
    ext t
    exact G.copiedConnectorObservation_iff_contains t₀ t none S hS
  have hB : P ∩ B = {t | H ⊆ t.val ∧ t.val \ H ∈ A} := by
    ext t
    constructor
    · rintro ⟨ht, hne, hc⟩
      refine ⟨(G.copiedConnectorObservation_iff_contains t₀ t none S hS).mp ht, ?_⟩
      change ambientColorContacts G K Γ (t.val \ H) ∈ D
      rw [ambient_count_eq_past_on_observation N S hS t₀ t ht hne]
      exact hc
    · rintro ⟨ht, hc⟩
      have hp := (G.copiedConnectorObservation_iff_contains t₀ t none S hS).mpr ht
      have hne : G.ancestorOf t none S hS ≠ none := by
        rw [hp.2.2.1]
        exact hne₀
      refine ⟨hp, hne, ?_⟩
      rw [← ambient_count_eq_past_on_observation N S hS t₀ t hp hne]
      exact hc
  have hC : MeasurableSet P := (Set.toFinite _).measurableSet
  have hC' : MeasurableSet {t : G.SpanningTree | H ⊆ t.val} :=
    (Set.toFinite _).measurableSet
  have hinter : {t : G.SpanningTree | H ⊆ t.val} ∩
      {t | H ⊆ t.val ∧ t.val \ H ∈ A} =
        {t | H ⊆ t.val ∧ t.val \ H ∈ A} := by
    ext t
    exact ⟨fun ht => ht.2, fun ht => ⟨ht.1, ht⟩⟩
  have hcond := G.treeLaw_cond_connector_count_event R H
    (G.is_tree_connectorCopies t₀ none S hS) t₀
    (G.connectorCopies_subset t₀ none S hS) A
  change ProbabilityTheory.cond G.treeLaw P B = _
  rw [ProbabilityTheory.cond_apply hC, hB, hP]
  rw [ProbabilityTheory.cond_apply hC', hinter] at hcond
  exact hcond

/-- The conditioning atom is positive on the actual uniform finite wired law. -/
theorem finite_whole_observation_pos (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree) :
    0 < law N {t | (graph N).copiedConnectorObservation t₀ t none S hS} := by
  have hP : {t | (graph N).copiedConnectorObservation t₀ t none S hS} =
      {t | (graph N).connectorCopies t₀ none S hS ⊆ t.val} := by
    ext t
    exact (graph N).copiedConnectorObservation_iff_contains t₀ t none S hS
  rw [hP]
  exact (graph N).treeLaw_containing_connector_pos
    ((graph N).connectorCopies t₀ none S hS) t₀
    ((graph N).connectorCopies_subset t₀ none S hS)

/-- The original outgoing copy is counted even though it is deleted from every
forest completion. The count filters the whole ambient copied edge carrier. -/
theorem finite_outgoing_contact_in_every_completion (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none)
    (F : (graph N).RootedForest ((graph N).connectorRootSupport t none S hS)) :
    let G := graph N
    let K := G.span t S
    let Γ := G.connectorRootSupport t none S hS \ K
    let e := G.parentEdge t none (G.ancestorOf t none S hS) hne
    e ∈ Finset.univ.filter (fun f =>
      (G.left f ∈ K ∧ G.right f ∈ G.oneVertices F.val Γ) ∨
      (G.right f ∈ K ∧ G.left f ∈ G.oneVertices F.val Γ)) ∧ e ∉ F.val := by
  dsimp only
  let G := graph N
  let a := G.ancestorOf t none S hS
  let e := G.parentEdge t none a hne
  let p := RootedPaths.path (G.toSimple_isTree t.property) a none
  have ha : a ∈ G.span t S :=
    RootedPaths.commonAncestor_mem_connectingSubtree (G.toSimple_isTree t.property) none S hS
  have he := G.parentEdge_spec t none a hne
  have hsnd : p.snd ∈ G.orderedAncestorTail t none S hS := by
    obtain ⟨b, hab, q, hp⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne p
    change p.snd ∈ p.support.tail
    simp only [hp, SimpleGraph.Walk.snd_cons, SimpleGraph.Walk.support_cons, List.tail_cons]
    exact q.start_mem_support
  have hΓ : p.snd ∈ G.connectorRootSupport t none S hS \ G.span t S := by
    rw [G.connectorRootSupport_sdiff_span_eq_tail]
    exact hsnd
  have hcolor : p.snd ∈ G.oneVertices F.val
      (G.connectorRootSupport t none S hS \ G.span t S) :=
    ⟨p.snd, hΓ, Relation.ReflTransGen.refl⟩
  have heH : e ∈ G.connectorCopies t none S hS :=
    Finset.mem_union_right _ (G.parentEdge_mem_rootPathCopies t none a hne)
  constructor
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases he.2 with he | he
    · exact Or.inl ⟨he.1 ▸ ha, he.2 ▸ hcolor⟩
    · exact Or.inr ⟨he.1 ▸ ha, he.2 ▸ hcolor⟩
  · exact Finset.disjoint_left.mp (G.rootedForest_disjoint_connector
      (G.is_tree_connectorCopies t none S hS).2.1 F.property) heH

end
end FiniteAvalanches.ConditioningConsumer
