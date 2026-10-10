import FiniteAvalanches.Trees.FiniteObservationIdentity
import FiniteAvalanches.Trees.RootedPathTail
import FiniteAvalanches.Trees.ConnectorTree

/-! The whole copied connecting tree and the ordered path strictly after its
common ancestor determine exactly the containing-connector atom. -/
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths SimpleGraph
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The actual rootward vertex sequence, with the common ancestor deleted. -/
def orderedAncestorTail (t : G.SpanningTree) (r : V) (S : Set V)
    (hS : S.Nonempty) : List V :=
  (path (G.toSimple_isTree t.property) (G.ancestorOf t r S hS) r).support.tail

/-- Each ordered pair records the direction of the corresponding rootward step. -/
def orderedAncestorDirections (t : G.SpanningTree) (r : V) (S : Set V)
    (hS : S.Nonempty) : List (V × V) :=
  let p := path (G.toSimple_isTree t.property) (G.ancestorOf t r S hS) r
  p.support.zip p.support.tail

/-- Equality of the true marked span, all its original internal copies, the
common ancestor, the ordered strict tail, and every original outgoing path copy. -/
def copiedConnectorObservation (t₀ t : G.SpanningTree) (r : V) (S : Set V)
    (hS : S.Nonempty) : Prop :=
  G.span t S = G.span t₀ S ∧
  G.internalEdges (G.span t S) t.val = G.internalEdges (G.span t₀ S) t₀.val ∧
  G.ancestorOf t r S hS = G.ancestorOf t₀ r S hS ∧
  G.orderedAncestorTail t r S hS = G.orderedAncestorTail t₀ r S hS ∧
  G.rootPathCopies t (G.ancestorOf t r S hS) r =
    G.rootPathCopies t₀ (G.ancestorOf t₀ r S hS) r

/-- Containment itself produces the full ordered observation; no observation
equivalence or geometric hypothesis is supplied by the caller. -/
theorem copiedConnectorObservation_iff_contains (t₀ t : G.SpanningTree)
    (r : V) (S : Set V) (hS : S.Nonempty) :
    G.copiedConnectorObservation t₀ t r S hS ↔
      G.connectorCopies t₀ r S hS ⊆ t.val := by
  have hbase := Observation11.connector_subset_iff_observation G t₀ t r S hS
  constructor
  · rintro ⟨hs, hb, ha, _, hp⟩
    exact hbase.mpr ⟨hs, hb, ha, hp⟩
  · intro h
    obtain ⟨hs, hb, ha, hp⟩ := hbase.mp h
    have ho : G.rootPathCopies t₀ (G.ancestorOf t₀ r S hS) r ⊆ t.val :=
      fun _ hf => h (Finset.mem_union_right _ hf)
    have hsupport := (Observation11.path_data_of_copy_subset G t₀ t
      (G.ancestorOf t₀ r S hS) r ho).1
    refine ⟨hs, hb, ha, ?_, hp⟩
    unfold orderedAncestorTail
    rw [ha, hsupport]

/-- The observation preserves the entire ordered path, including both endpoints. -/
theorem path_support_eq_of_copiedConnectorObservation (t₀ t : G.SpanningTree)
    (r : V) (S : Set V) (hS : S.Nonempty)
    (h : G.copiedConnectorObservation t₀ t r S hS) :
    (path (G.toSimple_isTree t.property) (G.ancestorOf t r S hS) r).support =
      (path (G.toSimple_isTree t₀.property) (G.ancestorOf t₀ r S hS) r).support := by
  have hc := (G.copiedConnectorObservation_iff_contains t₀ t r S hS).mp h
  have ho : G.rootPathCopies t₀ (G.ancestorOf t₀ r S hS) r ⊆ t.val :=
    fun _ hf => hc (Finset.mem_union_right _ hf)
  rw [h.2.2.1]
  exact (Observation11.path_data_of_copy_subset G t₀ t
    (G.ancestorOf t₀ r S hS) r ho).1

/-- Directions are retained in rootward order, rather than as unordered edges. -/
theorem directions_eq_of_copiedConnectorObservation (t₀ t : G.SpanningTree)
    (r : V) (S : Set V) (hS : S.Nonempty)
    (h : G.copiedConnectorObservation t₀ t r S hS) :
    G.orderedAncestorDirections t r S hS =
      G.orderedAncestorDirections t₀ r S hS := by
  unfold orderedAncestorDirections
  dsimp only
  rw [G.path_support_eq_of_copiedConnectorObservation t₀ t r S hS h]

theorem connectorRootSupport_eq_of_copiedConnectorObservation (t₀ t : G.SpanningTree)
    (r : V) (S : Set V) (hS : S.Nonempty)
    (h : G.copiedConnectorObservation t₀ t r S hS) :
    G.connectorRootSupport t r S hS = G.connectorRootSupport t₀ r S hS := by
  unfold connectorRootSupport
  rw [h.1, G.path_support_eq_of_copiedConnectorObservation t₀ t r S hS h]

theorem connectorCopies_eq_of_copiedConnectorObservation (t₀ t : G.SpanningTree)
    (r : V) (S : Set V) (hS : S.Nonempty)
    (h : G.copiedConnectorObservation t₀ t r S hS) :
    G.connectorCopies t r S hS = G.connectorCopies t₀ r S hS := by
  unfold connectorCopies
  rw [h.2.1, h.2.2.2.2]

/-- The other roots are exactly the ordered path vertices strictly after the
ancestor. The ancestor itself belongs to the connecting tree. -/
theorem connectorRootSupport_sdiff_span_eq_tail (t : G.SpanningTree)
    (r : V) (S : Set V) (hS : S.Nonempty) :
    G.connectorRootSupport t r S hS \ G.span t S =
      {x | x ∈ G.orderedAncestorTail t r S hS} := by
  let a := G.ancestorOf t r S hS
  let p := path (G.toSimple_isTree t.property) a r
  have ha : a ∈ G.span t S :=
    commonAncestor_mem_connectingSubtree (G.toSimple_isTree t.property) r S hS
  have hnodup : (a :: p.support.tail).Nodup := by
    rw [p.cons_tail_support]
    exact (path_isPath (G.toSimple_isTree t.property) a r).support_nodup
  have hnot : a ∉ p.support.tail := (List.nodup_cons.mp hnodup).1
  have hstrict := commonAncestor_strict_root_path_disjoint
    (G.toSimple_isTree t.property) r S hS
  ext x
  constructor
  · rintro ⟨hx, hxK⟩
    have hxp : x ∈ p.support := hx.resolve_left hxK
    have hxa : x ≠ a := fun h => hxK (h ▸ ha)
    rw [← p.cons_tail_support, List.mem_cons] at hxp
    exact hxp.resolve_left hxa
  · intro hx
    change x ∈ p.support.tail at hx
    have hxa : x ≠ a := fun h => hnot (h ▸ hx)
    have hxp : x ∈ p.support := by
      rw [← p.cons_tail_support]
      exact List.mem_cons_of_mem _ hx
    refine ⟨Or.inr hxp, ?_⟩
    apply Set.disjoint_left.mp hstrict ⟨?_, hxa⟩
    change x ∈ (path (G.toSimple_isTree t.property) r a).support
    rw [path_reverse, Walk.support_reverse, List.mem_reverse]
    exact hxp

theorem orderedAncestorTail_disjoint_span (t : G.SpanningTree)
    (r : V) (S : Set V) (hS : S.Nonempty) :
    Disjoint {x | x ∈ G.orderedAncestorTail t r S hS} (G.span t S) := by
  rw [← G.connectorRootSupport_sdiff_span_eq_tail t r S hS]
  exact Set.disjoint_left.mpr (fun _ hx hxK => hx.2 hxK)

/-- A nonroot ancestor gives a nonempty strict tail whose final vertex is the root. -/
theorem root_mem_orderedAncestorTail (t : G.SpanningTree) (r : V)
    (S : Set V) (hS : S.Nonempty) (hne : G.ancestorOf t r S hS ≠ r) :
    r ∈ G.orderedAncestorTail t r S hS := by
  let p := path (G.toSimple_isTree t.property) (G.ancestorOf t r S hS) r
  have hr := p.end_mem_support
  rw [← p.cons_tail_support, List.mem_cons] at hr
  exact hr.resolve_left hne.symm

/-- Every outgoing original copy belongs to its actual source-to-root path. -/
theorem parentEdge_mem_rootPathCopies (t : G.SpanningTree) (r a : V) (hne : a ≠ r) :
    G.parentEdge t r a hne ∈ G.rootPathCopies t a r := by
  let p := path (G.toSimple_isTree t.property) a r
  have he := G.parentEdge_spec t r a hne
  obtain ⟨b, hab, q, hp⟩ := Walk.exists_eq_cons_of_ne hne p
  refine Finset.mem_filter.mpr ⟨he.1, ?_⟩
  have hsp : (path (G.toSimple_isTree t.property) a r).snd = b := by
    change p.snd = b
    simp only [hp, Walk.snd_cons]
  have hedge : G.edge (G.parentEdge t r a hne) = s(a,b) := by
    rcases he.2 with he | he
    · simp only [edge, he.1, he.2, hsp]
    · simp only [edge, he.1, he.2, hsp, Sym2.eq_swap]
  change G.edge (G.parentEdge t r a hne) ∈ p.edges
  rw [hedge, hp, Walk.edges_cons]
  exact List.mem_cons_self

/-- The sink-incident last copy remains in the full connector. -/
theorem root_last_copy_mem_connector (t : G.SpanningTree) (r : V)
    (S : Set V) (hS : S.Nonempty) (hne : G.ancestorOf t r S hS ≠ r) :
    G.parentEdge t (G.ancestorOf t r S hS) r hne.symm ∈
      G.connectorCopies t r S hS := by
  apply Finset.mem_union_right
  have he := G.parentEdge_mem_rootPathCopies t (G.ancestorOf t r S hS) r hne.symm
  simpa only [rootPathCopies, path_reverse (G.toSimple_isTree t.property) r
    (G.ancestorOf t r S hS), Walk.edges_reverse, List.mem_reverse] using he

end
end FiniteAvalanches.Trees.Multigraph
