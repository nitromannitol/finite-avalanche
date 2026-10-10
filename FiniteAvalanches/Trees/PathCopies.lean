import FiniteAvalanches.Trees.CutComponents

/-! Deleting one original tree copy deletes exactly its simple edge, because
copy-to-edge is injective on an actual forest. -/
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
variable (G : Multigraph V E)

theorem toSimple_erase_tree (t : G.SpanningTree) (f : E) (hf : f ∈ t.val) :
    G.toSimple (t.val.erase f) = (G.toSimple t.val).deleteEdges {G.edge f} := by
  ext x y
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨⟨e, Finset.mem_of_mem_erase he, h⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hxy
    have heq : G.edge e = G.edge f := by
      rcases h with h | h
      · simpa only [edge, h.1, h.2] using hxy
      · simpa only [edge, h.1, h.2, Sym2.eq_swap] using hxy
    exact (Finset.mem_erase.mp he).1
      (G.edge_injOn_of_is_forest t.property.2.2.2 (Finset.mem_of_mem_erase he) hf heq)
  · rintro ⟨⟨e, he, h⟩, hn⟩
    refine ⟨e, Finset.mem_erase.mpr ⟨?_, he⟩, h⟩
    intro hef
    subst e
    apply hn
    simp only [Set.mem_singleton_iff]
    rcases h with h | h
    · simp only [edge, h.1, h.2]
    · simp only [edge, h.1, h.2, Sym2.eq_swap]

/-- The full root-path dictionary retains original edge-copy membership explicitly. -/
theorem separates_iff_mem_path (t : G.SpanningTree) (f : E) (hf : f ∈ t.val)
    (o r : V) :
    ¬G.reaches (t.val.erase f) o r ↔
      G.edge f ∈ (path (G.toSimple_isTree t.property) o r).edges := by
  have hr : G.reaches (t.val.erase f) o r ↔
      G.edge f ∉ (path (G.toSimple_isTree t.property) o r).edges := by
    rw [← G.toSimple_reachable, G.toSimple_erase_tree t f hf]
    change ((G.toSimple t.val).deleteEdges {s(G.left f, G.right f)}).Reachable o r ↔ _
    rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk]
    constructor
    · rintro ⟨p, hp⟩
      have he := path_eq (G.toSimple_isTree t.property) p.toPath.val p.toPath.property
      rw [he]
      exact fun h => hp (p.edges_toPath_subset_edges h)
    · intro hp
      exact ⟨path (G.toSimple_isTree t.property) o r, hp⟩
  exact (not_congr hr).trans not_not

/-- Literal original copies on the unique source-to-root path. -/
def rootPathCopies (t : G.SpanningTree) (o r : V) : Finset E :=
  t.val.filter fun f => G.edge f ∈ (path (G.toSimple_isTree t.property) o r).edges

theorem mem_rootPathCopies (t : G.SpanningTree) (o r : V) (f : E) :
    f ∈ G.rootPathCopies t o r ↔
      f ∈ t.val ∧ ¬G.reaches (t.val.erase f) o r := by
  simp only [rootPathCopies, Finset.mem_filter]
  constructor
  · rintro ⟨hf, hp⟩
    exact ⟨hf, (G.separates_iff_mem_path t f hf o r).mpr hp⟩
  · rintro ⟨hf, hs⟩
    exact ⟨hf, (G.separates_iff_mem_path t f hf o r).mp hs⟩

end
end FiniteAvalanches.Trees.Multigraph
