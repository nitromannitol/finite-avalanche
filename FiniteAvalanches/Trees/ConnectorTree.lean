import FiniteAvalanches.Trees.Ancestors
import FiniteAvalanches.Trees.PathCopies

/-! The actual marked connector and its ancestor-to-root path form a copied-edge tree.
No connectedness, observed-forest law, or conditional-kernel identity is supplied. -/
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths SimpleGraph
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
variable (G : Multigraph V E)

omit [DecidableEq E] in
/-- Lift a real simple walk using exactly its original copies in the ambient edge set. -/
theorem reaches_of_walk_copy_membership {t s : Finset E} {x y : V}
    (p : (G.toSimple t).Walk x y)
    (h : ∀ f ∈ t, G.edge f ∈ p.edges → f ∈ s) : G.reaches s x y := by
  induction p with
  | nil => exact .refl
  | @cons x z y hxz q ih =>
    obtain ⟨f, hft, hxy⟩ := hxz
    have hfe : G.edge f = s(x,z) := by
      rcases hxy with hxy | hxy
      · simp only [edge, hxy.1, hxy.2]
      · simp only [edge, hxy.1, hxy.2]
        exact Sym2.eq_swap
    have hfs : f ∈ s := h f hft (by rw [hfe]; exact List.mem_cons_self)
    exact Relation.ReflTransGen.head ⟨f,hfs,hxy⟩
      (ih (fun e het heq => h e het (List.mem_cons_of_mem _ heq)))

/-- Copies of a unique path connect its starting vertex to every actual path vertex. -/
theorem reaches_rootPathCopies_support (t : G.SpanningTree) (a r : V)
    {x : V} (hx : x ∈ (path (G.toSimple_isTree t.property) a r).support) :
    G.reaches (G.rootPathCopies t a r) a x := by
  apply G.reaches_of_walk_copy_membership
    ((path (G.toSimple_isTree t.property) a r).takeUntil x hx)
  intro f hft hf
  exact Finset.mem_filter.mpr ⟨hft,
    (path (G.toSimple_isTree t.property) a r).edges_takeUntil_subset_edges hx hf⟩

                                                                               
                                                          
theorem reaches_internalEdges_span (t : G.SpanningTree) (S : Set V)
    (hS : S.Nonempty) {x y : V} (hx : x ∈ G.span t S) (hy : y ∈ G.span t S) :
    G.reaches (G.internalEdges (G.span t S) t.val) x y := by
  let p := path (G.toSimple_isTree t.property) x y
  have hc := connectingSubtree_convex (G.toSimple_isTree t.property) S hS x hx y hy
  apply G.reaches_of_walk_copy_membership p
  intro f hft hf
  exact Finset.mem_filter.mpr ⟨hft,
    hc _ (p.fst_mem_support_of_mem_edges hf),
    hc _ (p.snd_mem_support_of_mem_edges hf)⟩

/-- The full connector support retains the actual ancestor and all vertices of its
unique path to the designated root. -/
def connectorRootSupport (t : G.SpanningTree) (r : V) (S : Set V)
    (hS : S.Nonempty) : Set V :=
  G.span t S ∪ {x | x ∈ (path (G.toSimple_isTree t.property)
    (G.ancestorOf t r S hS) r).support}

/-- The observed connector contains exactly original minimal-branch copies and
original ancestor-to-root path copies. Parallel IDs are never identified. -/
def connectorCopies (t : G.SpanningTree) (r : V) (S : Set V)
    (hS : S.Nonempty) : Finset E :=
  G.internalEdges (G.span t S) t.val ∪
    G.rootPathCopies t (G.ancestorOf t r S hS) r

/-- Every connector copy is an actual original copy of the supplied tree. -/
theorem connectorCopies_subset (t : G.SpanningTree) (r : V) (S : Set V)
    (hS : S.Nonempty) : G.connectorCopies t r S hS ⊆ t.val :=
  Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- The genuine observed connector is a tree on its entire actual root support.
All geometry and connectedness are derived from the supplied ordinary spanning tree. -/
theorem is_tree_connectorCopies (t : G.SpanningTree) (r : V)
    (S : Set V) (hS : S.Nonempty) :
    G.is_tree (G.connectorRootSupport t r S hS) (G.connectorCopies t r S hS) := by
  let a := G.ancestorOf t r S hS
  have ha : a ∈ G.span t S :=
    commonAncestor_mem_connectingSubtree (G.toSimple_isTree t.property) r S hS
  have hsub : G.connectorCopies t r S hS ⊆ t.val := G.connectorCopies_subset t r S hS
  have hreach : ∀ x ∈ G.connectorRootSupport t r S hS,
      G.reaches (G.connectorCopies t r S hS) a x := by
    intro x hx
    rcases hx with hx | hx
    · exact G.reaches_mono (Finset.subset_union_left)
        (G.reaches_internalEdges_span t S hS ha hx)
    · exact G.reaches_mono (Finset.subset_union_right)
        (G.reaches_rootPathCopies_support t a r hx)
  refine ⟨⟨a, Or.inl ha⟩, ?_, ?_, G.is_forest_mono hsub t.property.2.2.2⟩
  · intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · have hs := G.supported_internalEdges (G.span t S) t.val f hf
      exact ⟨Or.inl hs.1, Or.inl hs.2⟩
    · have hp := (Finset.mem_filter.mp hf).2
      exact ⟨Or.inr ((path (G.toSimple_isTree t.property) a r).fst_mem_support_of_mem_edges hp),
        Or.inr ((path (G.toSimple_isTree t.property) a r).snd_mem_support_of_mem_edges hp)⟩
  · intro x hx y hy
    exact (G.reaches_symm (hreach x hx)).trans (hreach y hy)

/-- Literal expanded form for callers of the finite connector-completion law. -/
theorem is_tree_span_union_rootPathCopies (t : G.SpanningTree) (r : V)
    (S : Set V) (hS : S.Nonempty) :
    G.is_tree (G.span t S ∪ {x | x ∈ (path (G.toSimple_isTree t.property)
      (G.ancestorOf t r S hS) r).support})
      (G.internalEdges (G.span t S) t.val ∪
        G.rootPathCopies t (G.ancestorOf t r S hS) r) :=
  G.is_tree_connectorCopies t r S hS

end
end FiniteAvalanches.Trees.Multigraph
