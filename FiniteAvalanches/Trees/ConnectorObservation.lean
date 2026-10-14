import FiniteAvalanches.Trees.PathCopyPreservation

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Multigraph.Observation11
open FiniteAvalanches.Trees.RootedPaths SimpleGraph
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Multigraph V E)

private theorem copies_reverse (t : G.SpanningTree) (x y : V) :
    G.rootPathCopies t x y = G.rootPathCopies t y x := by
  ext f
  simp only [rootPathCopies, Finset.mem_filter,
    path_reverse (G.toSimple_isTree t.property) x y, Walk.edges_reverse, List.mem_reverse]

private theorem span_path_copies (t : G.SpanningTree) (S : Set V) (hS : S.Nonempty)
    (x y : V) (hx : x ∈ G.span t S) (hy : y ∈ G.span t S) :
    G.rootPathCopies t x y ⊆ G.internalEdges (G.span t S) t.val :=
  pathCopies_subset_internal G t x y (G.span t S)
    (connectingSubtree_convex (G.toSimple_isTree t.property) S hS x hx y hy)

                                                                                   
                                                       
theorem span_and_branch_of_copy_subset (t₀ t : G.SpanningTree) (S : Set V)
    (hS : S.Nonempty) (h : G.internalEdges (G.span t₀ S) t₀.val ⊆ t.val) :
    G.span t S = G.span t₀ S ∧
    G.internalEdges (G.span t S) t.val = G.internalEdges (G.span t₀ S) t₀.val := by
  have hpaths (x y : V) (hx : x ∈ G.span t₀ S) (hy : y ∈ G.span t₀ S) :=
    path_data_of_copy_subset G t₀ t x y
      ((span_path_copies G t₀ S hS x y hx hy).trans h)
  have hs : G.span t S = G.span t₀ S := by
    ext z
    change (∃ x ∈ S, ∃ y ∈ S,
      z ∈ (path (G.toSimple_isTree t.property) x y).support) ↔
      (∃ x ∈ S, ∃ y ∈ S,
      z ∈ (path (G.toSimple_isTree t₀.property) x y).support)
    constructor <;> rintro ⟨x,hx,y,hy,hz⟩
    · exact ⟨x,hx,y,hy, by
        rwa [← (hpaths x y (subset_connectingSubtree _ S hx)
          (subset_connectingSubtree _ S hy)).1]⟩
    · exact ⟨x,hx,y,hy, by
        rwa [(hpaths x y (subset_connectingSubtree _ S hx)
          (subset_connectingSubtree _ S hy)).1]⟩
  refine ⟨hs, ?_⟩
  rw [hs]
  apply Finset.Subset.antisymm
  · intro f hf
    obtain ⟨hft,hl,hr⟩ := Finset.mem_filter.mp hf
    have hp : f ∈ G.rootPathCopies t (G.left f) (G.right f) :=
      (G.mem_rootPathCopies t (G.left f) (G.right f) f).mpr
        ⟨hft,t.property.2.2.2 f hft⟩
    rw [(hpaths (G.left f) (G.right f) hl hr).2.2] at hp
    exact span_path_copies G t₀ S hS (G.left f) (G.right f) hl hr hp
  · intro f hf
    obtain ⟨_,hl,hr⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨h hf,hl,hr⟩

/-- The actual prescribed connector event is exactly equality of its true minimal
span, original branch copies, common ancestor and original outgoing path copies.
No leaf condition is supplied: the minimal span is the union of all marked paths. -/
theorem connector_subset_iff_observation (t₀ t : G.SpanningTree) (r : V)
    (S : Set V) (hS : S.Nonempty) :
    (G.internalEdges (G.span t₀ S) t₀.val ∪
      G.rootPathCopies t₀ (G.ancestorOf t₀ r S hS) r) ⊆ t.val ↔
    G.span t S = G.span t₀ S ∧
    G.internalEdges (G.span t S) t.val = G.internalEdges (G.span t₀ S) t₀.val ∧
    G.ancestorOf t r S hS = G.ancestorOf t₀ r S hS ∧
    G.rootPathCopies t (G.ancestorOf t r S hS) r =
      G.rootPathCopies t₀ (G.ancestorOf t₀ r S hS) r := by
  constructor
  · intro h
    have hi : G.internalEdges (G.span t₀ S) t₀.val ⊆ t.val :=
      fun _ hf => h (Finset.mem_union_left _ hf)
    have ho : G.rootPathCopies t₀ (G.ancestorOf t₀ r S hS) r ⊆ t.val :=
      fun _ hf => h (Finset.mem_union_right _ hf)
    obtain ⟨hs,hb⟩ := span_and_branch_of_copy_subset G t₀ t S hS hi
    let a := G.ancestorOf t₀ r S hS
    have ha : a ∈ G.span t₀ S :=
      commonAncestor_mem_connectingSubtree (G.toSimple_isTree t₀.property) r S hS
    have hcommon : ∀ x ∈ S, ancestor (G.toSimple_isTree t.property) r a x := by
      intro x hx
      have hasource : ancestor (G.toSimple_isTree t₀.property) r a x :=
        (commonAncestor_spec (G.toSimple_isTree t₀.property) r S hS).1 x hx
      have hprefix : G.rootPathCopies t₀ r a ⊆ t.val := by
        rw [copies_reverse G t₀ r a]
        exact ho
      have hsuffix : G.rootPathCopies t₀ a x ⊆ t.val :=
        (span_path_copies G t₀ S hS a x ha
          (subset_connectingSubtree _ S hx)).trans hi
      have hfull : G.rootPathCopies t₀ r x ⊆ t.val := by
        intro f hf
        obtain ⟨hft,hfe⟩ := Finset.mem_filter.mp hf
        rw [path_split (G.toSimple_isTree t₀.property) hasource,
          Walk.edges_append, List.mem_append] at hfe
        rcases hfe with hf | hf
        · exact hprefix (Finset.mem_filter.mpr ⟨hft,hf⟩)
        · exact hsuffix (Finset.mem_filter.mpr ⟨hft,hf⟩)
      change a ∈ (path (G.toSimple_isTree t.property) r x).support
      rw [(path_data_of_copy_subset G t₀ t r x hfull).1]
      exact hasource
    have heqa : G.ancestorOf t r S hS = a :=
      (commonAncestor_eq_iff_mem_connectingSubtree
        (G.toSimple_isTree t.property) r S hS hcommon).mpr (by
          change a ∈ G.span t S
          rw [hs]
          exact ha)
    refine ⟨hs,hb,heqa,?_⟩
    rw [heqa]
    exact (path_data_of_copy_subset G t₀ t a r ho).2.2
  · rintro ⟨_,hb,ha,hp⟩
    apply Finset.union_subset
    · rw [← hb]
      exact Finset.filter_subset _ _
    · rw [← hp]
      exact Finset.filter_subset _ _

end
end FiniteAvalanches.Trees.Multigraph.Observation11
