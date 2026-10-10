import FiniteAvalanches.Electrical.Trees.LoopTransport
import FiniteAvalanches.Wilson.RootContraction.Equivalence

/-! Root contraction on the complete original edge carrier, including contracted loops. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
open FiniteAvalanches.Trees
open FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- Simultaneous root contraction retaining every original copied ID. -/
def allEdgeGraph (G : Multigraph V E) (R : CopiedNetwork.Roots (V := V)) :
    CopiedGraph (Vertex R) E := ⟨fun e => project R (G.left e), fun e => project R (G.right e)⟩

/-- Contracted root-root IDs are retained loops and cannot be selected by a tree. -/
theorem allEdge_tree_lift_project (G : Multigraph V E)
    (R : CopiedNetwork.Roots (V := V)) (T : (allEdgeGraph G R).SpanningTree) :
    liftCopies G R (projectCopies G R T.val) = T.val := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact (mem_projectCopies G R T.val f).mp hf
  · intro he
    have hs : project R (G.left e) ≠ project R (G.right e) :=
      fun h => CopiedGraph.loop_not_mem _ T e h he
    exact Finset.mem_image.mpr ⟨⟨e, hs⟩,
      (mem_projectCopies G R T.val _).mpr he, rfl⟩

/-- The old nonloop quotient and the all-edge quotient have exactly the same selectable trees. -/
theorem allEdge_tree_image_iff (G : Multigraph V E)
    (R : CopiedNetwork.Roots (V := V)) (S : Finset (Copy G R)) :
    ((Set.univ : Set (Vertex R)).Nonempty ∧
      (∀ x y, (allEdgeGraph G R).reaches (liftCopies G R S) x y) ∧
      ∀ e ∈ liftCopies G R S,
        ¬(allEdgeGraph G R).reaches ((liftCopies G R S).erase e)
          ((allEdgeGraph G R).left e) ((allEdgeGraph G R).right e)) ↔
      (graph G R).is_tree Set.univ S := by
  have hdec : (@Subtype.instDecidableEq E
      (fun e => project R (G.left e) ≠ project R (G.right e)) (Classical.decEq E)) =
      Classical.decEq (Copy G R) := Subsingleton.elim _ _
  rw [hdec]
  exact CopiedGraph.nonloop_tree_image_iff (allEdgeGraph G R) S

/-- Every original subset is a quotient tree exactly when it is a rooted forest before contraction. -/
theorem allEdge_tree_iff_rooted_forest (G : Multigraph V E)
    (R : CopiedNetwork.Roots (V := V)) (S : Finset E) :
    ((Set.univ : Set (Vertex R)).Nonempty ∧
      (∀ x y, (allEdgeGraph G R).reaches S x y) ∧
      ∀ e ∈ S, ¬(allEdgeGraph G R).reaches (S.erase e)
        ((allEdgeGraph G R).left e) ((allEdgeGraph G R).right e)) ↔
      G.is_rooted_forest R.val S := by
  constructor
  · intro h
    let T : (allEdgeGraph G R).SpanningTree := ⟨S, h⟩
    have heq := allEdge_tree_lift_project G R T
    apply (rooted_forest_iff_tree_and_lift_project G R S).mpr
    refine ⟨(allEdge_tree_image_iff G R _).mp ?_, heq⟩
    rw [heq]
    exact h
  · intro h
    have heq := lift_project_forest G R h
    have ht := (allEdge_tree_image_iff G R _).mpr (tree_of_rooted_forest G R h)
    rw [heq] at ht
    exact ht

/-- Root contraction is a literal subset-preserving bijection even with retained root-root loops. -/
def allEdgeRootContractionEquiv (G : Multigraph V E)
    (R : CopiedNetwork.Roots (V := V)) :
    G.RootedForest R.val ≃ (allEdgeGraph G R).SpanningTree where
  toFun F := ⟨F.val, (allEdge_tree_iff_rooted_forest G R F.val).mpr F.property⟩
  invFun T := ⟨T.val, (allEdge_tree_iff_rooted_forest G R T.val).mp T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem allEdgeRootContractionEquiv_copies (G : Multigraph V E)
    (R : CopiedNetwork.Roots (V := V)) (F : G.RootedForest R.val) :
    (allEdgeRootContractionEquiv G R F).val = F.val := rfl

end
end FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
