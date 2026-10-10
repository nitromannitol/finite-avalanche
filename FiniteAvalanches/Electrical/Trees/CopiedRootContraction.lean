import FiniteAvalanches.Electrical.Trees.AllEdgeRootContraction

/-! Full-carrier root contraction for copied graphs that already contain loops. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

local instance copiedRootNonloopDec (J : CopiedGraph V E) :
    DecidableEq {e : E // J.left e ≠ J.right e} := Classical.decEq _

/-- Identify the prescribed nonempty root set and retain every copied ID. -/
def rootQuotient (J : CopiedGraph V E) (R : Roots (V := V)) :
    CopiedGraph (NonemptyQuotient.Vertex R) E :=
  ⟨fun e => NonemptyQuotient.project R (J.left e),
    fun e => NonemptyQuotient.project R (J.right e)⟩

/-- The original-loop subtype changes no selected quotient-tree predicate. -/
theorem rootQuotient_tree_image_iff (J : CopiedGraph V E) (R : Roots (V := V))
    (S : Finset {e : E // J.left e ≠ J.right e}) :
    ((Set.univ : Set (NonemptyQuotient.Vertex R)).Nonempty ∧
      (∀ x y, (J.rootQuotient R).reaches (S.image Subtype.val) x y) ∧
      ∀ e ∈ S.image Subtype.val,
        ¬(J.rootQuotient R).reaches ((S.image Subtype.val).erase e)
          ((J.rootQuotient R).left e) ((J.rootQuotient R).right e)) ↔
      ((Set.univ : Set (NonemptyQuotient.Vertex R)).Nonempty ∧
        (∀ x y, (NonemptyQuotient.allEdgeGraph J.nonloopGraph R).reaches S x y) ∧
        ∀ e ∈ S, ¬(NonemptyQuotient.allEdgeGraph J.nonloopGraph R).reaches (S.erase e)
          ((NonemptyQuotient.allEdgeGraph J.nonloopGraph R).left e)
          ((NonemptyQuotient.allEdgeGraph J.nonloopGraph R).right e)) :=
  tree_image_iff (J.rootQuotient R) (NonemptyQuotient.allEdgeGraph J.nonloopGraph R)
    Subtype.val Subtype.coe_injective (fun _ => rfl) (fun _ => rfl) S

/-- A quotient tree selects precisely a rooted forest of the original copied graph. -/
theorem rootQuotient_tree_iff (J : CopiedGraph V E) (R : Roots (V := V)) (A : Finset E) :
    ((Set.univ : Set (NonemptyQuotient.Vertex R)).Nonempty ∧
      (∀ x y, (J.rootQuotient R).reaches A x y) ∧
      ∀ e ∈ A, ¬(J.rootQuotient R).reaches (A.erase e)
        ((J.rootQuotient R).left e) ((J.rootQuotient R).right e)) ↔
      ((∀ e ∈ A, ¬J.reaches (A.erase e) (J.left e) (J.right e)) ∧
        ∀ x, ∃ r ∈ R.val, J.reaches A x r ∧ ∀ r' ∈ R.val, J.reaches A x r' → r' = r) := by
  have h := fun S => (rootQuotient_tree_image_iff J R S).trans
    (NonemptyQuotient.allEdge_tree_iff_rooted_forest J.nonloopGraph R S)
  constructor
  · intro ht
    let T : (J.rootQuotient R).SpanningTree := ⟨A, ht⟩
    have ha : ∀ e ∈ A, J.left e ≠ J.right e := by
      intro e he hloop
      exact loop_not_mem _ T e (congrArg (NonemptyQuotient.project R) hloop) he
    have heq := nonloopSelection_image J A ha
    have himage : (J.nonloopSelection A).image Subtype.val = A := heq
    have hf := (h (J.nonloopSelection A)).mp (by rw [himage]; exact ht)
    have hf' := (nonloop_rooted_forest_image_iff J R.val _).mpr hf
    rw [himage] at hf'
    exact hf'
  · intro hf
    let F : J.RootedForest R.val := ⟨A, hf⟩
    have heq := nonloopSelection_image J A
      (fun e he hloop => rootedForest_loop_not_mem J R.val F e hloop he)
    have hf' := (nonloop_rooted_forest_image_iff J R.val (J.nonloopSelection A)).mp
      (by rw [heq]; exact hf)
    have ht := (h (J.nonloopSelection A)).mpr hf'
    rw [heq] at ht
    exact ht

/-- The all-ID quotient equivalence is literal on copied subsets, even with original loops. -/
def rootQuotientForestEquiv (J : CopiedGraph V E) (R : Roots (V := V)) :
    J.RootedForest R.val ≃ (J.rootQuotient R).SpanningTree where
  toFun F := ⟨F.val, (rootQuotient_tree_iff J R F.val).mpr F.property⟩
  invFun T := ⟨T.val, (rootQuotient_tree_iff J R T.val).mp T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rootQuotientForestEquiv_copies (J : CopiedGraph V E) (R : Roots (V := V))
    (F : J.RootedForest R.val) : (J.rootQuotientForestEquiv R F).val = F.val := rfl

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
