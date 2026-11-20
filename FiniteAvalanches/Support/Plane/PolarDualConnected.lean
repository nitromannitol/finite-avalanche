import FiniteAvalanches.Support.Plane.TwoPoleSeparation
import FiniteAvalanches.External.PlaneDualConnected
import FiniteAvalanches.Electrical.Geometry.BoundaryPathOrder

/-!
# Connectivity of the polar dual

Edge-path duality supplies an alternative dual walk around the added arc.
Removing that single dual copy therefore leaves the original-copy dual connected.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
/-- An empty copied-edge set connects only a vertex to itself. -/
theorem CopiedGraph.eq_of_reaches_empty (J : CopiedGraph V E) {x y : V}
    (h : J.reaches ∅ x y) : x = y := by
  induction h with
  | refl => rfl
  | tail _ hadj _ =>
    obtain ⟨e, he, _⟩ := hadj
    exact (Finset.notMem_empty e he).elim

/-- The original-copy polar dual is connected. -/
theorem polarDual_preconnected {J : CopiedGraph V E} (D : PlaneEmbedding J)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : OuterArc D alpha beta) :
    (supportGraph (polarDual A).left (polarDual A).right).Preconnected := by
  classical
  letI : DecidableEq (E ⊕ Unit) := Classical.decEq _
  let B := augmentedGraph J alpha beta
  let K := augmentedDual A
  let m : E ⊕ Unit := Sum.inr ()
  have hB : ∀ x y, B.reaches Finset.univ x y := by
    intro x y
    have h := J.reaches_augmented_original alpha beta
      (J.reaches_univ_of_supportGraph_reachable (hconn x y))
    exact B.reaches_mono (Finset.subset_univ _) h
  have hBconn := B.supportGraph_preconnected_of_reaches hB
  have hKconn : (supportGraph K.left K.right).Preconnected := by
    exact FiniteAvalanches.External.finite_plane_dual_connected B A.embedding.drawing
      A.embedding.edgeChart hBconn
  have hnot : ¬ B.reaches ∅ (B.left m) (B.right m) := by
    intro h
    exact hne (B.eq_of_reaches_empty h)
  have hK : K = (⟨fun e => negativeChartFace A.embedding.drawing e (A.embedding.edgeChart e),
      fun e => positiveChartFace A.embedding.drawing e (A.embedding.edgeChart e)⟩ :
      CopiedGraph (Face A.embedding.drawing) (E ⊕ Unit)) := by
    congr 1
  have halt : K.reaches (Finset.univ.erase m) (K.left m) (K.right m) := by
    have heq := edge_path_duality A.embedding.drawing A.embedding.edgeChart ∅ m
      (Finset.notMem_empty m)
    have h := not_not.mp (mt heq.mpr hnot)
    rw [hK]
    simpa only [Finset.compl_empty] using h
  let copies : E ≃ {e : E ⊕ Unit // e ≠ m} :=
    { toFun := fun e => ⟨Sum.inl e, by simp [m]⟩
      invFun := fun e => match h : e.val with
        | Sum.inl a => a
        | Sum.inr b => (e.property (by rw [h])).elim
      left_inv := by intro e; rfl
      right_inv := by
        intro e
        apply Subtype.ext
        cases e with
        | mk value hvalue =>
          cases value with
          | inl a => rfl
          | inr b => exact (hvalue (by cases b; rfl)).elim }
  apply K.supportGraph_preconnected_of_erase_equiv (polarDual A) m copies
  · intro e
    rfl
  · intro e
    rfl
  · exact hKconn
  · exact halt

end FiniteAvalanches.Electrical.StatementGeometry
