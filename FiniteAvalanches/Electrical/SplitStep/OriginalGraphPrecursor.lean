import FiniteAvalanches.Electrical.SplitStep.OriginalQuotientCycleCut
import FiniteAvalanches.Electrical.SplitStep.OriginalSuffixStar
import FiniteAvalanches.Electrical.SplitStep.OriginalDenominator
import FiniteAvalanches.Electrical.Trees.CopiedAllMinors

/-! Original source graph data for the diagonal identity, on every supplied drawing. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section

abbrev originalGraphPrecursorCopyDec (D : Finset (Site 2))
    (P : OneSet D) (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) :=
  Classical.decEq _

abbrev originalGraphPrecursorVertexDec (D : Finset (Site 2)) (P : OneSet D) :
    DecidableEq (Vertex D P) := Classical.decEq _

abbrev originalGraphPrecursorFaceDec {D : Finset (Site 2)} {P : OneSet D}
    (Q : Drawing (primalGraph D P)) : DecidableEq (Face Q) := Classical.decEq _

attribute [local instance] originalGraphPrecursorCopyDec originalGraphPrecursorVertexDec
  originalGraphPrecursorFaceDec

/-- The full original-copy quotient relation, actual suffix star, both dual minors,
the common denominator, and the removable-cycle criterion, without any geometric replacement. -/
theorem original_diagonal_graph_precursor
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ {m : ℕ} (vertices : Fin (m + 1) → Face Q) (_hinj : Function.Injective vertices)
      (copies : Fin m ≃ {e : Copy D P marked //
        copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}),
    (∀ k : Fin m,
      ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
      ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) →
    ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
      let B := sourceDeletedDualGraph D P marked Q charts
      let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
        (boundarySide _ _ _ copies i.val)
      let Y := originalAllEdgeQuotient D P marked
      (⟨fun e => identifyGroundedTerminals (alpha D P) (beta D P) (K.left e),
        fun e => identifyGroundedTerminals (alpha D P) (beta D P) (K.right e)⟩ :
          CopiedGraph (NonemptyQuotient.Vertex (pairRoots (alpha D P) (beta D P)))
            (Copy D P marked)) = Y ∧
      (∀ A : Finset (Copy D P marked),
        ((Set.univ : Set (NonemptyQuotient.Vertex (pairRoots (alpha D P) (beta D P)))).Nonempty ∧
          (∀ x y, Y.reaches A x y) ∧
          ∀ e ∈ A, ¬Y.reaches (A.erase e) (Y.left e) (Y.right e)) ↔
        ((Set.univ : Set (Face Q)).Nonempty ∧ (∀ x y, B.reaches Aᶜ x y) ∧
          ∀ e ∈ Aᶜ, ¬B.reaches (Aᶜ.erase e) (B.left e) (B.right e))) ∧
      Finset.univ.filter (fun e => K.left e = Sum.inr true ∨ K.right e = Sum.inr true) =
        ((Finset.univ : Finset (Fin m)).filter (fun k => i.val ≤ k.val)).image
          (fun k => (copies k).val) ∧
      (∀ e, ¬(K.left e = Sum.inr true ∧ K.right e = Sum.inr true)) ∧
      ((copiedLaplacian K).submatrix
        (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => Sum.inl v)
        (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => Sum.inl v)).det =
          (Nat.card B.SpanningTree : ℝ) ∧
      0 < ((copiedLaplacian K).submatrix
        (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => Sum.inl v)
        (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => Sum.inl v)).det ∧
      ((copiedLaplacian B).submatrix
        (fun x : {x : Face Q // x ∉ ({vertices (Fin.last m)} : Finset (Face Q))} => x.val)
        (fun x : {x : Face Q // x ∉ ({vertices (Fin.last m)} : Finset (Face Q))} => x.val)).det =
          (Nat.card B.SpanningTree : ℝ) ∧
      ((copiedLaplacian B).submatrix
        (fun x : {x : Face Q // x ∉ ({vertices i, vertices (Fin.last m)} : Finset (Face Q))} => x.val)
        (fun x : {x : Face Q // x ∉ ({vertices i, vertices (Fin.last m)} : Finset (Face Q))} => x.val)).det =
          (Nat.card (B.TwoRootForest (vertices i) (vertices (Fin.last m))) : ℝ) ∧
      (∀ F : B.TwoRootForest (vertices i) (vertices (Fin.last m)),
        ∃ k : Fin m, i.val ≤ k.val ∧ (copies k).val ∉ F.val ∧
          ∃ T : Y.SpanningTree, T.val = F.valᶜ.erase (copies k).val ∧
            insert (copies k).val T.val = F.valᶜ) ∧
      ∀ (F : B.TwoRootForest (vertices i) (vertices (Fin.last m))) (e : Copy D P marked),
        ((Set.univ : Set (NonemptyQuotient.Vertex (pairRoots (alpha D P) (beta D P)))).Nonempty ∧
          (∀ x y, Y.reaches (F.valᶜ.erase e) x y) ∧
          ∀ f ∈ F.valᶜ.erase e, ¬Y.reaches ((F.valᶜ.erase e).erase f) (Y.left f) (Y.right f)) ↔
          ¬B.reaches F.val (B.left e) (B.right e) := by
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends i _hi0 him B K Y
  refine ⟨original_identify_grounded_graph D P marked copies i.val,
    original_allEdge_tree_complement_iff D P hD marked Q charts finiteFaces,
    original_grounded_star_eq_suffix D P marked copies i.val,
    original_grounded_no_loop_at_true D P marked copies i.val,
    original_split_free_det_eq_dual_tree_count D P hD marked Q charts finiteFaces copies i.val,
    original_split_free_det_pos D P hD marked copies i.val,
    CopiedGraph.copiedLaplacian_det_eq_tree_count B (vertices (Fin.last m)),
    CopiedGraph.copiedLaplacian_det_eq_twoRootForest_count B (vertices i) (vertices (Fin.last m)),
    original_quotient_tree_plus_suffix D P hD marked Q charts finiteFaces
      vertices hinj copies hends i him, ?_⟩
  intro F e
  apply original_quotient_erase_tree_iff D P hD marked Q charts finiteFaces
    (vertices i) (vertices (Fin.last m))
  intro heq
  have hi := congrArg Fin.val (hinj heq)
  simp only [Fin.val_last] at hi
  omega

end
end FiniteAvalanches.Electrical.SplitStep
