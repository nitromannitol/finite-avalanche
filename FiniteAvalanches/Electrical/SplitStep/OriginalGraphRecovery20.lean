import FiniteAvalanches.Electrical.SplitStep.OriginalGraphPrecursor
import FiniteAvalanches.Electrical.SplitStep.OriginalForestComplement
import FiniteAvalanches.Electrical.SplitStep.OriginalUniqueSuffixCut

/-! Original graph recovery: all-edge source data, the denominator bijection, and the unique suffix cut. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section
attribute [local instance] originalGraphPrecursorCopyDec originalGraphPrecursorVertexDec
  originalGraphPrecursorFaceDec

/-- Every drawing, face and original copy stays literal. The sole missing complement bijection
is the one from K trees to dual forests rooted at the two stated path faces. -/
theorem original_diagonal_graph_recovery20
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
      ((⟨fun e => identifyGroundedTerminals (alpha D P) (beta D P) (K.left e),
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
      (∀ (F : B.TwoRootForest (vertices i) (vertices (Fin.last m))) (e : Copy D P marked),
        ((Set.univ : Set (NonemptyQuotient.Vertex (pairRoots (alpha D P) (beta D P)))).Nonempty ∧
          (∀ x y, Y.reaches (F.valᶜ.erase e) x y) ∧
          ∀ f ∈ F.valᶜ.erase e, ¬Y.reaches ((F.valᶜ.erase e).erase f) (Y.left f) (Y.right f)) ↔
          ¬B.reaches F.val (B.left e) (B.right e))) ∧
      (∃ phi : K.TwoRootForest (Sum.inr false) (Sum.inr true) ≃ B.SpanningTree,
        ∀ F, (phi F).val = F.valᶜ) ∧
      ∀ F : B.TwoRootForest (vertices i) (vertices (Fin.last m)),
        ∃! k : Fin m, i.val ≤ k.val ∧
          ¬B.reaches F.val (B.left (copies k).val) (B.right (copies k).val) := by
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends i hi0 him B K Y
  refine ⟨original_diagonal_graph_precursor D P hD marked Q charts finiteFaces
    vertices hinj copies hends i hi0 him, ?_, ?_⟩
  · exact ⟨originalGroundedForestDualTreeEquiv D P hD marked Q charts finiteFaces copies i.val,
      originalGroundedForestDualTreeEquiv_copies D P hD marked Q charts finiteFaces copies i.val⟩
  · exact original_twoRootForest_unique_suffix_cut D P hD marked Q charts finiteFaces
      vertices hinj copies hends i him

end
end FiniteAvalanches.Electrical.SplitStep
