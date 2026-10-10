import FiniteAvalanches.Electrical.ChordSplit.FreeLaplacian
import FiniteAvalanches.Electrical.SplitStep.ActualEnergy
import FiniteAvalanches.Electrical.SplitStep.OriginalAllEdgeComplement

/-! The full original dual-tree denominator is the grounded split free determinant. -/
set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open scoped Classical
noncomputable section

local instance originalDenominatorVertexDec (D : Finset (Site 2)) (P : OneSet D) :
    DecidableEq (Vertex D P) := Classical.decEq _

local instance originalDenominatorCopyDec (D : Finset (Site 2))
    (P : OneSet D) (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) :=
  Classical.decEq _

/-- The common denominator, on every original drawing and every full alpha-copy ordering. -/
theorem original_split_free_det_eq_dual_tree_count
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ),
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    ((copiedLaplacian K).submatrix
      (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => Sum.inl v)
      (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => Sum.inl v)).det =
      (Nat.card (sourceDeletedDualGraph D P marked Q charts).SpanningTree : ℝ) := by
  letI : Fintype (Face Q) := finiteFaces
  intro m copies i K
  let G := StatementTypes.graph D P marked
  have hJ : originalGraph D P marked = (⟨G.left, G.right⟩ : CopiedGraph _ _) := rfl
  dsimp only [K]
  rw [hJ, groundedSplit_free_det_eq_forest_count G (alpha D P) (beta D P)
    (boundarySide _ _ _ copies i)]
  let phi := (FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient.allEdgeRootContractionEquiv
    G (pairRoots (alpha D P) (beta D P))).trans
      (originalAllEdgeDualTreeEquiv D P hD marked Q charts finiteFaces)
  exact congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_congr phi)

/-- The common normalizer is strictly positive on the entire actual carrier. -/
theorem original_split_free_det_pos
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    0 < ((copiedLaplacian K).submatrix
      (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => Sum.inl v)
      (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => Sum.inl v)).det := by
  intro K
  let G := StatementTypes.graph D P marked
  have hJ : originalGraph D P marked = (⟨G.left, G.right⟩ : CopiedGraph _ _) := rfl
  dsimp only [K]
  rw [hJ, groundedSplit_free_laplacian]
  have hm : (copiedLaplacian (⟨G.left, G.right⟩ : CopiedGraph _ _)).submatrix
      (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => v.val)
      (fun v : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} => v.val) =
      (G.rootGram {alpha D P, beta D P}).submatrix
        (originalFreeEquiv (alpha D P) (beta D P))
        (originalFreeEquiv (alpha D P) (beta D P)) := by
    rw [← copiedLaplacian_eq_rootGram]
    rfl
  rw [hm, Matrix.det_submatrix_equiv_self]
  exact G.rootGram_det_pos {alpha D P, beta D P}
    ⟨alpha D P, Finset.mem_insert_self _ _⟩
    (Repair8.graph_connected D P hD marked).preconnected

end
end FiniteAvalanches.Electrical.SplitStep
