import FiniteAvalanches.Electrical.SplitStep.OriginalAllEdgeComplement
import FiniteAvalanches.Electrical.Trees.CopiedRootContraction
import FiniteAvalanches.Electrical.Trees.CopiedVertexTransport
import FiniteAvalanches.Electrical.Trees.SeparatingForestCompletion
import FiniteAvalanches.Electrical.ChordSplit.GroundedRootQuotient

/-! The second original complement bijection: two grounded-root forests to full dual trees. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section

local instance originalGroundedForestCopyDec (D : Finset (Site 2))
    (P : OneSet D) (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) :=
  Classical.decEq _

/-- Quotient-tree transport keeps every selected original ID, including the ground-loop exclusion. -/
def originalGroundedQuotientTreeEquiv (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    (K.rootQuotient (pairRoots (Sum.inr false) (Sum.inr true))).SpanningTree ≃
      (originalAllEdgeQuotient D P marked).SpanningTree := by
  intro K
  apply CopiedGraph.treeVertexEquiv _ _ (groundedRootVertexEquiv (alpha D P) (beta D P))
  · intro e
    exact (groundedRootVertexEquiv_project (alpha D P) (beta D P) (K.left e)).trans
      (identify_grounded_splitEndpoint (alpha D P) (beta D P) (boundarySide _ _ _ copies i)
        (copyA D P marked e) e)
  · intro e
    exact (groundedRootVertexEquiv_project (alpha D P) (beta D P) (K.right e)).trans
      (identify_grounded_splitEndpoint (alpha D P) (beta D P) (boundarySide _ _ _ copies i)
        (copyB D P marked e) e)

/-- Complement is a bijection between every actual separating K forest and every full B tree. -/
def originalGroundedForestDualTreeEquiv
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ),
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    K.TwoRootForest (Sum.inr false) (Sum.inr true) ≃
      (sourceDeletedDualGraph D P marked Q charts).SpanningTree := by
  letI : Fintype (Face Q) := finiteFaces
  intro m copies i K
  exact (K.rootQuotientForestEquiv (pairRoots (Sum.inr false) (Sum.inr true))).trans
    ((originalGroundedQuotientTreeEquiv D P marked copies i).trans
      (originalAllEdgeDualTreeEquiv D P hD marked Q charts finiteFaces))

theorem originalGroundedForestDualTreeEquiv_copies
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    letI : Fintype (Face Q) := finiteFaces
    ∀ {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ),
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    ∀ F : K.TwoRootForest (Sum.inr false) (Sum.inr true),
      (originalGroundedForestDualTreeEquiv D P hD marked Q charts finiteFaces copies i F).val = F.valᶜ := by
  intro m copies i K F
  rfl

end
end FiniteAvalanches.Electrical.SplitStep
