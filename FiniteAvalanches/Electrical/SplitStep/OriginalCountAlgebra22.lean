import FiniteAvalanches.Electrical.SplitStep.OriginalCounts21
import FiniteAvalanches.Electrical.SplitStep.OriginalAnalytic
import FiniteAvalanches.Electrical.Geometry.SourceDualPath
import FiniteAvalanches.External.PlaneDualBondCycle
import FiniteAvalanches.External.PlaneDualConnected

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical BigOperators
noncomputable section

/-- Original copied dual and split count ratios agree, including every loop and parallel ID. -/
theorem original_dual_split_count_ratio22 :
  ∀ (D : Finset (Site 2)) (P : OneSet D)
    (_hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)),
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
      (Nat.card (B.TwoRootForest (vertices i) (vertices (Fin.last m))) : ℝ) /
          (Nat.card B.SpanningTree : ℝ) =
        (Nat.card K.SpanningTree : ℝ) /
          (Nat.card (K.TwoRootForest (Sum.inr false) (Sum.inr true)) : ℝ) := by
  intro D P hD marked Q charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends i hi0 him B K
  obtain ⟨hnumerator, hdenominator⟩ := original_diagonal_tree_forest_counts21
    D P hD marked Q charts finiteFaces vertices hinj copies hends i hi0 him
  rw [← hnumerator, ← hdenominator]

end
end FiniteAvalanches.Electrical.SplitStep
