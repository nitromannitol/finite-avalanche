import FiniteAvalanches.Electrical.Source.BoundaryExpectation
import CurrentSource.SplitCurrentScalar

/-! A direct normalization and logarithmic-factor consumer for the original
boundary indicator law. -/
namespace FiniteAvalanches.Electrical.CurrentSourceRoots
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open FiniteAvalanches.Electrical.Source.CurrentSplit
open scoped Classical BigOperators
noncomputable section

/-- The actual tree normalizer is nonzero, and its actual indicator mean supplies
both positivity and the logarithmic factor used by the split estimate. -/
theorem boundary_expectation_log_factor
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) [finiteFaces : Fintype (Face Q)]
    {m : ℕ} (vertices : Fin (m + 1) → Face Q) (hinj : Function.Injective vertices)
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (hends : ∀ k : Fin m,
      ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
      ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ))
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m)))
    (k : Fin m) :
    let J := sourceDeletedDualGraph D P marked Q charts
    letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
    let mean := (∑ T : J.SpanningTree,
      J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies k).val) /
      (Fintype.card J.SpanningTree : ℝ)
    (Fintype.card J.SpanningTree : ℝ) ≠ 0 ∧ 0 < mean ∧
      1 ≤ 1 + Real.log (2 / mean) := by
  intro J mean
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  have hdata := original_boundary_expectation D P hD hDc hP marked Q charts
    vertices hinj copies hends hmarked k
  exact ⟨ne_of_gt hdata.2.2.1, hdata.2.2.2.1,
    one_le_log_factor mean hdata.2.2.2.1 hdata.2.2.2.2⟩

end
end FiniteAvalanches.Electrical.CurrentSourceRoots
