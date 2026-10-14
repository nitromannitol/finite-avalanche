import FiniteAvalanches.Electrical.SplitStep.OriginalCurrent
import FiniteAvalanches.Electrical.SplitStep.BoundaryPositive
import FiniteAvalanches.Electrical.Reference.ForestDualMoments

/-! Literal boundary indicator expectations on the original deleted dual. -/

namespace FiniteAvalanches.Electrical.Source
open LatticeProb StatementGeometry BSST Plane.SourceLattice LatticeDrawing
open FiniteAvalanches.Electrical.SplitStep
open scoped Classical BigOperators
noncomputable section

/-- The original uniform tree indicator mean is its grounded Green drop, with a
positive actual tree normalizer and a strictly positive mean at most one. -/
theorem original_boundary_expectation
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
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected
      FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
    let mean := (∑ T : J.SpanningTree,
      J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies k).val) /
      (Fintype.card J.SpanningTree : ℝ)
    mean = G (vertices 0) (vertices k.castSucc) - G (vertices 0) (vertices k.succ) ∧
      0 < Fintype.card J.SpanningTree ∧
      0 < (Fintype.card J.SpanningTree : ℝ) ∧ 0 < mean ∧ mean ≤ 1 := by
  intro J hc G mean
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  have hvoltage := original_boundary_voltage_eq_tree_average D P hD marked Q charts
    vertices copies hmarked k
  have hgreen := original_boundary_voltage_eq_green_drop D P hD hDc hP marked Q charts
    vertices hinj copies hends hmarked k
  have hmean : mean = G (vertices 0) (vertices k.castSucc) -
      G (vertices 0) (vertices k.succ) := hvoltage.symm.trans hgreen
  have hcard := (source_forest_contact_law D P hD marked Q charts finiteFaces
    (Fintype.ofFinite J.SpanningTree) m vertices copies hmarked).2.1
  have hpositive := boundary_voltage_pos_le_one D P hD marked (copies k)
  change 0 < _ ∧ _ ≤ 1 at hpositive
  rw [hvoltage] at hpositive
  exact ⟨hmean, hcard, by exact_mod_cast hcard, hpositive.1, hpositive.2⟩

end
end FiniteAvalanches.Electrical.Source
