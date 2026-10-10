import FiniteAvalanches.Electrical.SplitStep.OriginalGreenAssembly22
import FiniteAvalanches.Electrical.SplitStep.OriginalWholeTrial25
import FiniteAvalanches.External.PlanePuncturedChartFaceTransport

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical BigOperators
noncomputable section

/-- The split estimate on every original drawing and adjacent boundary copy. -/
theorem original_split_estimate24 :
  ∀ (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P),
  (∃ q : Plane → Plane, Continuous q ∧
    ∃ Q : Drawing (FiniteAvalanches.Electrical.LatticeDrawing.primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) ∧
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) ∧
      ∃ charts : ∀ e, EdgeChart Q e,
      ∃ _finiteFaces : Fintype (Face Q),
      ∃ m : ℕ, ∃ vertices : Fin (m + 1) → Face Q,
        Function.Injective vertices ∧
        ∃ copies : Fin m ≃ {e : Copy D P marked //
          copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P},
          (∀ k : Fin m,
            ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
              (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
            ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
              (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) ∧
          (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
            ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m)))) ∧
  (∀ q : Plane → Plane, Continuous q →
    ∀ Q : Drawing (FiniteAvalanches.Electrical.LatticeDrawing.primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) →
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) →
      ∀ charts : ∀ e, EdgeChart Q e,
      ∀ finiteFaces : Fintype (Face Q),
        letI : Fintype (Face Q) := finiteFaces
        ∀ m : ℕ, ∀ vertices : Fin (m + 1) → Face Q,
          Function.Injective vertices →
          ∀ copies : Fin m ≃ {e : Copy D P marked //
            copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P},
            (∀ k : Fin m,
              ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
                (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
              ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
                (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) →
            (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
                (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
              ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
                (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) →
            let J := sourceDeletedDualGraph D P marked Q charts
            let hc := source_deleted_dual_preconnected_of_classical
              D P hD hDc hP marked Q charts
              @FiniteAvalanches.External.finite_plane_dual_connected
              @FiniteAvalanches.External.finite_plane_dual_bond_cycle
            let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
            ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
              ∀ j : Fin m, (j.val + 1 = i.val ∨ j.val = i.val) →
                G (vertices i) (vertices i) - G (vertices 0) (vertices i) ≤
                  1 + 3888 * (1 + Real.log
                    (2 / (G (vertices 0) (vertices j.castSucc) -
                      G (vertices 0) (vertices j.succ))))) := by
  exact internal_split_of_whole_trial22 original_whole_weighted_trial

end
end FiniteAvalanches.Electrical.SplitStep
