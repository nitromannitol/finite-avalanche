import FiniteAvalanches.Sandpile.SourceCounting.MainOriginCofinite
import FiniteAvalanches.Electrical.Reference.ReferenceMomentOfSplit
import FiniteAvalanches.Wilson.Lattice.RevealedRoots.ReferenceConditional
import FiniteAvalanches.Wilson.Lattice.CofiniteReciprocalAssembly

set_option autoImplicit false
namespace FiniteAvalanches.ConditioningMain
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.External.SandpileLimit
open FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Electrical.LatticeDrawing FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical ENNReal BigOperators
noncomputable section

/-- The complete split estimate implies origin stabilization and the radius tail. -/
theorem main_origin_of_split
    (hsplit :
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
              FiniteAvalanches.External.finite_plane_dual_connected
              FiniteAvalanches.External.finite_plane_dual_bond_cycle
            let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
            ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
              ∀ j : Fin m, (j.val + 1 = i.val ∨ j.val = i.val) →
                G (vertices i) (vertices i) - G (vertices 0) (vertices i) ≤
                  1 + 3888 * (1 + Real.log
                    (2 / (G (vertices 0) (vertices j.castSucc) -
                      G (vertices 0) (vertices j.succ)))))
    ) :
(∀ᵐ η ∂(infiniteVolumeLaw : Measure StableField),
    ∃ w : List Site2, Stabilizes η (oneGrain (0 : Site2)) w) ∧
  ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ,
    ∀ R : ℝ, 0 ≤ R →
      (infiniteVolumeLaw : Measure StableField).real
        {η | ENNReal.ofReal R < extendedCount (radius η (0 : Site2))} ≤
      C * Real.rpow (Real.log (R + 2)) (-a) := by
  exact main_origin_of_cofinite_reciprocal
    (FiniteAvalanches.Wilson.Lattice.CofiniteReciprocalAssembly.cofinite_reciprocal_of_open_joint_v3
      (FiniteAvalanches.Wilson.Lattice.SourceTargets.local_comparison_and_revealed_roots_of_reference_v3
        (FiniteAvalanches.Electrical.Source.Reference.reference_moment_of_split hsplit)))

end
end FiniteAvalanches.ConditioningMain
