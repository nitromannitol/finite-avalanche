import FiniteAvalanches.Electrical.Ratio.Conductance
import FiniteAvalanches.Electrical.SplitStep.OriginalCounts21
import FiniteAvalanches.Electrical.SplitStep.ActualConnectivity
import FiniteAvalanches.Electrical.Geometry.SourceDualPath
import FiniteAvalanches.Electrical.Geometry.SourceDeletedDualPointwise
import FiniteAvalanches.Electrical.Green.Grounded
import FiniteAvalanches.External.PlaneDualBondCycle
import FiniteAvalanches.External.PlaneDualConnected

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Ratio
open LatticeProb
open FiniteAvalanches.Electrical.LatticeDrawing
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Electrical.SplitStep
open FiniteAvalanches.Electrical.ChordSplit
open scoped Classical
noncomputable section

theorem original_diagonal_eq_totalResponse :
  ∀ (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P),
  ∀ q : Plane → Plane, Continuous q →
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
              G (vertices i) (vertices i) = totalResponse D P hD marked copies i.val := by
  intro D P hD hDc hP marked q _hq Q _hpoint _hcurve charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends _hmarked J hc G i hi0 him
  let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
    (boundarySide _ _ _ copies i.val)
  have hK := actual_grounded_preconnected D P hD marked copies i.val hi0 him
  have huv : vertices i ≠ vertices (Fin.last m) := by
    intro h
    have he : i = Fin.last m := hinj h
    have hv := congrArg Fin.val he
    change i.val = m at hv
    omega
  have hcounts := original_diagonal_tree_forest_counts21 D P hD marked Q charts
    finiteFaces vertices hinj copies hends i hi0 him
  calc
    G (vertices i) (vertices i) =
        (Nat.card (J.TwoRootForest (vertices i) (vertices (Fin.last m))) : ℝ) /
          (Nat.card J.SpanningTree : ℝ) :=
      groundedGreen_diagonal_eq_count_ratio J (vertices (Fin.last m)) (vertices i) hc huv
    _ = (Nat.card K.SpanningTree : ℝ) /
        (Nat.card (K.TwoRootForest (.inr false) (.inr true)) : ℝ) := by
      rw [hcounts.1, hcounts.2]
    _ = effectiveConductance K (.inr false) (.inr true) (grounded_terminals_ne D P) hK :=
      (effectiveConductance_eq_count_ratio K (.inr false) (.inr true)
        (grounded_terminals_ne D P) hK).symm
    _ = totalResponse D P hD marked copies i.val :=
      actual_conductance_eq_totalResponse D P hD marked copies i.val hi0 him

end
end FiniteAvalanches.Electrical.Ratio
