import FiniteAvalanches.Electrical.SplitStep.OriginalAnalytic
import FiniteAvalanches.Electrical.Geometry.SourceDualPath
import FiniteAvalanches.Electrical.Geometry.SourceDeletedDualPointwise
import FiniteAvalanches.External.PlaneDualBondCycle
import FiniteAvalanches.External.PlaneDualConnected

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.LatticeDrawing
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.ChordSplit
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical BigOperators
noncomputable section

/-- Bare source data produce one original compatible path and the analytic split reduction
on that path. The original off-diagonal current is derived; its diagonal dictionary remains open. -/
theorem actual_source_split_analytic
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    ∃ q : Plane → Plane, Continuous q ∧
    ∃ Q : Drawing (FiniteAvalanches.Electrical.LatticeDrawing.primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) ∧
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) ∧
    ∃ charts : ∀ e, EdgeChart Q e,
    ∃ finiteFaces : Fintype (Face Q),
      letI : Fintype (Face Q) := finiteFaces
      ∃ m : ℕ, 3 ≤ m ∧ ∃ vertices : Fin (m + 1) → Face Q,
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
          (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) ∧
      (supportGraph (sourceDeletedDualGraph D P marked Q charts).left
        (sourceDeletedDualGraph D P marked Q charts).right).Preconnected ∧
      let J := sourceDeletedDualGraph D P marked Q charts
      let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
        @FiniteAvalanches.External.finite_plane_dual_connected
        @FiniteAvalanches.External.finite_plane_dual_bond_cycle
      let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
      ∀ i : Fin (m + 1), ∀ (hi0 : 0 < i.val) (him : i.val < m),
        (supportGraph (actualSplit D P marked copies i.val).left
          (actualSplit D P marked copies i.val).right).Connected ∧
        (let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
            (boundarySide _ _ _ copies i.val);
          effectiveConductance K (.inr false) (.inr true) (grounded_terminals_ne D P)
            (actual_grounded_preconnected D P hD marked copies i.val hi0 him) =
              totalResponse D P hD marked copies i.val) ∧
        (-laplacian (actualSplit D P marked copies i.val).left
          (actualSplit D P marked copies i.val).right (splitVoltage D P hD marked) (.inr true) =
          G (vertices 0) (vertices i)) ∧
        ∀ f : SplitVertex (alpha D P) → ℝ, f (.inr false) = 0 → f (.inr true) = 1 →
          energy (actualSplit D P marked copies i.val).left
            (actualSplit D P marked copies i.val).right
            (fun x => (1 - splitVoltage D P hD marked x) * f x) =
            G (vertices 0) (vertices i) +
              weightedEnergy (actualSplit D P marked copies i.val).left
                (actualSplit D P marked copies i.val).right
                (fun x => 1 - splitVoltage D P hD marked x) f ∧
          totalResponse D P hD marked copies i.val - G (vertices 0) (vertices i) ≤
            ∑ e : Copy D P marked,
              (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i.val).left e)) *
              (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i.val).right e)) *
              (f ((actualSplit D P marked copies i.val).left e) -
                f ((actualSplit D P marked copies i.val).right e)) ^ 2 := by
  obtain ⟨q, hq, Q, hpoint, hcurve, charts, finiteFaces, hdual⟩ :=
    source_deleted_dual_path_of_bond_cycle @FiniteAvalanches.External.finite_plane_dual_bond_cycle
      D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨_dualDrawing, _dualCharts, _vertexFaces, _hpoint, _hvertex, _hcross,
    _hparts, _hlocal, _horient, _Hstar, _hsp, _hsc,
    m, hm, vertices, hinj, copies, hpath, hmarked⟩ := hdual
  refine ⟨q, hq, Q, hpoint, hcurve, charts, finiteFaces,
    m, hm, vertices, hinj, copies, hpath, hmarked, ?_, ?_⟩
  · exact source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      @FiniteAvalanches.External.finite_plane_dual_connected
      @FiniteAvalanches.External.finite_plane_dual_bond_cycle
  · dsimp only
    intro i hi0 him
    exact original_split_analytic D P hD hDc hP marked Q charts
      vertices hinj copies hpath hmarked i hi0 him

end
end FiniteAvalanches.Electrical.SplitStep
