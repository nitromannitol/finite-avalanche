import FiniteAvalanches.Electrical.SplitStep.OriginalSourcePhysicalTrial
import FiniteAvalanches.External.PlanePuncturedChartFaceTransport

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical BigOperators
noncomputable section

/-- Every original drawing and boundary path admits the weighted trial with the source constant. -/
theorem original_whole_weighted_trial :
∀ (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P),
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
                ∃ f : SplitVertex (alpha D P) → ℝ,
                  f (.inr false) = 0 ∧ f (.inr true) = 1 ∧
                  weightedEnergy (actualSplit D P marked copies i.val).left
                    (actualSplit D P marked copies i.val).right
                    (fun x => 1 - splitVoltage D P hD marked x) f ≤
                  1 + 3888 * (1 + Real.log
                    (2 / (G (vertices 0) (vertices j.castSucc) -
                      G (vertices 0) (vertices j.succ))))) := by
  intro D P hD hDc hP marked _q _hq Q _hpoint _hcurve charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends hmarked
  obtain ⟨B, A, faces, _hfaces, _hmarkedSides, psi, _hpsi, _hstream,
    _hgauge, _hbalance, sigma, _hsigma, htrial⟩ := original_source_full_physical_trial
      D P hD hDc hP marked Q charts vertices hinj copies hends hmarked
  dsimp only
  intro i hi0 him j hj
  have hf := htrial i hi0 him j hj
  exact ⟨_, hf.1, hf.2.1, hf.2.2.2.2⟩

end
end FiniteAvalanches.Electrical.SplitStep
