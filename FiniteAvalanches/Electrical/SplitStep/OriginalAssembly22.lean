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

/-- Bare source data construct the exact geometry in the split statement. -/
theorem original_split_geometry22 :
  ∀ (D : Finset (Site 2)) (P : OneSet D)
    (_hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (_hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (_hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
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
              (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m)))) := by
  intro D P hD hDc hP marked
  obtain ⟨q, hq, Q, hpoint, hcurve, charts, finiteFaces, hdual⟩ :=
    source_deleted_dual_path_of_bond_cycle
      @FiniteAvalanches.External.finite_plane_dual_bond_cycle D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨_dualDrawing, _dualCharts, _vertexFaces, _hpoint, _hvertex, _hcross,
    _hparts, _hlocal, _horient, _Hstar, _hsp, _hsc,
    m, _hm, vertices, hinj, copies, hpath, hmarked⟩ := hdual
  exact ⟨q, hq, Q, hpoint, hcurve, charts, finiteFaces,
    m, vertices, hinj, copies, hpath, hmarked⟩

/-- Internal composition conditional on the two entire still-open original electrical statements. -/
theorem internal_split_of_whole_diagonal_and_trial22
    (hdiagonal :
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
              @FiniteAvalanches.External.finite_plane_dual_connected
              @FiniteAvalanches.External.finite_plane_dual_bond_cycle
            let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
            ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
              G (vertices i) (vertices i) = totalResponse D P hD marked copies i.val)
    (htrial :
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
                      G (vertices 0) (vertices j.succ)))))) :
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
  intro D P hD hDc hP marked
  refine ⟨original_split_geometry22 D P hD hDc hP marked, ?_⟩
  intro q hq Q hpoint hcurve charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hpath hmarked
  dsimp only
  intro i hi0 him j hadjacent
  obtain ⟨f, hf0, hf1, henergy⟩ := htrial D P hD hDc hP marked
    q hq Q hpoint hcurve charts finiteFaces m vertices hinj copies hpath hmarked
    i hi0 him j hadjacent
  have hbound := actual_split_response_sub_original_green_bound D P hD hDc hP marked
    Q charts vertices hinj copies hpath hmarked i f hf0 hf1
  have hdiag := hdiagonal D P hD hDc hP marked
    q hq Q hpoint hcurve charts finiteFaces m vertices hinj copies hpath hmarked i hi0 him
  rw [← hdiag] at hbound
  exact hbound.trans henergy

end
end FiniteAvalanches.Electrical.SplitStep
