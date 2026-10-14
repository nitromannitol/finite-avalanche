import FiniteAvalanchesCurrent.ArcMomentV7
import FiniteAvalanches.Electrical.Source.BoundaryExpectation

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.CurrentSourceRoots
open LatticeProb
open FiniteAvalanches.Electrical.LatticeDrawing
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical BigOperators
noncomputable section

/-- The original forest variance bound with literal dual-tree indicator expectations. -/
theorem arc_variance_expectations :
  ∀ (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P),
  let a := copyA D P marked
  let b := copyB D P marked
  let J0 := StatementTypes.graph D P marked
  let F := J0.RootedForest ({alpha D P, beta D P} : Set (Vertex D P))
  letI : Nonempty F := Repair8.forest_nonempty D P hD marked
  let Y : F → ℝ := fun f => ∑ z : Plane.Dart (Copy D P marked),
    if Plane.tail a b z = alpha D P ∧ J0.reaches f.val (Plane.head a b z) (beta D P)
    then 1 else 0
  let mean := (∑ f : F, Y f)/(Fintype.card F : ℝ)
  let variance := (∑ f : F, (Y f-mean)^2)/(Fintype.card F : ℝ)
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
            letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
            variance ≤ mean + 3 * ∑ k : Fin m,
              ((∑ T : J.SpanningTree,
                J.pathIndicator T (vertices 0) (vertices (Fin.last m)) (copies k).val) /
                (Fintype.card J.SpanningTree : ℝ)) *
              (G (vertices k.castSucc) (vertices k.castSucc) -
                G (vertices 0) (vertices k.castSucc) +
                G (vertices k.succ) (vertices k.succ) - G (vertices 0) (vertices k.succ))) := by
  intro D P hD hDc hP marked a b J0 F Y mean variance
  obtain ⟨hgeometry, hbound⟩ := arc_variance D P hD hDc hP marked
  refine ⟨hgeometry, ?_⟩
  intro q hq Q hpoint hcurve charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends hmarked
  let J := sourceDeletedDualGraph D P marked Q charts
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  have h := hbound q hq Q hpoint hcurve charts finiteFaces
    m vertices hinj copies hends hmarked
  dsimp only at h ⊢
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  have hmean := (original_boundary_expectation D P hD hDc hP marked Q charts
    vertices hinj copies hends hmarked k).1
  rw [hmean]

end
end FiniteAvalanches.Electrical.CurrentSourceRoots
