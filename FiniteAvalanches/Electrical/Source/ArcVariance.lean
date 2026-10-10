import FiniteAvalanches.Electrical.Geometry.SourceCompatibleDisk
import FiniteAvalanches.Electrical.Reference.ForestDualMoments
import FiniteAvalanches.Electrical.Green.TreeArcVariance
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Source
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

/-- The source bound on every original drawing and complete boundary path enumeration. -/
theorem arc_variance_on_original_geometry
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) (finiteFaces : Fintype (Face Q)) :
    let F := ReferenceMoment.Forest D P marked
    let mean := ReferenceMoment.forestMean D P marked
    let variance := (∑ f : F, (ReferenceMoment.boundaryContacts D P marked f - mean)^2) /
      (Fintype.card F : ℝ)
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
        let psi := fun k : Fin (m + 1) => G (vertices 0) (vertices k)
        let g := fun k : Fin (m + 1) => G (vertices k) (vertices k)
        let p := fun k : Fin m => psi k.castSucc - psi k.succ
        variance ≤ mean + 3 * ∑ k : Fin m,
          p k * (g k.castSucc - psi k.castSucc + g k.succ - psi k.succ) := by
  intro F mean variance m vertices hinj copies hends hmarked J hc G psi g p
  letI : Fintype (Face Q) := finiteFaces
  letI : Fintype J.SpanningTree := Fintype.ofFinite J.SpanningTree
  obtain ⟨diskDrawing, hpoints, hcurves, hcircle⟩ :=
    source_compatible_path_disk D P hD hDc hP marked Q charts finiteFaces
      m vertices hinj (fun i => (copies i).val) (fun i => (copies i).property) hends
  obtain ⟨hmean, hvariance⟩ := source_forest_variance_transport D P hD marked Q charts
    finiteFaces (Fintype.ofFinite J.SpanningTree) m vertices copies hmarked
  have htree := tree_boundary_arc_variance J diskDrawing hc hpoints hcurves
    m vertices hinj (fun i => (copies i).val) hends hcircle
  change mean = _ at hmean
  change variance = _ at hvariance
  rw [hvariance, hmean]
  exact htree.2

/-- The source variance bound in terms of the full original H0 forest mean. -/
theorem arc_variance :
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
            let psi := fun k : Fin (m + 1) => G (vertices 0) (vertices k)
            let g := fun k : Fin (m + 1) => G (vertices k) (vertices k)
            let p := fun k : Fin m => psi k.castSucc - psi k.succ
            variance ≤ mean + 3 * ∑ k : Fin m,
              p k * (g k.castSucc - psi k.castSucc + g k.succ - psi k.succ)) := by
  intro D P hD hDc hP marked a b J0 F Y mean variance
  constructor
  · obtain ⟨q, hq, Q, hp, hc, charts, finiteFaces, hdual⟩ :=
      source_deleted_dual_path_of_bond_cycle FiniteAvalanches.External.finite_plane_dual_bond_cycle
        D P hD hDc hP marked
    letI : Fintype (Face Q) := finiteFaces
    obtain ⟨_dualDrawing, _dualCharts, _vertexFaces, _hpoint, _hvertex, _hcross,
      _hparts, _hlocal, _horient, _Hstar, _hsp, _hsc,
      m, _hm, vertices, hinj, copies, hends, hmarked⟩ := hdual
    exact ⟨q, hq, Q, hp, hc, charts, finiteFaces, m, vertices, hinj, copies, hends, hmarked⟩
  · intro q _hq Q _hp _hc charts finiteFaces
    exact arc_variance_on_original_geometry D P hD hDc hP marked Q charts finiteFaces

end
end FiniteAvalanches.Electrical.Source
