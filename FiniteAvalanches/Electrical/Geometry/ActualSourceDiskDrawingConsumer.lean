import FiniteAvalanches.Electrical.Geometry.ActualSourceOuterFaceConsumer
import FiniteAvalanches.Electrical.Geometry.SourceDeletedDualPointwise
import FiniteAvalanches.Electrical.Geometry.BoundaryReflection
import FiniteAvalanches.External.PlaneDualBondCycle
import FiniteAvalanches.External.PlaneEdgeChartIncidence
import FiniteAvalanches.External.PlanePuncturedFaceTransport
import FiniteAvalanches.External.PlaneDualConnected
import FiniteAvalanches.External.OuterFaceRedrawing

/-! A disk drawing of the actual marked-copy-deleted source dual and its boundary path. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical
noncomputable section

/-- Source data alone supply one connected all-face deleted dual, its actual
unbounded-face boundary path, and a drawing of the identical copied graph in
the closed unit disk. The original retained path copies lie wholly on the circle;
their actual vertices have increasing angular coordinates after at most a global reflection. -/
theorem actual_source_deleted_dual_disk_drawing
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    ∃ q : Plane → Plane, Continuous q ∧ ∃ Q : Drawing (primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) ∧
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) ∧
    ∃ charts : ∀ e, EdgeChart Q e,
    ∃ finiteFaces : Fintype (Face Q),
      letI : Fintype (Face Q) := finiteFaces
      ∃ m : ℕ, 3 ≤ m ∧ ∃ vertices : Fin (m + 1) → Face Q,
        Function.Injective vertices ∧ ∃ copies : Fin m → Copy D P marked,
          Function.Injective (fun i => (copies i).val) ∧
          (∀ e : Copy D P marked, (∃ i, copies i = e) ↔
            copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P) ∧
          (∀ i : Fin m,
            ((sourceDeletedDualGraph D P marked Q charts).left (copies i) = vertices i.castSucc ∧
              (sourceDeletedDualGraph D P marked Q charts).right (copies i) = vertices i.succ) ∨
            ((sourceDeletedDualGraph D P marked Q charts).right (copies i) = vertices i.castSucc ∧
              (sourceDeletedDualGraph D P marked Q charts).left (copies i) = vertices i.succ)) ∧
          (∀ i : Fin m, (copies i).val ≠ marked.val) ∧
          (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
            ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) ∧
          (supportGraph (sourceDeletedDualGraph D P marked Q charts).left
            (sourceDeletedDualGraph D P marked Q charts).right).Preconnected ∧
          (∀ F G : Face Q,
            (sourceDeletedDualGraph D P marked Q charts).reaches Finset.univ F G) ∧
        ∃ Hstar : Drawing (sourceDeletedDualGraph D P marked Q charts),
        ∃ outerFace : Face Hstar,
          ¬Bornology.IsBounded (faceRegion Hstar outerFace) ∧
          (Set.range (fun k => Hstar.point (vertices k)) ∪
            ⋃ i : Fin m, Set.range (Hstar.curve (copies i))) ⊆
              frontier (faceRegion Hstar outerFace) ∧
        ∃ diskDrawing : Drawing (sourceDeletedDualGraph D P marked Q charts),
          (∀ F : Face Q, diskDrawing.point F ∈ disk) ∧
          (∀ e t, diskDrawing.curve e t ∈ disk) ∧
          (∀ i t, diskDrawing.curve (copies i) t ∈ circle) ∧
          (∀ e : Copy D P marked,
            copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P →
              Set.range (diskDrawing.curve e) ⊆ circle) ∧
        ∃ θ : Fin (m + 1) → ℝ,
          StrictMono θ ∧
          θ (Fin.last m) < θ 0 + 2 * Real.pi ∧
          (∀ k, diskDrawing.point (vertices k) = (Real.cos (θ k), Real.sin (θ k))) := by
  obtain ⟨q, hq, Q, hp, hc, charts, finiteFaces, hdual⟩ :=
    actual_source_outer_face_path
      FiniteAvalanches.External.finite_plane_dual_bond_cycle
      FiniteAvalanches.External.plane_edge_chart_incidence
      FiniteAvalanches.External.plane_punctured_face_transport D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨_fullDual, _merged, _halpha, _hbeta, _halphaSafe, _harc,
    _p, _hpole, _hpinside, _c, _hproper, _hformula, redrawn, _hnewp, _hnewc,
    faces, _hregions, _hclosures, _hfrontier, _hincidences, _hcurveclosures,
    hunbounded, m, hm, vertices, hinj, copies, hcopyinj, hcoverage,
    hends, hnonmarked, hmarked, htrace, _hboundary, _hvertices⟩ := hdual
  let Hstar := deleteMarkedDualDrawing D P marked Q charts redrawn
  have hconn := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
    FiniteAvalanches.External.finite_plane_dual_connected
    FiniteAvalanches.External.finite_plane_dual_bond_cycle
  obtain ⟨rawDisk, hrawPoints, hrawCurves, hrawCircle⟩ :=
    FiniteAvalanches.External.outer_face_simple_path_disk_redrawing
      (sourceDeletedDualGraph D P marked Q charts) Hstar hconn m vertices hinj copies hends
      (faces _merged) hunbounded
      (fun i t => htrace (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_range_self t⟩)))
  obtain ⟨diskDrawing, hreflect, θ, hmono, hspan, hangles⟩ :=
    rawDisk.boundary_path_ordered_angles m (by omega) vertices hinj copies hends hrawCircle
  have hdiskPoints : ∀ F : Face Q, diskDrawing.point F ∈ disk := by
    rcases hreflect with rfl | rfl
    · exact hrawPoints
    · intro F
      exact (reflectPoint_mem_disk _).mpr (hrawPoints F)
  have hdiskCurves : ∀ e t, diskDrawing.curve e t ∈ disk := by
    rcases hreflect with rfl | rfl
    · exact hrawCurves
    · intro e t
      exact (reflectPoint_mem_disk _).mpr (hrawCurves e t)
  have hcircle : ∀ i t, diskDrawing.curve (copies i) t ∈ circle := by
    rcases hreflect with rfl | rfl
    · exact hrawCircle
    · intro i t
      exact (reflectPoint_mem_circle _).mpr (hrawCircle i t)
  refine ⟨q, hq, Q, hp, hc, charts, finiteFaces, m, hm, vertices, hinj, copies,
    hcopyinj, hcoverage, hends, hnonmarked, hmarked, hconn, ?_,
    Hstar, faces _merged, hunbounded, htrace,
    diskDrawing, hdiskPoints, hdiskCurves, hcircle, ?_, θ, hmono, hspan, hangles⟩
  · intro F G
    exact (sourceDeletedDualGraph D P marked Q charts).reaches_univ_of_supportGraph_reachable
      (hconn F G)
  · intro e he
    obtain ⟨i, rfl⟩ := (hcoverage e).mpr he
    rintro z ⟨t, rfl⟩
    exact hcircle i t

end
end FiniteAvalanches.Electrical.LatticeDrawing
