import FiniteAvalanches.Electrical.Geometry.SourceMarkedFace
import FiniteAvalanches.Electrical.Reference.Connected
import FiniteAvalanches.Electrical.Reference.CutConnectivity
import FiniteAvalanches.External.GeometricDual

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.DrawingContraction
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical
noncomputable section

/-- The retained original IDs are exactly all primal copies except the marked ID. -/
def retainedPrimalEquiv (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) :
    Copy D P marked ≃ {e : PrimalCopy D P // e ≠ markedPrimal D P marked} where
  toFun e := ⟨retainedPrimal D P marked e, retainedPrimal_ne_marked D P marked e⟩
  invFun e := ⟨e.val.val, Finset.mem_filter.mpr ⟨
    (Finset.mem_filter.mp e.val.property).1,
    (Finset.mem_filter.mp e.val.property).2,
    fun h => e.property (Subtype.ext h)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem retainedPrimal_covers (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (e : PrimalCopy D P) :
    (∃ f : Copy D P marked, retainedPrimal D P marked f = e) ↔
      e ≠ markedPrimal D P marked := by
  constructor
  · rintro ⟨f, rfl⟩
    exact retainedPrimal_ne_marked D P marked f
  · intro he
    exact ⟨(retainedPrimalEquiv D P marked).symm ⟨e, he⟩,
      congrArg Subtype.val ((retainedPrimalEquiv D P marked).apply_symm_apply ⟨e, he⟩)⟩

theorem primal_loopless (D : Finset (Site 2)) (P : OneSet D)
    (e : PrimalCopy D P) : (primalGraph D P).left e ≠ (primalGraph D P).right e :=
  (Finset.mem_filter.mp e.property).2

/-- H0 walks lift copy by copy into H on the same complete vertex carrier. -/
theorem primal_reaches_of_domain_connected (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (x y : Vertex D P) :
    (FiniteAvalanches.Electrical.Plane.SourceLattice.primalGraph D P).reaches Finset.univ x y := by
  have h := Repair8.graph_reaches D P hD marked x y
  induction h with
  | refl => exact .refl
  | @tail u v _ hadj ih =>
    obtain ⟨e, _, hends⟩ := hadj
    exact ih.tail ⟨retainedPrimal D P marked e, Finset.mem_univ _, hends⟩

theorem primal_preconnected (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    (supportGraph (primalGraph D P).left (primalGraph D P).right).Preconnected :=
  (FiniteAvalanches.Electrical.Plane.SourceLattice.primalGraph D P).supportGraph_preconnected_of_reaches
    (primal_reaches_of_domain_connected D P hD marked)

/-- The full dual uses the actual complement faces of H and every original H copy. -/
def sourceDualGraph (D : Finset (Site 2)) (P : OneSet D)
    (Q : Drawing (primalGraph D P)) (charts : ∀ e, EdgeChart Q e) :
    CopiedGraph (Face Q) (PrimalCopy D P) :=
  ⟨fun e => negativeChartFace Q e (charts e),
    fun e => positiveChartFace Q e (charts e)⟩

/-- Only the marked original dual copy is omitted; no face vertex is removed or merged. -/
def sourceDeletedDualGraph (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) : CopiedGraph (Face Q) (Copy D P marked) :=
  ⟨fun e => (sourceDualGraph D P Q charts).left (retainedPrimal D P marked e),
    fun e => (sourceDualGraph D P Q charts).right (retainedPrimal D P marked e)⟩

def deleteMarkedDualDrawing (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) [Fintype (Face Q)]
    (dualDrawing : Drawing (sourceDualGraph D P Q charts)) :
    Drawing (sourceDeletedDualGraph D P marked Q charts) :=
  restrictDrawing dualDrawing (retainedPrimal D P marked)
    (retainedPrimal_injective D P marked) (fun _ => rfl) (fun _ => rfl)

/-- Construct the dual of H itself, then delete only its marked original dual copy. -/
theorem source_H_deleted_dual_realization (D : Finset (Site 2)) (P : OneSet D)
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
        ∃ dualDrawing : Drawing (sourceDualGraph D P Q charts),
        ∃ dualCharts : ∀ e, EdgeChart dualDrawing e,
        ∃ vertexFaces : Vertex D P ≃ Face dualDrawing,
          (∀ F : Face Q, dualDrawing.point F ∈ faceRegion Q F) ∧
          (∀ v : Vertex D P, Q.point v ∈ faceRegion dualDrawing (vertexFaces v)) ∧
          (∀ (e f : PrimalCopy D P) (s t : ArcParameter),
            Q.curve e s = dualDrawing.curve f t ↔
              e = f ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
          (∀ (e : PrimalCopy D P) (t : ArcParameter),
            (t.val < 1 / 2 → dualDrawing.curve e t ∈
              faceRegion Q ((sourceDualGraph D P Q charts).left e)) ∧
            (1 / 2 < t.val → dualDrawing.curve e t ∈
              faceRegion Q ((sourceDualGraph D P Q charts).right e))) ∧
          (∀ e : PrimalCopy D P, ∃ radius : ℝ, 0 < radius ∧
            radius < (charts e).radius ∧ ∀ t : ArcParameter,
              |t.val - 1 / 2| < radius →
              (charts e).chart.map (dualDrawing.curve e t) = (1 / 2, t.val - 1 / 2)) ∧
          (∀ e : PrimalCopy D P,
            positiveChartFace dualDrawing e (dualCharts e) = vertexFaces ((primalGraph D P).left e) ∧
            negativeChartFace dualDrawing e (dualCharts e) = vertexFaces ((primalGraph D P).right e)) ∧
          ∃ Hstar : Drawing (sourceDeletedDualGraph D P marked Q charts),
            (∀ F : Face Q, Hstar.point F = dualDrawing.point F) ∧
            (∀ e t, Hstar.curve e t = dualDrawing.curve (retainedPrimal D P marked e) t) := by
  obtain ⟨q, hq, Q, hp, hc⟩ := source_primal_realization D P hDc hP marked
  obtain ⟨charts⟩ := ChartExistence.consume_arc_straightening
    FiniteAvalanches.External.parametrized_plane_arc_straightening Q (primal_loopless D P)
  letI : Nonempty (PrimalCopy D P) := ⟨markedPrimal D P marked⟩
  obtain ⟨finiteFaces, hdual⟩ := FiniteAvalanches.External.finite_plane_geometric_dual
    (primalGraph D P) Q charts (primal_preconnected D P hD marked)
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨dualDrawing, dualCharts, vertexFaces, hpoint, hvertex, hcross, hparts, hlocal, horient⟩ := hdual
  exact ⟨q, hq, Q, hp, hc, charts, finiteFaces, dualDrawing, dualCharts, vertexFaces,
    hpoint, hvertex, hcross, hparts, hlocal, horient,
    deleteMarkedDualDrawing D P marked Q charts dualDrawing, fun _ => rfl, fun _ _ => rfl⟩

end
end FiniteAvalanches.Electrical.LatticeDrawing
