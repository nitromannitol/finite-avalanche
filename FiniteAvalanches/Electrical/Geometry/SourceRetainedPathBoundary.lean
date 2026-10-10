import FiniteAvalanches.Electrical.Geometry.SourceDualPath
import FiniteAvalanches.Electrical.Geometry.IncidenceApplication

/-! The actual retained source path and the complement face containing both primal poles. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Electrical.ComplementFaces
open FiniteAvalanches.Electrical.IncidenceApplication
open scoped Classical
noncomputable section

/-- The actual retained alpha-star path lies in the frontier of the actual merged
Hstar face, conditional only on two explicit closed generic classical propositions.
Neither proposition is registered or asserted by this module. -/
theorem source_retained_path_frontier_of_classical_incidence
    (hbond :
∀ {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (Q : Drawing J)
    (charts : ∀ e : E, EdgeChart Q e) (A : Finset V),
  (∀ x y : V, x ∈ A → y ∈ A →
    J.reaches (Finset.univ.filter fun e => J.left e ∈ A ∧ J.right e ∈ A) x y) →
  (∀ x y : V, x ∉ A → y ∉ A →
    J.reaches (Finset.univ.filter fun e => J.left e ∉ A ∧ J.right e ∉ A) x y) →
  ∀ marked : E,
    ((J.left marked ∈ A ∧ J.right marked ∉ A) ∨
      (J.right marked ∈ A ∧ J.left marked ∉ A)) →
  ∃ m : ℕ, ∃ vertices : Fin (m + 1) → Face Q,
    Function.Injective vertices ∧
    ∃ copies : Fin m ≃ {e : E // e ≠ marked ∧
      ((J.left e ∈ A ∧ J.right e ∉ A) ∨ (J.right e ∈ A ∧ J.left e ∉ A))},
      m + 1 = (Finset.univ.filter fun e : E =>
        (J.left e ∈ A ∧ J.right e ∉ A) ∨ (J.right e ∈ A ∧ J.left e ∉ A)).card ∧
      (∀ i : Fin m,
        (negativeChartFace Q (copies i).val (charts (copies i).val) = vertices i.castSucc ∧
          positiveChartFace Q (copies i).val (charts (copies i).val) = vertices i.succ) ∨
        (positiveChartFace Q (copies i).val (charts (copies i).val) = vertices i.castSucc ∧
          negativeChartFace Q (copies i).val (charts (copies i).val) = vertices i.succ)) ∧
      ((negativeChartFace Q marked (charts marked) = vertices 0 ∧
          positiveChartFace Q marked (charts marked) = vertices (Fin.last m)) ∨
        (positiveChartFace Q marked (charts marked) = vertices 0 ∧
          negativeChartFace Q marked (charts marked) = vertices (Fin.last m))))
    (hinc :
∀ {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (R : Drawing J) (e : E) (c : EdgeChart R e),
  J.left e ≠ J.right e →
  Set.range (R.curve e) ⊆ closure (faceRegion R (positiveChartFace R e c)) ∧
  Set.range (R.curve e) ⊆ closure (faceRegion R (negativeChartFace R e c)))
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
            (∀ e t, Hstar.curve e t = dualDrawing.curve (retainedPrimal D P marked e) t) ∧
            ∃ merged : Face Hstar,
              Q.point (alpha D P) ∈ faceRegion Hstar merged ∧
              Q.point (beta D P) ∈ faceRegion Hstar merged ∧
              Set.range (Q.curve (markedPrimal D P marked)) ⊆ faceRegion Hstar merged ∧
              faceRegion dualDrawing (vertexFaces (alpha D P)) ⊆ faceRegion Hstar merged ∧
              faceRegion dualDrawing (vertexFaces (beta D P)) ⊆ faceRegion Hstar merged ∧
              (∀ face : Face Hstar,
                Q.point (alpha D P) ∈ faceRegion Hstar face → face = merged) ∧
            ∃ m : ℕ, 3 ≤ m ∧ ∃ vertices : Fin (m + 1) → Face Q,
              Function.Injective vertices ∧
              ∃ copies : Fin m ≃ {e : Copy D P marked //
                copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P},
                (∀ i : Fin m,
                  ((sourceDeletedDualGraph D P marked Q charts).left (copies i).val = vertices i.castSucc ∧
                    (sourceDeletedDualGraph D P marked Q charts).right (copies i).val = vertices i.succ) ∨
                  ((sourceDeletedDualGraph D P marked Q charts).right (copies i).val = vertices i.castSucc ∧
                    (sourceDeletedDualGraph D P marked Q charts).left (copies i).val = vertices i.succ)) ∧
                (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
                    (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
                  ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
                    (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) ∧
                (∀ i : Fin m, Set.range (Hstar.curve (copies i).val) ⊆
                  frontier (faceRegion Hstar merged)) ∧
                (∀ k : Fin (m + 1), Hstar.point (vertices k) ∈
                  frontier (faceRegion Hstar merged)) := by
  obtain ⟨q, hq, Q, hp, hc, charts, finiteFaces, hdual⟩ :=
    source_path_face_merger_of_bond_cycle hbond D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨dualDrawing, dualCharts, vertexFaces, hpoint, hvertex, hcross,
    hparts, hlocal, horient, Hstar, hsp, hsc,
    merged, halpha, hbeta, harc, hregionAlpha, hregionBeta, hunique,
    m, hm, vertices, hinj, copies, hends, hmarked⟩ := hdual
  have hboundary (i : Fin m) : Set.range (Hstar.curve (copies i).val) ⊆
      frontier (faceRegion Hstar merged) := by
    have hne := path_copy_nonloop m vertices hinj (fun j => (copies j).val) hends i
    have hnfull : (sourceDualGraph D P Q charts).left
        (retainedPrimal D P marked (copies i).val) ≠
      (sourceDualGraph D P Q charts).right
        (retainedPrimal D P marked (copies i).val) := hne
    obtain ⟨hpositive, hnegative⟩ := hinc (sourceDualGraph D P Q charts) dualDrawing
      (retainedPrimal D P marked (copies i).val)
      (dualCharts (retainedPrimal D P marked (copies i).val)) hnfull
    have hwhole : Set.range (dualDrawing.curve
        (retainedPrimal D P marked (copies i).val)) ⊆
        closure (faceRegion dualDrawing (vertexFaces (alpha D P))) := by
      rcases (copies i).property with ha | hb
      · rw [(horient _).1] at hpositive
        change Set.range (dualDrawing.curve _) ⊆
          closure (faceRegion dualDrawing (vertexFaces (copyA D P marked (copies i).val)))
          at hpositive
        rw [ha] at hpositive
        exact hpositive
      · rw [(horient _).2] at hnegative
        change Set.range (dualDrawing.curve _) ⊆
          closure (faceRegion dualDrawing (vertexFaces (copyB D P marked (copies i).val)))
          at hnegative
        rw [hb] at hnegative
        exact hnegative
    rintro z ⟨t, rfl⟩
    apply mem_frontier_of_mem_trace Hstar merged _
    · exact Or.inr (Set.mem_iUnion.mpr ⟨(copies i).val, Set.mem_range_self t⟩)
    · rw [hsc]
      exact closure_mono hregionAlpha (hwhole (Set.mem_range_self t))
  have hvertices := path_vertices_mem_frontier Hstar merged m (by omega)
    vertices (fun i => (copies i).val) hends hboundary
  exact ⟨q, hq, Q, hp, hc, charts, finiteFaces, dualDrawing, dualCharts, vertexFaces,
    hpoint, hvertex, hcross, hparts, hlocal, horient, Hstar, hsp, hsc,
    merged, halpha, hbeta, harc, hregionAlpha, hregionBeta, hunique,
    m, hm, vertices, hinj, copies, hends, hmarked, hboundary, hvertices⟩

end
end FiniteAvalanches.Electrical.LatticeDrawing
