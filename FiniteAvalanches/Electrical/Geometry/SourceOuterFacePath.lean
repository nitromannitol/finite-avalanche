import FiniteAvalanches.Electrical.Geometry.PunctureTransport

/-! Full-H dual redrawing with the entire retained alpha-star path on an unbounded face. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Electrical.DrawingContraction
open FiniteAvalanches.Electrical.PunctureTransport
open scoped Classical
noncomputable section

/-- Redraw the full geometric dual, then delete only the marked original dual copy.
All retained alpha-star curves and path vertices lie on one actual unbounded face.
The three displayed closed generic antecedents remain unregistered. -/
theorem source_outer_face_path_of_closed_classical_inputs
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
    (hpuncture :
∀ {V E E₀ : Type} [Fintype V] [Fintype E] [Fintype E₀]
    (J : CopiedGraph V E) (K : CopiedGraph V E₀) (D : Drawing J)
    (i : E₀ → E) (hi : Function.Injective i)
    (hl : ∀ e, J.left (i e) = K.left e)
    (hr : ∀ e, J.right (i e) = K.right e)
    (F : Face (restrictDrawing D i hi hl hr)),
  let R := restrictDrawing D i hi hl hr
  ∃ p : Plane, ∃ hp : p ∉ drawingTrace D,
    p ∈ faceRegion R F ∧
    ∃ c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)},
      (∀ z : {z : Plane // z ≠ p},
        (c z).val =
          ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
           -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) ∧
      ∃ D' : Drawing J,
        (∀ v, D'.point v = (c ⟨D.point v, by
          intro heq
          apply hp
          exact heq ▸ (Or.inl (Set.mem_range_self v) : D.point v ∈ drawingTrace D)⟩).val) ∧
        (∀ e t, D'.curve e t = (c ⟨D.curve e t, by
          intro heq
          apply hp
          exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
            D.curve e t ∈ drawingTrace D)⟩).val) ∧
        let R' := restrictDrawing D' i hi hl hr
        ∃ faces : Face R ≃ Face R',
          (∀ G : Face R, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ faceRegion R G ↔ (c z).val ∈ faceRegion R' (faces G)) ∧
          (∀ G : Face R, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ closure (faceRegion R G) ↔
              (c z).val ∈ closure (faceRegion R' (faces G))) ∧
          (∀ G : Face R, ∀ v : V, incident R v G ↔ incident R' v (faces G)) ∧
          (∀ e : E, ∀ S : Set ArcParameter, ∀ t : ArcParameter,
            D.curve e t ∈ closure (D.curve e '' S) ↔
              D'.curve e t ∈ closure (D'.curve e '' S)) ∧
          ¬Bornology.IsBounded (faceRegion R' (faces F)))
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
        ∃ fullDual : Drawing (sourceDualGraph D P Q charts),
        ∃ vertexFaces : Vertex D P ≃ Face fullDual,
          (∀ F : Face Q, fullDual.point F ∈ faceRegion Q F) ∧
          (∀ v : Vertex D P, Q.point v ∈ faceRegion fullDual (vertexFaces v)) ∧
          (∀ (e f : PrimalCopy D P) (s t : ArcParameter),
            Q.curve e s = fullDual.curve f t ↔
              e = f ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
        let R := deleteMarkedDualDrawing D P marked Q charts fullDual
        ∃ merged : Face R,
          Q.point (alpha D P) ∈ faceRegion R merged ∧
          Q.point (beta D P) ∈ faceRegion R merged ∧
          Q.point (alpha D P) ∉ drawingTrace fullDual ∧
          Set.range (Q.curve (markedPrimal D P marked)) ⊆ faceRegion R merged ∧
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
          (∀ i : Fin m, Set.range (R.curve (copies i).val) ⊆ frontier (faceRegion R merged)) ∧
          (∀ k : Fin (m + 1), R.point (vertices k) ∈ frontier (faceRegion R merged)) ∧
        ∃ p : Plane, ∃ hp : p ∉ drawingTrace fullDual,
          p ∈ faceRegion R merged ∧
        ∃ c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)},
          IsProperMap c ∧
          (∀ z : {z : Plane // z ≠ p},
            (c z).val =
              ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
               -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) ∧
        ∃ redrawn : Drawing (sourceDualGraph D P Q charts),
          (∀ v, redrawn.point v = (c ⟨fullDual.point v, by
            intro heq
            apply hp
            exact heq ▸ (Or.inl (Set.mem_range_self v) : fullDual.point v ∈ drawingTrace fullDual)⟩).val) ∧
          (∀ e t, redrawn.curve e t = (c ⟨fullDual.curve e t, by
            intro heq
            apply hp
            exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
              fullDual.curve e t ∈ drawingTrace fullDual)⟩).val) ∧
        let R' := deleteMarkedDualDrawing D P marked Q charts redrawn
        ∃ faces : Face R ≃ Face R',
          (∀ G : Face R, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ faceRegion R G ↔ (c z).val ∈ faceRegion R' (faces G)) ∧
          (∀ G : Face R, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ closure (faceRegion R G) ↔
              (c z).val ∈ closure (faceRegion R' (faces G))) ∧
          (∀ G : Face R, ∀ z : {z : Plane // z ≠ p},
            z.val ∈ frontier (faceRegion R G) ↔
              (c z).val ∈ frontier (faceRegion R' (faces G))) ∧
          (∀ G : Face R, ∀ v : Face Q, incident R v G ↔ incident R' v (faces G)) ∧
          (∀ e : PrimalCopy D P, ∀ S : Set ArcParameter, ∀ t : ArcParameter,
            fullDual.curve e t ∈ closure (fullDual.curve e '' S) ↔
              redrawn.curve e t ∈ closure (redrawn.curve e '' S)) ∧
          ¬Bornology.IsBounded (faceRegion R' (faces merged)) ∧
          (∀ i : Fin m, Set.range (R'.curve (copies i).val) ⊆
            frontier (faceRegion R' (faces merged))) ∧
          (∀ k : Fin (m + 1), R'.point (vertices k) ∈
            frontier (faceRegion R' (faces merged))) := by
  obtain ⟨q, hq, Q, hp, hc, charts, finiteFaces, hdual⟩ :=
    source_retained_path_frontier_of_classical_incidence hbond hinc D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨fullDual, _, vertexFaces, hpoint, hvertex, hcross, _, _, _,
    Hstar, hsp, hsc, merged, halpha, hbeta, harc, _, _, _,
    m, hm, vertices, hinj, copies, hends, hmarked, hboundary, hvertices⟩ := hdual
  have hrestriction : Hstar = deleteMarkedDualDrawing D P marked Q charts fullDual :=
    drawing_eq_of_points_curves _ _ hsp hsc
  subst Hstar
  have halphaSafe : Q.point (alpha D P) ∉ drawingTrace fullDual := (hvertex _).1
  obtain ⟨p, hpole, hpinside, c, hformula, redrawn, hnewp, hnewc,
    faces, hregions, hclosures, hincidences, hcurveclosures, hunbounded⟩ :=
    hpuncture (sourceDualGraph D P Q charts)
      (sourceDeletedDualGraph D P marked Q charts) fullDual
      (retainedPrimal D P marked) (retainedPrimal_injective D P marked)
      (fun _ => rfl) (fun _ => rfl) merged
  have hfrontier (G) (z : {z : Plane // z ≠ p}) :=
    frontier_transport _ _ G (faces G) z.val (c z).val
      (hregions G z) (hclosures G z)
  have hnewboundary (i : Fin m) :
      Set.range ((deleteMarkedDualDrawing D P marked Q charts redrawn).curve (copies i).val) ⊆
        frontier (faceRegion (deleteMarkedDualDrawing D P marked Q charts redrawn) (faces merged)) := by
    rintro z ⟨t, rfl⟩
    have hoff : fullDual.curve (retainedPrimal D P marked (copies i).val) t ≠ p := by
      intro heq
      apply hpole
      exact heq ▸ (Or.inr (Set.mem_iUnion.mpr
        ⟨retainedPrimal D P marked (copies i).val, Set.mem_range_self t⟩))
    have hb := (hfrontier merged ⟨_, hoff⟩).mp (hboundary i (Set.mem_range_self t))
    change redrawn.curve _ t ∈ _
    rw [hnewc]
    exact hb
  have hnewvertices (k : Fin (m + 1)) :
      (deleteMarkedDualDrawing D P marked Q charts redrawn).point (vertices k) ∈
        frontier (faceRegion (deleteMarkedDualDrawing D P marked Q charts redrawn) (faces merged)) := by
    have hoff : fullDual.point (vertices k) ≠ p := by
      intro heq
      apply hpole
      exact heq ▸ (Or.inl (Set.mem_range_self (vertices k)))
    have hb := (hfrontier merged ⟨_, hoff⟩).mp (hvertices k)
    change redrawn.point (vertices k) ∈ _
    rw [hnewp]
    exact hb
  exact ⟨q, hq, Q, hp, hc, charts, finiteFaces, fullDual, vertexFaces,
    hpoint, hvertex, hcross, merged, halpha, hbeta, halphaSafe, harc,
    m, hm, vertices, hinj, copies, hends, hmarked, hboundary, hvertices,
    p, hpole, hpinside, c, c.isProperMap, hformula, redrawn, hnewp, hnewc,
    faces, hregions, hclosures, hfrontier, hincidences, hcurveclosures,
    hunbounded, hnewboundary, hnewvertices⟩

end
end FiniteAvalanches.Electrical.LatticeDrawing
