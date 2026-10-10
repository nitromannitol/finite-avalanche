import FiniteAvalanches.Electrical.Geometry.SourceOuterFacePath

/-! Actual bare-source consumer with all original retained IDs and the whole path trace. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Electrical.DrawingContraction
open scoped Classical
noncomputable section

/-- Consume the actual source redrawing and expose the entire path trace on the
boundary of its actual unbounded complementary component. All three closed
classical antecedents remain explicit; no geometric source premise is supplied. -/
theorem actual_source_outer_face_path
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
      let R := deleteMarkedDualDrawing D P marked Q charts fullDual
      ∃ merged : Face R,
        Q.point (alpha D P) ∈ faceRegion R merged ∧
        Q.point (beta D P) ∈ faceRegion R merged ∧
        Q.point (alpha D P) ∉ drawingTrace fullDual ∧
        Set.range (Q.curve (markedPrimal D P marked)) ⊆ faceRegion R merged ∧
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
          (Set.range (fun k => R'.point (vertices k)) ∪
            ⋃ i : Fin m, Set.range (R'.curve (copies i))) ⊆
              frontier (faceRegion R' (faces merged)) ∧
          (∀ e : Copy D P marked,
            copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P →
              Set.range (R'.curve e) ⊆ frontier (faceRegion R' (faces merged))) ∧
          (∀ k : Fin (m + 1), R'.point (vertices k) ∈
            frontier (faceRegion R' (faces merged))) := by
  obtain ⟨q, hq, Q, hp, hc, charts, finiteFaces, hdual⟩ :=
    source_outer_face_path_of_closed_classical_inputs hbond hinc hpuncture D P hD hDc hP marked
  letI : Fintype (Face Q) := finiteFaces
  obtain ⟨fullDual, _, _, _, _, merged, halpha, hbeta, halphaSafe, harc,
    m, hm, vertices, hinj, edges, hends, hmarked, _, _,
    p, hpole, hpinside, c, hproper, hformula, redrawn, hnewp, hnewc,
    faces, hregions, hclosures, hfrontier, hincidences, hcurveclosures,
    hunbounded, hboundary, hvertices⟩ := hdual
  refine ⟨q, hq, Q, hp, hc, charts, finiteFaces, fullDual,
    merged, halpha, hbeta, halphaSafe, harc,
    p, hpole, hpinside, c, hproper, hformula, redrawn, hnewp, hnewc,
    faces, hregions, hclosures, hfrontier, hincidences, hcurveclosures, hunbounded,
    m, hm, vertices, hinj, (fun i => (edges i).val), ?_, ?_, hends, ?_, hmarked,
    ?_, ?_, hvertices⟩
  · intro i j h
    apply edges.injective
    exact Subtype.ext (Subtype.ext h)
  · intro e
    constructor
    · rintro ⟨i, rfl⟩
      exact (edges i).property
    · intro he
      obtain ⟨i, hi⟩ := edges.surjective ⟨e, he⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  · intro i
    exact (Finset.mem_filter.mp (edges i).val.property).2.2
  · intro z hz
    rcases hz with ⟨k, rfl⟩ | hz
    · exact hvertices k
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact hboundary i hi
  · intro e he
    obtain ⟨i, hi⟩ := edges.surjective ⟨e, he⟩
    have heq : (edges i).val = e := congrArg Subtype.val hi
    rw [← heq]
    exact hboundary i

end
end FiniteAvalanches.Electrical.LatticeDrawing
