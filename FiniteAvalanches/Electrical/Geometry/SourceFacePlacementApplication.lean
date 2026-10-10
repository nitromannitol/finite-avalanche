import FiniteAvalanches.Electrical.Geometry.SourceMarkedFace
import FiniteAvalanches.Electrical.Reference.Connected

/-! Conditional placement of the actual source drawing and its marked common face. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source (Plane drawingTrace EdgeChart OuterArc)
open FiniteAvalanches.Electrical.BSST (Face faceRegion incident)
open FiniteAvalanches.Electrical.DrawingContraction (restrictDrawing)
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical
noncomputable section

/-- The full source drawing places its marked common face outside, conditional
on the exact generic punctured-plane face placement assertion. -/
theorem actual_outer_arc_of_generic_face_placement
    (hplace :
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
      let R := deleteMarkedDrawing D P marked Q
      ∃ F : Face R, ∃ p : Plane, ∃ hp : p ∉ drawingTrace Q,
        p ∈ faceRegion R F ∧
        ∃ c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)},
          (∀ z : {z : Plane // z ≠ p},
            (c z).val =
              ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
               -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) ∧
          ∃ Q' : Drawing (primalGraph D P),
            (∀ v, Q'.point v = (c ⟨Q.point v, by
              intro heq
              apply hp
              exact heq ▸ (Or.inl (Set.mem_range_self v) :
                Q.point v ∈ drawingTrace Q)⟩).val) ∧
            (∀ e t, Q'.curve e t = (c ⟨Q.curve e t, by
              intro heq
              apply hp
              exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
                Q.curve e t ∈ drawingTrace Q)⟩).val) ∧
            let R' := deleteMarkedDrawing D P marked Q'
            ∃ faces : Face R ≃ Face R',
              (∀ G : Face R, ∀ z : {z : Plane // z ≠ p},
                z.val ∈ faceRegion R G ↔ (c z).val ∈ faceRegion R' (faces G)) ∧
              (∀ G : Face R, ∀ z : {z : Plane // z ≠ p},
                z.val ∈ closure (faceRegion R G) ↔
                  (c z).val ∈ closure (faceRegion R' (faces G))) ∧
              (∀ G : Face R, ∀ v : Vertex D P,
                incident R v G ↔ incident R' v (faces G)) ∧
              (∀ e : PrimalCopy D P, ∀ S : Set ArcParameter, ∀ t : ArcParameter,
                Q.curve e t ∈ closure (Q.curve e '' S) ↔
                  Q'.curve e t ∈ closure (Q'.curve e '' S)) ∧
              ¬Bornology.IsBounded (faceRegion R' (faces F)) ∧
              (∀ e t, R'.curve e t = Q'.curve (retainedPrimal D P marked e) t) ∧
              (∀ t : ArcParameter, 0 < t.val → t.val < 1 →
                Q'.curve (markedPrimal D P marked) t ∉ drawingTrace R') ∧
              (∀ t : ArcParameter, 0 < t.val → t.val < 1 →
                Q'.curve (markedPrimal D P marked) t ∈ faceRegion R' (faces F)) ∧
              Set.range (Q'.curve (markedPrimal D P marked)) ⊆
                closure (faceRegion R' (faces F)) ∧
              incident R' (alpha D P) (faces F) ∧ incident R' (beta D P) (faces F) ∧
              (∀ G : Face R',
                (∀ t : ArcParameter, 0 < t.val → t.val < 1 →
                  Q'.curve (markedPrimal D P marked) t ∈ faceRegion R' G) →
                G = faces F) ∧
              (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
                Q'.curve (markedPrimal D P marked) ⟨0, by constructor <;> norm_num⟩ ∈
                  closure (Q'.curve (markedPrimal D P marked) ''
                    {t : ArcParameter | 0 < t.val ∧ t.val < epsilon}) ∧
                Q'.curve (markedPrimal D P marked) ⟨1, by constructor <;> norm_num⟩ ∈
                  closure (Q'.curve (markedPrimal D P marked) ''
                    {t : ArcParameter | 1 - epsilon < t.val ∧ t.val < 1}) ∧
                Q'.curve (markedPrimal D P marked) ''
                    {t : ArcParameter | 0 < t.val ∧ t.val < epsilon} ⊆
                  faceRegion R' (faces F) ∧
                Q'.curve (markedPrimal D P marked) ''
                    {t : ArcParameter | 1 - epsilon < t.val ∧ t.val < 1} ⊆
                  faceRegion R' (faces F)) ∧
              (supportGraph (copyA D P marked) (copyB D P marked)).Connected ∧
              ∃ charts : ∀ e, EdgeChart R' e,
                ∃ O : OuterArc (ChartExistence.planeEmbeddingOfCharts R'
                    (copy_loopless D P marked) charts) (alpha D P) (beta D P),
                  O.face = faces F := by
  obtain ⟨q, hq, Q, hqp, hqc, Q0, hQ0, F0, _, hF0, hcl0, ha0, hb0, hu0, hg0⟩ :=
    source_marked_common_face D P hDc hP marked
  have original : ∃ F : Face Q0.drawing,
      (∀ t : ArcParameter, 0 < t.val → t.val < 1 →
        Q.curve (markedPrimal D P marked) t ∈ faceRegion Q0.drawing F) ∧
      Set.range (Q.curve (markedPrimal D P marked)) ⊆ closure (faceRegion Q0.drawing F) ∧
      incident Q0.drawing (alpha D P) F ∧ incident Q0.drawing (beta D P) F ∧
      (∀ G : Face Q0.drawing,
        (∀ t : ArcParameter, 0 < t.val → t.val < 1 →
          Q.curve (markedPrimal D P marked) t ∈ faceRegion Q0.drawing G) → G = F) ∧
      (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        Q.curve (markedPrimal D P marked) ⟨0, by constructor <;> norm_num⟩ ∈
          closure (Q.curve (markedPrimal D P marked) ''
            {t : ArcParameter | 0 < t.val ∧ t.val < epsilon}) ∧
        Q.curve (markedPrimal D P marked) ⟨1, by constructor <;> norm_num⟩ ∈
          closure (Q.curve (markedPrimal D P marked) ''
            {t : ArcParameter | 1 - epsilon < t.val ∧ t.val < 1}) ∧
        Q.curve (markedPrimal D P marked) ''
            {t : ArcParameter | 0 < t.val ∧ t.val < epsilon} ⊆ faceRegion Q0.drawing F ∧
        Q.curve (markedPrimal D P marked) ''
            {t : ArcParameter | 1 - epsilon < t.val ∧ t.val < 1} ⊆ faceRegion Q0.drawing F) :=
    ⟨F0, hF0, hcl0, ha0, hb0, hu0, hg0⟩
  rw [hQ0] at original
  obtain ⟨F, hF, hcl, ha, hb, hunique, hg⟩ := original
  let R := deleteMarkedDrawing D P marked Q
  obtain ⟨p, hp, hpF, c, hc, Q', hpoint, hcurve, faces, hregion, hclosure,
    hincident, hcurveClosure, hunbounded⟩ :=
    hplace (primalGraph D P)
      (⟨copyA D P marked, copyB D P marked⟩ :
        CopiedGraph (Vertex D P) (Copy D P marked)) Q
      (retainedPrimal D P marked) (retainedPrimal_injective D P marked)
      (fun _ => rfl) (fun _ => rfl) F
  let R' := deleteMarkedDrawing D P marked Q'
  have curve_ne (e : PrimalCopy D P) (t : ArcParameter) : Q.curve e t ≠ p := by
    intro heq
    apply hp
    exact heq ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
      Q.curve e t ∈ drawingTrace Q)
  have hmarked (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
      Q'.curve (markedPrimal D P marked) t ∈ faceRegion R' (faces F) := by
    rw [hcurve]
    exact (hregion F ⟨Q.curve (markedPrimal D P marked) t,
      curve_ne _ t⟩).mp (hF t ht0 ht1)
  have hmarkedClosure : Set.range (Q'.curve (markedPrimal D P marked)) ⊆
      closure (faceRegion R' (faces F)) := by
    rintro z ⟨t, rfl⟩
    rw [hcurve]
    exact (hclosure F ⟨Q.curve (markedPrimal D P marked) t,
      curve_ne _ t⟩).mp (hcl (Set.mem_range_self t))
  have ha' : incident R' (alpha D P) (faces F) := (hincident F _).mp ha
  have hb' : incident R' (beta D P) (faces F) := (hincident F _).mp hb
  have hunique' (G : Face R')
      (hG : ∀ t : ArcParameter, 0 < t.val → t.val < 1 →
        Q'.curve (markedPrimal D P marked) t ∈ faceRegion R' G) : G = faces F := by
    obtain ⟨G0, rfl⟩ := faces.surjective G
    apply congrArg faces
    apply hunique
    intro t ht0 ht1
    apply (hregion G0 ⟨Q.curve (markedPrimal D P marked) t, curve_ne _ t⟩).mpr
    rw [← hcurve]
    exact hG t ht0 ht1
  have hconnected := Repair8.graph_connected D P hD marked
  have hne : alpha D P ≠ beta D P := Sum.inl_injective.ne (by decide)
  obtain ⟨charts, O, hO⟩ := ChartExistence.source_outer_arc_of_unbounded_face
    (⟨copyA D P marked, copyB D P marked⟩ :
      CopiedGraph (Vertex D P) (Copy D P marked)) R'
    (copy_loopless D P marked) hconnected.preconnected
    (alpha D P) (beta D P) hne (faces F) ha' hb' hunbounded
  refine ⟨q, hq, Q, hqp, hqc, F, p, hp, hpF, c, hc, Q', hpoint, hcurve,
    faces, hregion, hclosure, hincident, hcurveClosure, hunbounded,
    (fun _ _ => rfl), ?_, hmarked, hmarkedClosure, ha', hb', hunique', ?_,
    hconnected, charts, O, hO⟩
  · intro t ht0 ht1
    exact DeletedArc.omitted_interior_off_trace Q' (retainedPrimal D P marked)
      (retainedPrimal_injective D P marked) (fun _ => rfl) (fun _ => rfl)
      (markedPrimal D P marked) (retainedPrimal_ne_marked D P marked) t ht0 ht1
  · intro epsilon he0 he1
    obtain ⟨hgStart, hgFinish, hgStartFace, hgFinishFace⟩ := hg epsilon he0 he1
    refine ⟨(hcurveClosure _ _ _).mp hgStart, (hcurveClosure _ _ _).mp hgFinish,
      ?_, ?_⟩
    · rintro z ⟨t, ht, rfl⟩
      rw [hcurve]
      exact (hregion F ⟨Q.curve (markedPrimal D P marked) t, curve_ne _ t⟩).mp
        (hgStartFace ⟨t, ht, rfl⟩)
    · rintro z ⟨t, ht, rfl⟩
      rw [hcurve]
      exact (hregion F ⟨Q.curve (markedPrimal D P marked) t, curve_ne _ t⟩).mp
        (hgFinishFace ⟨t, ht, rfl⟩)

end
end FiniteAvalanches.Electrical.LatticeDrawing
