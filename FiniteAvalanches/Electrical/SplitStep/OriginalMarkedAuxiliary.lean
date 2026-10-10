import FiniteAvalanches.Electrical.SplitStep.ActualEnergy
import FiniteAvalanches.Electrical.Geometry.SourceHDual
import FiniteAvalanches.Electrical.Geometry.PolarDual

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- The added auxiliary ID is exactly the original marked ID. -/
def augmentedOriginalCopyEquiv (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : Copy D P marked ⊕ Unit ≃ LatticeDrawing.PrimalCopy D P :=
  Equiv.ofBijective (Sum.elim (retainedPrimal D P marked) (fun _ => markedPrimal D P marked))
    ⟨by
      intro e f h
      cases e with
      | inl e =>
        cases f with
        | inl f => exact congrArg Sum.inl (retainedPrimal_injective D P marked h)
        | inr f => exact (retainedPrimal_ne_marked D P marked e h).elim
      | inr e =>
        cases f with
        | inl f => exact (retainedPrimal_ne_marked D P marked f h.symm).elim
        | inr f => cases e; cases f; rfl,
      by
        intro e
        by_cases he : e = markedPrimal D P marked
        · exact ⟨.inr (), he.symm⟩
        · obtain ⟨f, hf⟩ := (retainedPrimal_covers D P marked e).mpr he
          exact ⟨.inl f, hf⟩⟩

/-- Only the original marked parameter is reversed when its storage starts at beta. -/
def markedParameter (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : ArcParameter ≃ₜ ArcParameter :=
  if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
    Homeomorph.refl _ else unitInterval.symmHomeomorph

theorem marked_parameter_endpoints (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P)) :
    Q.curve (markedPrimal D P marked) (markedParameter D P marked ⟨0, by norm_num⟩) =
      Q.point (alpha D P) ∧
    Q.curve (markedPrimal D P marked) (markedParameter D P marked ⟨1, by norm_num⟩) =
      Q.point (beta D P) := by
  rcases marked.property with h | h
  · have ha : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P := h.1
    have hb : (LatticeDrawing.primalGraph D P).right (markedPrimal D P marked) = beta D P := h.2
    simp only [markedParameter, if_pos ha, Homeomorph.refl_apply]
    exact ⟨(Q.start _).trans (congrArg Q.point ha),
      (Q.finish _).trans (congrArg Q.point hb)⟩
  · have hb : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = beta D P := h.1
    have ha : (LatticeDrawing.primalGraph D P).right (markedPrimal D P marked) = alpha D P := h.2
    have hn : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) ≠ alpha D P := by
      rw [hb]; intro he; cases he
    simp only [markedParameter, if_neg hn]
    change Q.curve _ (unitInterval.symm 0) = _ ∧ Q.curve _ (unitInterval.symm 1) = _
    rw [unitInterval.symm_zero, unitInterval.symm_one]
    exact ⟨(Q.finish _).trans (congrArg Q.point ha),
      (Q.start _).trans (congrArg Q.point hb)⟩

theorem marked_parameter_interior (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    0 < (markedParameter D P marked t).val ∧
      (markedParameter D P marked t).val < 1 := by
  unfold markedParameter
  split
  · exact ⟨ht0, ht1⟩
  · change 0 < 1 - t.val ∧ 1 - t.val < 1
    constructor <;> linarith only [ht0, ht1]

/-- The original full drawing, relabelled as H0 plus its own marked auxiliary arc. -/
def originalAugmentedDrawing (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P)) :
    Drawing (augmentedGraph (originalGraph D P marked) (alpha D P) (beta D P)) where
  point := Q.point
  point_injective := Q.point_injective
  curve := Sum.elim (fun e => Q.curve (retainedPrimal D P marked e))
    (fun _ t => Q.curve (markedPrimal D P marked) (markedParameter D P marked t))
  continuous := by
    intro e
    cases e with
    | inl e => exact Q.continuous _
    | inr _ => exact (Q.continuous _).comp (markedParameter D P marked).continuous
  injective := by
    intro e s _ t _ h
    cases e with
    | inl e => exact Q.nonloop_curve_injective _ (primal_loopless D P _) h
    | inr _ =>
      exact (markedParameter D P marked).injective
        (Q.nonloop_curve_injective _ (primal_loopless D P _) h)
  start := by
    intro e
    cases e with
    | inl e => exact Q.start _
    | inr _ => exact (marked_parameter_endpoints D P marked Q).1
  finish := by
    intro e
    cases e with
    | inl e => exact Q.finish _
    | inr _ => exact (marked_parameter_endpoints D P marked Q).2
  avoids := by
    intro e t ht0 ht1 v
    cases e with
    | inl e => exact Q.avoids _ t ht0 ht1 v
    | inr _ =>
      have ht := marked_parameter_interior D P marked t ht0 ht1
      exact Q.avoids _ _ ht.1 ht.2 v
  intersects := by
    intro e f hef s t h
    let tau : Copy D P marked ⊕ Unit → ArcParameter → ArcParameter :=
      Sum.elim (fun _ => id) (fun _ => markedParameter D P marked)
    have h' : Q.curve (augmentedOriginalCopyEquiv D P marked e) (tau e s) =
        Q.curve (augmentedOriginalCopyEquiv D P marked f) (tau f t) := by
      cases e <;> cases f <;> exact h
    have hst := Q.intersects (augmentedOriginalCopyEquiv D P marked e)
      (augmentedOriginalCopyEquiv D P marked f)
      ((augmentedOriginalCopyEquiv D P marked).injective.ne hef)
      (tau e s) (tau f t) h'
    have endpoints (e : Copy D P marked ⊕ Unit) (s : ArcParameter)
        (hs : (tau e s).val = 0 ∨ (tau e s).val = 1) : s.val = 0 ∨ s.val = 1 := by
      cases e with
      | inl e => exact hs
      | inr _ =>
        change (markedParameter D P marked s).val = 0 ∨
          (markedParameter D P marked s).val = 1 at hs
        unfold markedParameter at hs
        split at hs
        · exact hs
        · change 1 - s.val = 0 ∨ 1 - s.val = 1 at hs
          rcases hs with hs | hs
          · right; linarith only [hs]
          · left; linarith only [hs]
    exact ⟨endpoints e s hst.1, endpoints f t hst.2⟩

theorem original_augmented_trace (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P)) :
    drawingTrace Q = drawingTrace (originalAugmentedDrawing D P marked Q) := by
  ext z
  constructor
  · rintro (⟨v, hv⟩ | hz)
    · exact Or.inl ⟨v, hv⟩
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
      by_cases he : e = markedPrimal D P marked
      · subst e
        exact Or.inr (Set.mem_iUnion.mpr ⟨.inr (),
          (markedParameter D P marked).symm t, by
            simpa only [originalAugmentedDrawing, Sum.elim_inr,
              Homeomorph.apply_symm_apply] using ht⟩)
      · obtain ⟨f, rfl⟩ := (retainedPrimal_covers D P marked e).mpr he
        exact Or.inr (Set.mem_iUnion.mpr ⟨.inl f, t, ht⟩)
  · rintro (⟨v, hv⟩ | hz)
    · exact Or.inl ⟨v, hv⟩
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp hz
      cases e with
      | inl e => exact Or.inr (Set.mem_iUnion.mpr ⟨retainedPrimal D P marked e, t, ht⟩)
      | inr _ => exact Or.inr (Set.mem_iUnion.mpr
          ⟨markedPrimal D P marked, markedParameter D P marked t, ht⟩)

/-- Equal literal traces retain every full-H complement component. -/
def traceFaceEquiv {V E W I : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype I]
    {J : CopiedGraph V E} {K : CopiedGraph W I} (Q : Drawing J) (R : Drawing K)
    (h : drawingTrace Q = drawingTrace R) : Face Q ≃ Face R :=
  Equiv.cast (congrArg (fun T : Set Plane => ConnectedComponents {z : Plane // z ∉ T}) h)

private theorem component_region_cast (S T : Set Plane) (h : S = T)
    (F : ConnectedComponents {z : Plane // z ∉ S}) :
    {z : Plane | ∃ hz : z ∉ S, ConnectedComponents.mk (⟨z, hz⟩ : {w : Plane // w ∉ S}) = F} =
    {z : Plane | ∃ hz : z ∉ T, ConnectedComponents.mk (⟨z, hz⟩ : {w : Plane // w ∉ T}) =
      Equiv.cast (congrArg (fun U : Set Plane => ConnectedComponents {w : Plane // w ∉ U}) h) F} := by
  cases h
  rfl

theorem trace_face_region {V E W I : Type} [Fintype V] [Fintype E] [Fintype W] [Fintype I]
    {J : CopiedGraph V E} {K : CopiedGraph W I} (Q : Drawing J) (R : Drawing K)
    (h : drawingTrace Q = drawingTrace R) (F : Face Q) :
    faceRegion Q F = faceRegion R (traceFaceEquiv Q R h F) :=
  component_region_cast _ _ h F

/-- The actual marked arc is auxiliary, on the same supplied drawing and all its faces. -/
theorem original_marked_auxiliary_dictionary (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P)) :
    ∃ F : Face (deleteMarkedDrawing D P marked Q),
    ∃ A : AuxiliaryArc (deleteMarkedDrawing D P marked Q) F (alpha D P) (beta D P),
      A.drawing = originalAugmentedDrawing D P marked Q ∧
    ∃ faces : Face Q ≃ Face A.drawing,
      (∀ G, faceRegion Q G = faceRegion A.drawing (faces G)) ∧
      (∀ G v, incident Q v G ↔ incident A.drawing v (faces G)) ∧
      (∀ e, A.drawing.curve (.inl e) = Q.curve (retainedPrimal D P marked e)) ∧
      A.drawing.curve (.inr ()) =
        Q.curve (markedPrimal D P marked) ∘ markedParameter D P marked := by
  let R := deleteMarkedDrawing D P marked Q
  obtain ⟨F, hF, _, _⟩ := DeletedArc.common_face R
    (Q.curve (markedPrimal D P marked)) (Q.continuous _)
    (DeletedArc.omitted_interior_off_trace Q (retainedPrimal D P marked)
      (retainedPrimal_injective D P marked) (fun _ => rfl) (fun _ => rfl)
      (markedPrimal D P marked) (retainedPrimal_ne_marked D P marked))
  let A : AuxiliaryArc R F (alpha D P) (beta D P) := {
    drawing := originalAugmentedDrawing D P marked Q
    point_eq := rfl
    curve_eq := fun _ => rfl
    interior_in_face := by
      intro t ht0 ht1
      have ht := marked_parameter_interior D P marked t ht0 ht1
      exact hF _ ht.1 ht.2 }
  let faces := traceFaceEquiv Q A.drawing (original_augmented_trace D P marked Q)
  refine ⟨F, A, rfl, faces, ?_, ?_, fun _ => rfl, rfl⟩
  · exact trace_face_region Q A.drawing (original_augmented_trace D P marked Q)
  · intro G v
    change Q.point v ∈ closure (faceRegion Q G) ↔ Q.point v ∈ closure (faceRegion A.drawing (faces G))
    rw [trace_face_region Q A.drawing (original_augmented_trace D P marked Q) G]

end
end FiniteAvalanches.Electrical.SplitStep
