/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/QuantitativeStages.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.FreshDenseSelection
import FiniteAvalanches.Support.Schoenflies.StageTransition

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





















open Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}
  {P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}

 
def TargetFaceMesh
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (bound : ℝ) : Prop :=
  ∀ {F : γ}, F ∈ P.str.faces → Metric.diam (closure (P.tgt.cell F)) < bound

namespace TargetFaceMesh

variable {T : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)}
  {par : γ → γ} {bound : ℝ}

 
theorem refine (hmesh : TargetFaceMesh P bound) (href : T.tgt.Refines P.tgt par) :
    TargetFaceMesh T bound := by
  intro F hF
  exact lt_of_le_of_lt
    (href.diam_cell_le P.tgt_isCellDecomposition
      (Plane.isBounded_closedSquare 0 1) (T.str.mem_cells_of_mem_faces hF))
    (hmesh (href.parent_mem_faces hF))

 
theorem forwardTransfer (hmesh : TargetFaceMesh P bound)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (h : IsTransferOf T P H Hdraw par) : TargetFaceMesh T bound :=
  hmesh.refine h.refines_tgt

 
theorem diam_star_lt (hmesh : TargetFaceMesh P bound)
    {σ : γ} (hσ : σ ∈ P.str.cells) :
    Metric.diam (P.tgt.star σ) < 2 * bound :=
  P.tgt_isCellDecomposition.diam_star_lt P.str_combInvariants
    (Plane.isBounded_closedSquare 0 1) hσ
    (fun _ hF _ => hmesh hF)

end TargetFaceMesh

 
structure QuantitativeReverseStage
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (anchors : List Plane) (bound : ℝ) where
   
  cover : TargetSegmentCover P
   
  overlay : TargetSegmentCover.MeshOverlayTransferData cover anchors
   
  delta_lt_half_bound : overlay.delta < bound / 2

namespace QuantitativeReverseStage

variable {anchors : List Plane} {bound : ℝ}
  (w : QuantitativeReverseStage P anchors bound)

 
abbrev pair : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  w.overlay.pair

 
abbrev parent : γ → γ := w.overlay.parent

 
theorem transition : StageTransition w.pair P w.parent :=
  w.overlay.transfer.stageTransition

 
theorem diam_targetStar_lt_bound {σ : γ} (hσ : σ ∈ w.pair.str.cells) :
    Metric.diam (w.pair.tgt.star σ) < bound := by
  have hstar := w.overlay.diam_targetStar_lt hσ
  linarith [w.delta_lt_half_bound]

 
theorem targetFaceMesh : TargetFaceMesh w.pair w.overlay.delta := by
  intro F hF
  exact w.overlay.diam_closure_targetFace_lt hF

end QuantitativeReverseStage

 


theorem exists_quantitativeReverseStage [Infinite γ]
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hsep : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
    (anchors : List Plane) {bound : ℝ} (hbound : 0 < bound) :
    Nonempty (QuantitativeReverseStage P anchors bound) := by
  obtain ⟨Q⟩ := P.exists_targetSegmentCover
  have hhalf : 0 < bound / 2 := by positivity
  obtain ⟨w, hw⟩ := Q.exists_meshOverlayTransferData_lt_inside
    hsep hcycle anchors hhalf
  exact ⟨{ cover := Q, overlay := w, delta_lt_half_bound := hw }⟩

end Schoenflies
