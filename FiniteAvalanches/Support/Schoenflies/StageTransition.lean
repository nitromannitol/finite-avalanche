/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/StageTransition.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.FiniteTransferTarget

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 

















open Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

 
structure StageTransition
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (par : γ → γ) : Prop where
   
  refines_src : T.src.Refines P.src par
   
  refines_tgt : T.tgt.Refines P.tgt par
   
  sourceSkeletonSet_subset : P.src.skeletonSet ⊆ T.src.skeletonSet
   
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet

namespace StageTransition

variable {P Q T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {par₁ par₂ : γ → γ}

 

theorem targetSkeletonSet_subset {par : γ → γ}
    (h : StageTransition T P par) : P.tgt.skeletonSet ⊆ T.tgt.skeletonSet := by
  rw [← P.homeo.image_skeletonSet, ← T.homeo.image_skeletonSet]
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h.sourceSkeletonSet_subset hx, h.homeo_eqOn hx⟩

 
theorem trans (h₂ : StageTransition T Q par₂) (h₁ : StageTransition Q P par₁) :
    StageTransition T P (par₁ ∘ par₂) where
  refines_src := h₂.refines_src.trans h₁.refines_src
  refines_tgt := h₂.refines_tgt.trans h₁.refines_tgt
  sourceSkeletonSet_subset :=
    h₁.sourceSkeletonSet_subset.trans h₂.sourceSkeletonSet_subset
  homeo_eqOn := by
    intro x hx
    calc
      T.homeo.toFun x = Q.homeo.toFun x :=
        h₂.homeo_eqOn (h₁.sourceSkeletonSet_subset hx)
      _ = P.homeo.toFun x := h₁.homeo_eqOn hx

end StageTransition

 
theorem IsPartialTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsPartialTransferOf T P B Hdraw par) : StageTransition T P par where
  refines_src := h.refines_src
  refines_tgt := h.refines_tgt
  sourceSkeletonSet_subset := h.sourceSkeletonSet_subset
  homeo_eqOn := h.homeo_eqOn

 
theorem IsTargetPartialTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTargetPartialTransferOf T P B Hdraw par) : StageTransition T P par where
  refines_src := h.refines_src
  refines_tgt := h.refines_tgt
  sourceSkeletonSet_subset := h.sourceSkeletonSet_subset
  homeo_eqOn := h.homeo_eqOn

 
theorem IsTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTransferOf T P H Hdraw par) : StageTransition T P par :=
  h.toIsPartialTransferOf.stageTransition

 
theorem IsTargetTransferOf.stageTransition
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (h : IsTargetTransferOf T P H Hdraw par) : StageTransition T P par :=
  h.toIsTargetPartialTransferOf.stageTransition

end Schoenflies
