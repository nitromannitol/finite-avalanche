/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/StageTower.lean.
-/
import FiniteAvalanches.Support.Schoenflies.StageTransition
import FiniteAvalanches.Support.Schoenflies.LimitMap
import FiniteAvalanches.Support.Schoenflies.BoundaryContinuity2

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




















































open Bornology Filter Metric Set Topology
open scoped Graph

namespace Schoenflies

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}

 




 

theorem isBounded_union_inside (hC : IsSeparating C) : IsBounded (C ∪ inside C) := by
  rw [Set.union_comm, ← (IsRegionOf.inside C).closure_eq hC]
  exact hC.isBounded_inside.closure

 

theorem isOpen_union_inside_sdiff (hC : IsSeparating C) : IsOpen ((C ∪ inside C) \ C) := by
  rw [union_inside_sdiff]; exact hC.isOpen_inside

 
theorem isOpen_closedSquare_sdiff_modelCurve :
    IsOpen (Plane.closedSquare 0 1 \ modelCurve) := by
  rw [closedSquare_sdiff_modelCurve]; exact Plane.isOpen_openSquare 0 1

 

 








structure StageSequence (γ : Type*) [Nonempty γ] (S₀ : CellStructure γ) (C : Set Plane) where
   
  stage : ℕ → GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)
   
  par : ℕ → γ → γ
   
  transition : ∀ n, StageTransition (stage (n + 1)) (stage n) (par n)
   
  eps : ℕ → ℝ
   
  diam_tgtStar_le : ∀ n, ∀ ⦃σ⦄, σ ∈ (stage n).str.cells → diam ((stage n).tgt.star σ) ≤ eps n
   
  tendsto_eps : Tendsto eps atTop (nhds 0)
   
  tendsto_diam_srcStar : ∀ ⦃x⦄, x ∈ inside C →
    Tendsto (fun n => diam ((stage n).src.star ((stage n).src.carrier x))) atTop (nhds 0)
   

  base : S₀.CombInvariants
   
  isSeparating : IsSeparating C

namespace StageSequence

variable (T : StageSequence γ S₀ C)

 
theorem refines_src (n : ℕ) :
    (T.stage (n + 1)).src.Refines (T.stage n).src (T.par n) :=
  (T.transition n).refines_src

 
theorem refines_tgt (n : ℕ) :
    (T.stage (n + 1)).tgt.Refines (T.stage n).tgt (T.par n) :=
  (T.transition n).refines_tgt

 
theorem skeletonSet_mono (n : ℕ) :
    (T.stage n).src.skeletonSet ⊆ (T.stage (n + 1)).src.skeletonSet :=
  (T.transition n).sourceSkeletonSet_subset

 
theorem skelHomeo_succ (n : ℕ) :
    Set.EqOn (T.stage (n + 1)).homeo.toFun (T.stage n).homeo.toFun
      (T.stage n).src.skeletonSet :=
  (T.transition n).homeo_eqOn

 


def limitTower : CellStructure.LimitTower γ where
  str n := (T.stage n).str
  src n := (T.stage n).src
  tgt n := (T.stage n).tgt
  skelHomeo n := (T.stage n).homeo
  par := T.par
  dom := C ∪ inside C
  bdry := C
  dom' := Plane.closedSquare 0 1
  bdry' := modelCurve
  eps := T.eps
  srcDecomp n := (T.stage n).src_isCellDecomposition
  tgtDecomp n := (T.stage n).tgt_isCellDecomposition
  comb n := (T.stage n).combInvariants T.base
  srcRefines := T.refines_src
  tgtRefines := T.refines_tgt
  srcOuterSet n := (T.stage n).src_isWeaklyAdmissible.outerSet_eq
  tgtOuterSet n := (T.stage n).tgt_isWeaklyAdmissible.outerSet_eq
  isClosed_dom := isClosed_union_inside T.isSeparating
  isClosed_dom' := Plane.isClosed_closedSquare 0 1
  isBounded_dom := isBounded_union_inside T.isSeparating
  isBounded_dom' := Plane.isBounded_closedSquare 0 1
  isOpen_int := isOpen_union_inside_sdiff T.isSeparating
  isOpen_int' := isOpen_closedSquare_sdiff_modelCurve
  skeletonSet_mono := T.skeletonSet_mono
  skelHomeo_succ := T.skelHomeo_succ
  diam_tgtStar_le := T.diam_tgtStar_le
  tendsto_eps := T.tendsto_eps
  tendsto_diam_srcStar := by
    intro x hx
    exact T.tendsto_diam_srcStar (by rwa [union_inside_sdiff] at hx)

@[simp] theorem limitTower_region : T.limitTower.region = inside C := union_inside_sdiff C

@[simp] theorem limitTower_region' : T.limitTower.region' = Plane.openSquare 0 1 :=
  closedSquare_sdiff_modelCurve

 


theorem isHomeoOn_F :
    IsHomeoOn T.limitTower.F T.limitTower.inv (inside C) (Plane.openSquare 0 1) := by
  have h := T.limitTower.isHomeoOn_F
  rwa [limitTower_region, limitTower_region'] at h

 





theorem F_eq_skelHomeo {n : ℕ} {x : Plane} (hx : x ∈ (T.stage n).src.skeletonSet)
    (hxD : x ∈ C ∪ inside C) : T.limitTower.F x = (T.stage n).homeo.toFun x :=
  CellStructure.LimitTower.F_eq_skelHomeo hx hxD

end StageSequence

end Schoenflies
