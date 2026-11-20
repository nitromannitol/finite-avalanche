/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/RealizeSubdivHomeo.lean.
-/
import FiniteAvalanches.Support.Schoenflies.RealizeSubdiv
import FiniteAvalanches.Support.Schoenflies.ArcMonotone

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 

























































open Set unitInterval
open scoped Graph

namespace Schoenflies

open Graph

namespace CellStructure

namespace SubdivData

variable {γ : Type*} {S : CellStructure γ} {R₁ R₂ : S.Realization}
  (d : S.SubdivData) (g : SkeletonHomeo R₁ R₂) {t : ℝ}

 

theorem edgeArc_subset_skeletonSet (R : S.Realization) :
    R.drawing d.edge '' I ⊆ R.skeletonSet :=
  edgeArc_subset_pointSet (d.edge_mem_edgeSet_graph R)

 


theorem arcMatch_edge : ArcMatch (R₁.drawing d.edge) (R₂.drawing d.edge) g.toFun where
  continuousOn_src := d.continuousOn_drawing_edge R₁
  injOn_src := d.injOn_drawing_edge R₁
  continuousOn_tgt := d.continuousOn_drawing_edge R₂
  injOn_tgt := d.injOn_drawing_edge R₂
  continuousOn_map := g.continuousOn_toFun.mono (d.edgeArc_subset_skeletonSet R₁)
  injOn_map := g.injOn.mono (d.edgeArc_subset_skeletonSet R₁)
  image_eq := g.edgeArc_image d.edge_mem_edgeSet

 

 



noncomputable def targetParam (d : S.SubdivData) (g : SkeletonHomeo R₁ R₂) (t : ℝ) : ℝ :=
  transferParam (R₁.drawing d.edge) (R₂.drawing d.edge) g.toFun t

theorem targetParam_mem_I (ht : t ∈ I) : d.targetParam g t ∈ I :=
  (d.arcMatch_edge g).param_mem_I ht

 
theorem drawing_targetParam (ht : t ∈ I) :
    R₂.drawing d.edge (d.targetParam g t) = g.toFun (R₁.drawing d.edge t) :=
  (d.arcMatch_edge g).apply_param ht

 

theorem targetParam_leftParam : d.targetParam g (d.leftParam R₁) = d.leftParam R₂ := by
  refine (d.arcMatch_edge g).param_eq (d.leftParam_mem_I R₂) ?_
  rw [d.drawing_leftParam R₂, d.drawing_leftParam R₁]
  exact (g.pos_apply d.isLink.left_mem).symm

 
theorem targetParam_rightParam : d.targetParam g (d.rightParam R₁) = d.rightParam R₂ := by
  refine (d.arcMatch_edge g).param_eq (d.rightParam_mem_I R₂) ?_
  rw [d.drawing_rightParam R₂, d.drawing_rightParam R₁]
  exact (g.pos_apply d.isLink.right_mem).symm

 


theorem targetParam_ends :
    (d.targetParam g 0 = 0 ∧ d.targetParam g 1 = 1) ∨
      (d.targetParam g 0 = 1 ∧ d.targetParam g 1 = 0) := by
  have hL := d.targetParam_leftParam g
  have hR := d.targetParam_rightParam g
  rw [rightParam, rightParam] at hR
  rcases d.leftParam_eq_zero_or_one R₁ with h1 | h1 <;>
      rcases d.leftParam_eq_zero_or_one R₂ with h2 | h2 <;>
      simp only [h1, h2, sub_zero, sub_self] at hL hR
  · exact Or.inl ⟨hL, hR⟩
  · exact Or.inr ⟨hL, hR⟩
  · exact Or.inr ⟨hR, hL⟩
  · exact Or.inl ⟨hR, hL⟩

 

theorem targetParam_mem_Ioo (ht : t ∈ Ioo (0 : ℝ) 1) : d.targetParam g t ∈ Ioo (0 : ℝ) 1 :=
  (d.arcMatch_edge g).param_mem_Ioo_of_ends (d.targetParam_ends g) ht

 

theorem image_edge_uIcc {s u : ℝ} (hs : s ∈ I) (hu : u ∈ I) :
    g.toFun '' (R₁.drawing d.edge '' uIcc s u) =
      R₂.drawing d.edge '' uIcc (d.targetParam g s) (d.targetParam g u) :=
  (d.arcMatch_edge g).image_image_uIcc hs hu

 

 





noncomputable def realizeHomeo (d : S.SubdivData) (g : SkeletonHomeo R₁ R₂) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    SkeletonHomeo (d.realize R₁ t ht)
      (d.realize R₂ (d.targetParam g t) (d.targetParam_mem_Ioo g ht)) where
  toFun := g.toFun
  invFun := g.invFun
  continuousOn_toFun := by
    rw [skeletonSet_realize ht]; exact g.continuousOn_toFun
  continuousOn_invFun := by
    rw [skeletonSet_realize (d.targetParam_mem_Ioo g ht)]; exact g.continuousOn_invFun
  leftInvOn := by
    rw [skeletonSet_realize ht]; exact g.leftInvOn
  rightInvOn := by
    rw [skeletonSet_realize (d.targetParam_mem_Ioo g ht)]; exact g.rightInvOn
  pos_apply := by
    intro v hv
    rw [subdivideEdge_skel, d.skeleton_vertexSet, mem_insert_iff] at hv
    simp only [realize_pos]
    rcases hv with rfl | hv
    · rw [realizePos_newVertex, realizePos_newVertex]
      exact (d.drawing_targetParam g (Ioo_subset_Icc_self ht)).symm
    · rw [realizePos_of_mem_vertexSet hv, realizePos_of_mem_vertexSet hv]
      exact g.pos_apply hv
  edgeArc_image := by
    intro e he
    rw [subdivideEdge_skel, d.skeleton_edgeSet] at he
    simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff] at he
    simp only [realize_drawing]
    rcases he with rfl | rfl | ⟨heS, hee⟩
    · 
      rw [edgeArc_newEdge₁, edgeArc_newEdge₁,
        d.image_edge_uIcc g (d.leftParam_mem_I R₁) (Ioo_subset_Icc_self ht),
        d.targetParam_leftParam g]
    · 
      rw [edgeArc_newEdge₂, edgeArc_newEdge₂,
        d.image_edge_uIcc g (Ioo_subset_Icc_self ht) (d.rightParam_mem_I R₁),
        d.targetParam_rightParam g]
    · 
      have hc := S.mem_cells_of_mem_edgeSet heS
      rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hc) (d.ne_newEdge₂_of_mem_cells hc),
        edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hc) (d.ne_newEdge₂_of_mem_cells hc)]
      exact g.edgeArc_image heS

@[simp] theorem realizeHomeo_toFun (ht : t ∈ Ioo (0 : ℝ) 1) :
    (d.realizeHomeo g ht).toFun = g.toFun := rfl

@[simp] theorem realizeHomeo_invFun (ht : t ∈ Ioo (0 : ℝ) 1) :
    (d.realizeHomeo g ht).invFun = g.invFun := rfl

 

theorem realizeHomeo_eqOn (ht : t ∈ Ioo (0 : ℝ) 1) {A : Set Plane} :
    EqOn (d.realizeHomeo g ht).toFun g.toFun A := fun _ _ => rfl

end SubdivData

end CellStructure

end Schoenflies
