/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/MatchedSplit.lean.
-/
import FiniteAvalanches.Support.Schoenflies.RealizeSplit
import FiniteAvalanches.Support.Schoenflies.FaceCycles

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




























































































open Set Schoenflies
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β}

 



theorem pointSet_congr {drw drw' : β → ℝ → Plane}
    (h : ∀ ⦃e⦄, e ∈ E(G) → edgeArc drw e = edgeArc drw' e) :
    pointSet G drw = pointSet G drw' := by
  rw [pointSet, pointSet]
  exact congrArg _ (Set.iUnion₂_congr fun e he => h he)

end Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

 



theorem Realization.pos_mem_skeletonSet (R : S.Realization) {v : γ} (hv : v ∈ V(S.skel)) :
    R.pos v ∈ R.skeletonSet :=
  Graph.vertexSet_subset_pointSet (by rw [Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)

namespace SplitData

variable {d : S.SplitData}

 





 




theorem skeletonSet_realize {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}
    (hE : d.EarCrosscut R earPos earDraw) :
    (d.realize R earPos earDraw hE).skeletonSet = R.skeletonSet ∪ d.earSet earPos earDraw := by
  have hstep : (d.realize R earPos earDraw hE).skeletonSet =
      Graph.pointSet (R.graph.union (d.earGraph earPos)) (d.splitDrawing R earDraw) := by
    rw [← hE.splitGraph_eq]
    rfl
  rw [hstep, Graph.pointSet_union]
  congr 1
  · exact Graph.pointSet_congr fun e he =>
      edgeArc_splitDrawing_of_mem_skel (by rwa [Realization.edgeSet_graph] at he)
  · exact Graph.pointSet_congr fun e he =>
      edgeArc_splitDrawing_of_mem_ear (by rwa [d.edgeSet_earGraph] at he)

 

theorem skeletonSet_subset_realize {R : S.Realization} {earPos : γ → Plane}
    {earDraw : γ → ℝ → Plane} (hE : d.EarCrosscut R earPos earDraw) :
    R.skeletonSet ⊆ (d.realize R earPos earDraw hE).skeletonSet :=
  (skeletonSet_realize hE).symm ▸ Set.subset_union_left

 
theorem isClosed_earSet {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}
    (hE : d.EarCrosscut R earPos earDraw) : IsClosed (d.earSet earPos earDraw) :=
  hE.isArcBetween_earSet.isArc.isCompact.isClosed

 

 











structure EarHomeo (d : S.SplitData) (earPos₁ : γ → Plane) (earDraw₁ : γ → ℝ → Plane)
    (earPos₂ : γ → Plane) (earDraw₂ : γ → ℝ → Plane) where
   
  toFun : Plane → Plane
   
  invFun : Plane → Plane
   
  continuousOn_toFun : ContinuousOn toFun (d.earSet earPos₁ earDraw₁)
   
  continuousOn_invFun : ContinuousOn invFun (d.earSet earPos₂ earDraw₂)
   
  leftInvOn : LeftInvOn invFun toFun (d.earSet earPos₁ earDraw₁)
   
  rightInvOn : RightInvOn invFun toFun (d.earSet earPos₂ earDraw₂)
   
  earPos_apply : ∀ ⦃z⦄, z ∈ V(d.ear) → toFun (earPos₁ z) = earPos₂ z
   
  edgeArc_image : ∀ ⦃f⦄, f ∈ E(d.ear) →
    toFun '' Graph.edgeArc earDraw₁ f = Graph.edgeArc earDraw₂ f

namespace EarHomeo

variable {earPos₁ earPos₂ : γ → Plane} {earDraw₁ earDraw₂ : γ → ℝ → Plane}
  (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂)

 


theorem image_earSet :
    m.toFun '' d.earSet earPos₁ earDraw₁ = d.earSet earPos₂ earDraw₂ := by
  rw [earSet, earSet, Graph.pointSet, Graph.pointSet, Set.image_union, Set.image_iUnion₂]
  congr 1
  · rw [d.vertexSet_earGraph, d.vertexSet_earGraph, ← Set.image_comp]
    exact Set.image_congr fun z hz => m.earPos_apply hz
  · rw [d.edgeSet_earGraph, d.edgeSet_earGraph]
    exact Set.iUnion₂_congr fun f hf => m.edgeArc_image hf

theorem injOn : InjOn m.toFun (d.earSet earPos₁ earDraw₁) := m.leftInvOn.injOn

theorem mapsTo :
    MapsTo m.toFun (d.earSet earPos₁ earDraw₁) (d.earSet earPos₂ earDraw₂) :=
  fun _ hx => m.image_earSet ▸ Set.mem_image_of_mem _ hx

 


theorem mapsTo_invFun :
    MapsTo m.invFun (d.earSet earPos₂ earDraw₂) (d.earSet earPos₁ earDraw₁) := by
  intro y hy
  rw [← m.image_earSet] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [m.leftInvOn hx]
  exact hx

 


def symm : d.EarHomeo earPos₂ earDraw₂ earPos₁ earDraw₁ where
  toFun := m.invFun
  invFun := m.toFun
  continuousOn_toFun := m.continuousOn_invFun
  continuousOn_invFun := m.continuousOn_toFun
  leftInvOn := m.rightInvOn
  rightInvOn := m.leftInvOn
  earPos_apply := by
    intro z hz
    rw [← m.earPos_apply hz]
    apply m.leftInvOn
    exact Graph.vertexSet_subset_pointSet (by
      rw [d.vertexSet_earGraph]
      exact ⟨z, hz, rfl⟩)
  edgeArc_image := by
    intro f hf
    rw [← m.edgeArc_image hf]
    exact m.leftInvOn.image_image'
      (Graph.edgeArc_subset_pointSet (by rw [d.edgeSet_earGraph]; exact hf))

@[simp] theorem symm_toFun : m.symm.toFun = m.invFun := rfl

@[simp] theorem symm_invFun : m.symm.invFun = m.toFun := rfl

variable {R₁ R₂ : S.Realization}

 


theorem toFun_pos_source (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.toFun (R₁.pos d.source) = R₂.pos d.source := by
  rw [← hE₁.pos_source, m.earPos_apply d.source_mem_ear, hE₂.pos_source]

theorem toFun_pos_target (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.toFun (R₁.pos d.target) = R₂.pos d.target := by
  rw [← hE₁.pos_target, m.earPos_apply d.target_mem_ear, hE₂.pos_target]

theorem invFun_pos_source (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.invFun (R₂.pos d.source) = R₁.pos d.source := by
  rw [← m.toFun_pos_source hE₁ hE₂, m.leftInvOn hE₁.pos_source_mem_earSet]

theorem invFun_pos_target (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.invFun (R₂.pos d.target) = R₁.pos d.target := by
  rw [← m.toFun_pos_target hE₁ hE₂, m.leftInvOn hE₁.pos_target_mem_earSet]

end EarHomeo

 

variable {R₁ R₂ : S.Realization} {earPos₁ earPos₂ : γ → Plane}
  {earDraw₁ earDraw₂ : γ → ℝ → Plane}

open scoped Classical in
 


noncomputable def splitMap (g : SkeletonHomeo R₁ R₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) : Plane → Plane :=
  fun x => if x ∈ R₁.skeletonSet then g.toFun x else m.toFun x

open scoped Classical in
 
noncomputable def splitInvMap (g : SkeletonHomeo R₁ R₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) : Plane → Plane :=
  fun y => if y ∈ R₂.skeletonSet then g.invFun y else m.invFun y

variable {g : SkeletonHomeo R₁ R₂} {m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂}

theorem splitMap_of_mem_skeletonSet {x : Plane} (hx : x ∈ R₁.skeletonSet) :
    splitMap g m x = g.toFun x := by
  classical
  simp only [splitMap, if_pos hx]

theorem splitMap_eqOn_skeletonSet : EqOn (splitMap g m) g.toFun R₁.skeletonSet :=
  fun _ hx => splitMap_of_mem_skeletonSet hx

theorem splitInvMap_of_mem_skeletonSet {y : Plane} (hy : y ∈ R₂.skeletonSet) :
    splitInvMap g m y = g.invFun y := by
  classical
  simp only [splitInvMap, if_pos hy]

theorem splitInvMap_of_notMem_skeletonSet {y : Plane} (hy : y ∉ R₂.skeletonSet) :
    splitInvMap g m y = m.invFun y := by
  classical
  simp only [splitInvMap, if_neg hy]

variable (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁) (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂)

include hE₁ hE₂

 


theorem splitMap_of_mem_earSet {x : Plane} (hx : x ∈ d.earSet earPos₁ earDraw₁) :
    splitMap g m x = m.toFun x := by
  classical
  by_cases hs : x ∈ R₁.skeletonSet
  · rw [splitMap, if_pos hs]
    have hends := hE₁.earSet_inter_skeletonSet ⟨hx, hs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
    rcases hends with rfl | rfl
    · rw [g.pos_apply d.source_mem_skel, m.toFun_pos_source hE₁ hE₂]
    · rw [g.pos_apply d.target_mem_skel, m.toFun_pos_target hE₁ hE₂]
  · rw [splitMap, if_neg hs]

theorem splitMap_eqOn_earSet : EqOn (splitMap g m) m.toFun (d.earSet earPos₁ earDraw₁) :=
  fun _ hx => splitMap_of_mem_earSet hE₁ hE₂ hx

 
theorem splitInvMap_eqOn_earSet :
    EqOn (splitInvMap g m) m.invFun (d.earSet earPos₂ earDraw₂) := by
  classical
  intro y hy
  by_cases hs : y ∈ R₂.skeletonSet
  · rw [splitInvMap, if_pos hs]
    have hends := hE₂.earSet_inter_skeletonSet ⟨hy, hs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
    rcases hends with rfl | rfl
    · have h : g.invFun (R₂.pos d.source) = R₁.pos d.source := g.symm.pos_apply d.source_mem_skel
      rw [h, m.invFun_pos_source hE₁ hE₂]
    · have h : g.invFun (R₂.pos d.target) = R₁.pos d.target := g.symm.pos_apply d.target_mem_skel
      rw [h, m.invFun_pos_target hE₁ hE₂]
  · rw [splitInvMap, if_neg hs]

 



theorem toFun_notMem_skeletonSet {x : Plane} (hx : x ∈ d.earSet earPos₁ earDraw₁)
    (hs : x ∉ R₁.skeletonSet) : m.toFun x ∉ R₂.skeletonSet := by
  intro hcon
  have hends := hE₂.earSet_inter_skeletonSet ⟨m.mapsTo hx, hcon⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
  rcases hends with heq | heq
  · rw [← m.toFun_pos_source hE₁ hE₂] at heq
    exact hs (m.injOn hx hE₁.pos_source_mem_earSet heq ▸ R₁.pos_mem_skeletonSet d.source_mem_skel)
  · rw [← m.toFun_pos_target hE₁ hE₂] at heq
    exact hs (m.injOn hx hE₁.pos_target_mem_earSet heq ▸ R₁.pos_mem_skeletonSet d.target_mem_skel)

 
theorem invFun_notMem_skeletonSet {y : Plane} (hy : y ∈ d.earSet earPos₂ earDraw₂)
    (hs : y ∉ R₂.skeletonSet) : m.invFun y ∉ R₁.skeletonSet := by
  intro hcon
  have hx : m.invFun y ∈ d.earSet earPos₁ earDraw₁ := m.mapsTo_invFun hy
  have hends := hE₁.earSet_inter_skeletonSet ⟨hx, hcon⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
  have hback : m.toFun (m.invFun y) = y := m.rightInvOn hy
  rcases hends with heq | heq
  · rw [heq, m.toFun_pos_source hE₁ hE₂] at hback
    exact hs (hback ▸ R₂.pos_mem_skeletonSet d.source_mem_skel)
  · rw [heq, m.toFun_pos_target hE₁ hE₂] at hback
    exact hs (hback ▸ R₂.pos_mem_skeletonSet d.target_mem_skel)

 

 








noncomputable def splitHomeo (g : SkeletonHomeo R₁ R₂)
    (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁) (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) :
    SkeletonHomeo (d.realize R₁ earPos₁ earDraw₁ hE₁) (d.realize R₂ earPos₂ earDraw₂ hE₂) where
  toFun := splitMap g m
  invFun := splitInvMap g m
  continuousOn_toFun := by
    rw [skeletonSet_realize hE₁]
    refine Plane.continuousOn_union_of_isClosed R₁.isCompact_skeletonSet.isClosed
      (isClosed_earSet hE₁) (g.continuousOn_toFun.congr splitMap_eqOn_skeletonSet) ?_
    exact m.continuousOn_toFun.congr (splitMap_eqOn_earSet hE₁ hE₂)
  continuousOn_invFun := by
    rw [skeletonSet_realize hE₂]
    refine Plane.continuousOn_union_of_isClosed R₂.isCompact_skeletonSet.isClosed
      (isClosed_earSet hE₂) (g.continuousOn_invFun.congr fun _ hy =>
        splitInvMap_of_mem_skeletonSet hy) ?_
    exact m.continuousOn_invFun.congr (splitInvMap_eqOn_earSet hE₁ hE₂)
  leftInvOn := by
    rw [skeletonSet_realize hE₁]
    rintro x (hx | hx)
    · rw [splitMap_of_mem_skeletonSet hx,
        splitInvMap_of_mem_skeletonSet (g.image_skeletonSet ▸ Set.mem_image_of_mem _ hx),
        g.leftInvOn hx]
    · by_cases hs : x ∈ R₁.skeletonSet
      · rw [splitMap_of_mem_skeletonSet hs,
          splitInvMap_of_mem_skeletonSet (g.image_skeletonSet ▸ Set.mem_image_of_mem _ hs),
          g.leftInvOn hs]
      · rw [splitMap_of_mem_earSet hE₁ hE₂ hx,
          splitInvMap_of_notMem_skeletonSet (toFun_notMem_skeletonSet hE₁ hE₂ hx hs),
          m.leftInvOn hx]
  rightInvOn := by
    rw [skeletonSet_realize hE₂]
    rintro y (hy | hy)
    · rw [splitInvMap_of_mem_skeletonSet hy,
        splitMap_of_mem_skeletonSet (g.symm.image_skeletonSet ▸ Set.mem_image_of_mem _ hy),
        g.rightInvOn hy]
    · by_cases hs : y ∈ R₂.skeletonSet
      · rw [splitInvMap_of_mem_skeletonSet hs,
          splitMap_of_mem_skeletonSet (g.symm.image_skeletonSet ▸ Set.mem_image_of_mem _ hs),
          g.rightInvOn hs]
      · rw [splitInvMap_of_notMem_skeletonSet hs,
          splitMap_of_mem_earSet hE₁ hE₂ (m.mapsTo_invFun hy), m.rightInvOn hy]
  pos_apply := by
    intro v hv
    have hv' : v ∈ V(S.skel) ∪ V(d.ear) := hv
    rcases hv' with hv' | hv'
    · change splitMap g m (d.splitPos R₁ earPos₁ v) = d.splitPos R₂ earPos₂ v
      rw [hE₁.splitPos_eq hv', hE₂.splitPos_eq hv',
        splitMap_of_mem_skeletonSet (R₁.pos_mem_skeletonSet hv'), g.pos_apply hv']
    · change splitMap g m (d.splitPos R₁ earPos₁ v) = d.splitPos R₂ earPos₂ v
      rw [splitPos_of_mem_ear hv', splitPos_of_mem_ear hv',
        splitMap_of_mem_earSet hE₁ hE₂ (EarCrosscut.mem_earSet_of_mem_ear hv'),
        m.earPos_apply hv']
  edgeArc_image := by
    intro e he
    have he' : e ∈ E(S.skel) ∪ E(d.ear) := he
    rcases he' with he' | he'
    · change splitMap g m '' Graph.edgeArc (d.splitDrawing R₁ earDraw₁) e =
        Graph.edgeArc (d.splitDrawing R₂ earDraw₂) e
      rw [edgeArc_splitDrawing_of_mem_skel he', edgeArc_splitDrawing_of_mem_skel he',
        Set.image_congr (fun x hx => splitMap_of_mem_skeletonSet
          (Graph.edgeArc_subset_pointSet (by rwa [Realization.edgeSet_graph]) hx)),
        g.edgeArc_image he']
    · change splitMap g m '' Graph.edgeArc (d.splitDrawing R₁ earDraw₁) e =
        Graph.edgeArc (d.splitDrawing R₂ earDraw₂) e
      rw [edgeArc_splitDrawing_of_mem_ear he', edgeArc_splitDrawing_of_mem_ear he',
        Set.image_congr (fun x hx => splitMap_of_mem_earSet hE₁ hE₂
          (EarCrosscut.edgeArc_subset_earSet he' hx)),
        m.edgeArc_image he']

@[simp] theorem splitHomeo_toFun : (splitHomeo g hE₁ hE₂ m).toFun = splitMap g m := rfl

@[simp] theorem splitHomeo_invFun : (splitHomeo g hE₁ hE₂ m).invFun = splitInvMap g m := rfl

 




theorem splitHomeo_eqOn :
    EqOn (splitHomeo g hE₁ hE₂ m).toFun g.toFun R₁.skeletonSet :=
  splitMap_eqOn_skeletonSet

 

theorem splitHomeo_eqOn_earSet :
    EqOn (splitHomeo g hE₁ hE₂ m).toFun m.toFun (d.earSet earPos₁ earDraw₁) :=
  splitMap_eqOn_earSet hE₁ hE₂

end SplitData

end CellStructure

end Schoenflies
