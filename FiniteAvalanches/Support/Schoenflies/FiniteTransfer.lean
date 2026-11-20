/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/FiniteTransfer.lean.
-/
import FiniteAvalanches.Support.Schoenflies.RefinementStars
import FiniteAvalanches.Support.Schoenflies.OverlayGraph
import FiniteAvalanches.Support.Schoenflies.SkeletonAccess
import FiniteAvalanches.Support.Schoenflies.Graph.RelativeEar
import FiniteAvalanches.Support.Schoenflies.Graph.Relabel
import FiniteAvalanches.Support.Schoenflies.Graph.CycleJordan
import FiniteAvalanches.Support.Schoenflies.JordanClosed
import FiniteAvalanches.Support.Schoenflies.BoundaryCyclesGenerated
import FiniteAvalanches.Support.Schoenflies.MatchedSplit
import FiniteAvalanches.Support.Schoenflies.MatchedArc

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





























































































































open Metric Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*}

 









namespace CellStructure

namespace Realization

variable {S : CellStructure γ}

 


structure IsWeaklyAdmissible (R : S.Realization) (outer dom : Set Plane) : Prop where
   
  isTwoConnected : R.graph.IsTwoConnected
   
  outerSet_eq : R.outerSet = outer
   
  isPolygonal : ∀ ⦃e⦄, e ∈ E(S.skel) → e ∉ E(S.outerGraph) → IsPolygonal (edgeArc R.drawing e)
   

  cell_subset : ∀ ⦃e⦄, e ∈ E(S.skel) → e ∉ E(S.outerGraph) → R.cell e ⊆ dom \ outer
   
  skeletonSet_subset : R.skeletonSet ⊆ dom

 
structure IsAdmissible (R : S.Realization) (outer dom : Set Plane) : Prop
    extends R.IsWeaklyAdmissible outer dom where
   
  isConnected_nonboundary : IsConnected R.nonboundary

end Realization

namespace SplitData.EarCrosscut

variable {S : CellStructure γ}
variable {d : S.SplitData} {R : S.Realization} {outer dom : Set Plane}
  {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}

 

theorem isWeaklyAdmissible_realize (hE : d.EarCrosscut R earPos earDraw)
    (hR : R.IsWeaklyAdmissible outer dom) (hcd : R.IsCellDecomposition dom)
    (hpoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc earDraw e)) :
    (d.realize R earPos earDraw hE).IsWeaklyAdmissible outer dom where
  isTwoConnected := by
    change ((S.splitFace d).skel.map (d.splitPos R earPos)).IsTwoConnected
    rw [hE.splitGraph_eq]
    have hcompat : R.graph.Compatible (d.earGraph earPos) :=
      Graph.Compatible.of_disjoint_edgeSet (by
        rw [Realization.edgeSet_graph, d.edgeSet_earGraph]
        exact d.disjoint_edgeSet)
    exact hR.isTwoConnected.ear hcompat hE.isPathGraph_earGraph source_ne_target_pos
      (by rw [R.vertexSet_graph]; exact ⟨d.source, d.source_mem_skel, rfl⟩)
      (by rw [R.vertexSet_graph]; exact ⟨d.target, d.target_mem_skel, rfl⟩)
  outerSet_eq := by
    change Graph.pointSet ((S.splitFace d).outerGraph.map (d.splitPos R earPos))
      (d.splitDrawing R earDraw) = outer
    rw [CellStructure.splitFace_outerGraph]
    have hgraph : S.outerGraph.map (d.splitPos R earPos) = S.outerGraph.map R.pos :=
      Graph.map_eq_of_eqOn fun z hz => hE.splitPos_eq (S.outerGraph_le.vertexSet_mono hz)
    rw [hgraph]
    calc
      Graph.pointSet (S.outerGraph.map R.pos) (d.splitDrawing R earDraw) =
          Graph.pointSet (S.outerGraph.map R.pos) R.drawing := by
        apply Graph.pointSet_congr
        intro e he
        rw [Graph.edgeSet_map] at he
        exact d.edgeArc_splitDrawing_of_mem_skel (S.outerGraph_le.edgeSet_mono he)
      _ = R.outerSet := rfl
      _ = outer := hR.outerSet_eq
  isPolygonal := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    rw [CellStructure.splitFace_outerGraph] at houter
    rcases he with he | he
    · change IsPolygonal (edgeArc (d.splitDrawing R earDraw) e)
      rw [d.edgeArc_splitDrawing_of_mem_skel he]
      exact hR.isPolygonal he houter
    · change IsPolygonal (edgeArc (d.splitDrawing R earDraw) e)
      rw [d.edgeArc_splitDrawing_of_mem_ear he]
      exact hpoly he
  cell_subset := by
    intro e he houter
    change e ∈ E(d.skeleton) at he
    rw [CellStructure.splitFace_outerGraph] at houter
    rcases he with he | he
    · rw [CellStructure.SplitData.realize_cell,
        d.splitCell_of_mem_cells (S.mem_cells_of_mem_edgeSet he)]
      exact hR.cell_subset he houter
    · rw [CellStructure.SplitData.realize_cell, d.splitCell_earEdge he]
      intro x hx
      have hxEar : x ∈ d.earSet earPos earDraw :=
        edgeArc_subset_earSet he hx.1
      have hxEnds : x ∉ ({R.pos d.source, R.pos d.target} : Set Plane) := by
        rintro (rfl | rfl)
        · exact hx.2 ⟨d.source, d.source_mem_ear, hE.pos_source⟩
        · exact hx.2 ⟨d.target, d.target_mem_ear, hE.pos_target⟩
      have hxFace : x ∈ R.cell d.face := hE.subset_face ⟨hxEar, hxEnds⟩
      refine ⟨hcd.cell_subset_domain (S.mem_cells_of_mem_faces d.face_mem) hxFace, ?_⟩
      intro hxOuter
      have hxSkel : x ∈ R.skeletonSet := by
        apply R.outerSet_subset_skeletonSet
        rw [hR.outerSet_eq]
        exact hxOuter
      exact Set.disjoint_left.1 (R.disjoint_cell_skeletonSet hcd d.face_mem) hxFace hxSkel
  skeletonSet_subset := by
    rw [d.skeletonSet_realize hE]
    refine Set.union_subset hR.skeletonSet_subset ?_
    intro x hx
    by_cases hxEnds : x ∈ ({R.pos d.source, R.pos d.target} : Set Plane)
    · rcases hxEnds with rfl | rfl
      · exact hR.skeletonSet_subset (R.pos_mem_skeletonSet d.source_mem_skel)
      · exact hR.skeletonSet_subset (R.pos_mem_skeletonSet d.target_mem_skel)
    · exact hcd.cell_subset_domain (S.mem_cells_of_mem_faces d.face_mem)
        (hE.subset_face ⟨hx, hxEnds⟩)

end SplitData.EarCrosscut

namespace SplitData.EarCrosscut

variable {S : CellStructure γ} {d : S.SplitData} {R₁ R₂ : S.Realization}
  {srcPos : γ → Plane} {srcDraw : γ → ℝ → Plane}

 




theorem exists_matched_target (hsrc : d.EarCrosscut R₁ srcPos srcDraw)
    {A : Set Plane} (hApoly : IsPolygonal A)
    (hAarc : IsArcBetween A (R₂.pos d.source) (R₂.pos d.target))
    (hAsub : A \ {R₂.pos d.source, R₂.pos d.target} ⊆ R₂.cell d.face)
    (hdisj : Disjoint (R₂.cell d.face) R₂.skeletonSet) :
    ∃ tgtPos : γ → Plane, ∃ tgtDraw : γ → ℝ → Plane,
      ∃ _ : d.EarHomeo srcPos srcDraw tgtPos tgtDraw,
      d.EarCrosscut R₂ tgtPos tgtDraw ∧
      ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (Graph.edgeArc tgtDraw e) := by
  classical
  let m : ArcHomeo (d.earSet srcPos srcDraw) A
      (R₁.pos d.source) (R₁.pos d.target) (R₂.pos d.source) (R₂.pos d.target) :=
    Classical.choice (exists_arcHomeo hsrc.isArcBetween_earSet hAarc)
  let tgtPos : γ → Plane := fun z => m.toFun (srcPos z)
  let tgtDraw : γ → ℝ → Plane := Graph.mapDrawing m srcDraw
  have hgraph : d.earGraph tgtPos = (d.earGraph srcPos).map m.toFun := by
    change d.ear.map tgtPos = (d.ear.map srcPos).map m.toFun
    rw [Graph.map_map]
    rfl
  have hset : d.earSet tgtPos tgtDraw = A := by
    rw [CellStructure.SplitData.earSet, hgraph,
      Graph.pointSet_map_mapDrawing (G := d.earGraph srcPos)]
    exact m.image_eq
  have htgt : d.EarCrosscut R₂ tgtPos tgtDraw := {
    pos_source := by
      change m.toFun (srcPos d.source) = R₂.pos d.source
      rw [hsrc.pos_source]
      exact m.map_left
    pos_target := by
      change m.toFun (srcPos d.target) = R₂.pos d.target
      rw [hsrc.pos_target]
      exact m.map_right
    injOn := by
      intro x hx y hy hxy
      apply hsrc.injOn hx hy
      apply m.injOn (CellStructure.SplitData.EarCrosscut.mem_earSet_of_mem_ear hx)
        (CellStructure.SplitData.EarCrosscut.mem_earSet_of_mem_ear hy)
      exact hxy
    isDrawing := by
      rw [hgraph]
      exact hsrc.isDrawing.map_arcHomeo m rfl
    subset_face := by
      intro x hx
      apply hAsub
      exact ⟨hset ▸ hx.1, hx.2⟩
    disjoint_skeleton := hdisj
    polygonal := hset ▸ hApoly
  }
  have hhomeo : d.EarHomeo srcPos srcDraw tgtPos tgtDraw := {
    toFun := m.toFun
    invFun := m.invFun
    continuousOn_toFun := m.continuousOn_toFun
    continuousOn_invFun := by
      rw [hset]
      exact m.continuousOn_invFun
    leftInvOn := m.leftInvOn
    rightInvOn := by
      rw [hset]
      exact m.rightInvOn
    earPos_apply := by intro z _; rfl
    edgeArc_image := by
      intro e _
      exact (Graph.edgeArc_mapDrawing m e).symm
  }
  refine ⟨tgtPos, tgtDraw, hhomeo, htgt, ?_⟩
  intro e he
  obtain ⟨x, y, hxy⟩ := d.ear.exists_isLink_of_mem_edgeSet he
  have hedge : IsArcBetween (Graph.edgeArc tgtDraw e) (tgtPos x) (tgtPos y) :=
    htgt.isDrawing.edge_isArcBetween (hxy.map tgtPos)
  exact hedge.isPolygonal_of_subset_arc hAarc hApoly
    (hset ▸ CellStructure.SplitData.EarCrosscut.edgeArc_subset_earSet he)

end SplitData.EarCrosscut

namespace Realization

variable {S : CellStructure γ}

 










variable {R : S.Realization} {D N Q : Set Plane} {F σ : γ} {z : Plane}

 
theorem mem_faces_of_notMem_skeletonSet (R : S.Realization) (hσ : σ ∈ S.cells)
    (hz : z ∈ R.cell σ) (hznot : z ∉ R.skeletonSet) : σ ∈ S.faces := by
  rcases hσ with hσ | hσ
  · exact absurd (cell_subset_skeletonSet hσ hz) hznot
  · exact hσ

namespace IsCellDecomposition

 


theorem frontier_cell_subset_skeletonSet (h : R.IsCellDecomposition D)
    (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : frontier (R.cell F) ⊆ R.skeletonSet := by
  rw [← hJ.faceBoundary_eq h hF, Realization.faceBoundary]
  rintro z hz
  obtain ⟨σ, ⟨⟨hσ, hσF⟩, hσne⟩, hz⟩ := Realization.mem_cellUnion_iff.1 hz
  rcases hσ with (hv | he) | hface
  · exact R.cell_subset_skeletonSet (Or.inl hv) hz
  · exact R.cell_subset_skeletonSet (Or.inr he) hz
  · exact absurd (h.sub_face_eq hJ hface hF hσF) hσne

 

theorem cellsAbsorb (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan) :
    CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F} := by
  rintro N hN hNdisj A ⟨F, hF, rfl⟩ hmeet
  exact subset_of_isPreconnected_of_frontier_disjoint (hJ.isOpen hF) hN
    (hNdisj.mono_right (h.frontier_cell_subset_skeletonSet hJ hF)) hmeet

 

theorem face_eq_connectedComponentIn (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) (hFQ : R.cell F ⊆ Q) (z : Plane)
    (hz : z ∈ R.cell F) :
    R.cell F = connectedComponentIn (Q \ R.skeletonSet) z := by
  symm
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hJ.isOpen hF)
    (hJ.isConnected hF).isPreconnected ?_ ?_ hz
  · exact fun x hx => ⟨hFQ hx,
      Set.disjoint_left.1 (R.disjoint_cell_skeletonSet h hF) hx⟩
  · refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro x ⟨hxfr, -, hxskel⟩
    exact hxskel (h.frontier_cell_subset_skeletonSet hJ hF hxfr)

 


theorem sub_of_pos_mem_closure_cell (h : R.IsCellDecomposition D) {a F : γ}
    (ha : a ∈ V(S.skel)) (hF : F ∈ S.faces) (hmem : R.pos a ∈ closure (R.cell F)) :
    S.sub a F := by
  refine h.sub_of_subset_closure (S.mem_cells_of_mem_vertexSet ha)
    (S.mem_cells_of_mem_faces hF) ?_
  rw [R.cell_vertex ha]
  exact Set.singleton_subset_iff.2 hmem

 

theorem exists_unique_face_subset_cell (h : R.IsCellDecomposition D)
    (hcells : CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F})
    (hN : IsPreconnected N) (hNne : N.Nonempty) (hND : N ⊆ D)
    (hNdisj : Disjoint N R.skeletonSet) :
    ∃ F ∈ S.faces, N ⊆ R.cell F ∧ ∀ T ∈ S.faces, N ⊆ R.cell T → T = F := by
  obtain ⟨z, hz⟩ := hNne
  obtain ⟨F, hFc, hzF⟩ := h.exists_cell (hND hz)
  have hznot : z ∉ R.skeletonSet := Set.disjoint_left.1 hNdisj hz
  have hFf : F ∈ S.faces := R.mem_faces_of_notMem_skeletonSet hFc hzF hznot
  refine ⟨F, hFf, hcells N hN hNdisj (R.cell F) ⟨F, hFf, rfl⟩ ⟨z, hz, hzF⟩, fun T hT hNT => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (h.disjoint (S.mem_cells_of_mem_faces hT) hFc hne) (hNT hz) hzF

 






theorem exists_face_of_ear (h : R.IsCellDecomposition D)
    (hcells : CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F})
    (hN : IsPreconnected N) (hNne : N.Nonempty) (hND : N ⊆ D)
    (hNdisj : Disjoint N R.skeletonSet) {a b : γ}
    (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel))
    (hacl : R.pos a ∈ closure N) (hbcl : R.pos b ∈ closure N) :
    ∃ F ∈ S.faces, N ⊆ R.cell F ∧ S.sub a F ∧ S.sub b F ∧
      ∀ T ∈ S.faces, N ⊆ R.cell T → T = F := by
  obtain ⟨F, hF, hNF, huniq⟩ := h.exists_unique_face_subset_cell hcells hN hNne hND hNdisj
  exact ⟨F, hF, hNF,
    h.sub_of_pos_mem_closure_cell ha hF (closure_mono hNF hacl),
    h.sub_of_pos_mem_closure_cell hb hF (closure_mono hNF hbcl), huniq⟩

end IsCellDecomposition

end Realization

end CellStructure

 









 



structure GeneratedPair (S₀ : CellStructure γ) (srcOuter srcDom tgtOuter tgtDom : Set Plane)
    where
   
  str : CellStructure γ
   
  generated : GeneratedStructure S₀ str
   
  str_combInvariants : str.CombInvariants
   
  str_boundaryCycles : str.BoundaryCycles
   
  src : str.Realization
   
  tgt : str.Realization
   
  homeo : CellStructure.SkeletonHomeo src tgt
   
  src_isCellDecomposition : src.IsCellDecomposition srcDom
   
  tgt_isCellDecomposition : tgt.IsCellDecomposition tgtDom
   
  src_isFaceJordan : src.IsFaceJordan
   

  tgt_isFaceJordan : tgt.IsFaceJordan
   
  tgtInterior_isOpen : IsOpen (tgtDom \ tgtOuter)
   
  tgtInterior_frontier_subset : frontier (tgtDom \ tgtOuter) ⊆ tgt.skeletonSet
   
  tgt_isPolygonal : ∀ ⦃e⦄, e ∈ E(str.skel) → IsPolygonal (edgeArc tgt.drawing e)
   
  src_isWeaklyAdmissible : src.IsWeaklyAdmissible srcOuter srcDom
   
  tgt_isWeaklyAdmissible : tgt.IsWeaklyAdmissible tgtOuter tgtDom

namespace GeneratedPair

variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

 

theorem combInvariants (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h₀ : S₀.CombInvariants) : P.str.CombInvariants :=
  P.generated.combInvariants h₀

 

theorem boundaryCycles (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hcycles : S₀.BoundaryCycles) (h₀ : S₀.CombInvariants) :
    P.str.BoundaryCycles :=
  P.generated.boundaryCycles hcycles h₀

 

theorem src_nonboundary_eq (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    P.src.nonboundary = P.src.skeletonSet \ srcOuter := by
  rw [CellStructure.Realization.nonboundary, P.src_isWeaklyAdmissible.outerSet_eq]

 



theorem tgt_isAdmissible (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.src.nonboundary) : P.tgt.IsAdmissible tgtOuter tgtDom :=
  { P.tgt_isWeaklyAdmissible with
    isConnected_nonboundary := P.homeo.isConnected_nonboundary_iff.1 h }

 
theorem src_isAdmissible (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.src.nonboundary) : P.src.IsAdmissible srcOuter srcDom :=
  { P.src_isWeaklyAdmissible with isConnected_nonboundary := h }

 
theorem tgt_face_subset_interior (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} (hF : F ∈ P.str.faces) : P.tgt.cell F ⊆ tgtDom \ tgtOuter := by
  intro x hx
  refine ⟨P.tgt_isCellDecomposition.cell_subset_domain
    (P.str.mem_cells_of_mem_faces hF) hx, ?_⟩
  intro hxOuter
  have hxSkel : x ∈ P.tgt.skeletonSet := by
    rw [← P.tgt_isWeaklyAdmissible.outerSet_eq] at hxOuter
    exact P.tgt.outerSet_subset_skeletonSet hxOuter
  exact Set.disjoint_left.1
    (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hF) hx hxSkel

 
theorem tgt_face_isComponent (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} (hF : F ∈ P.str.faces) :
    P.tgt.cell F ⊆ tgtDom \ tgtOuter ∧
      ∃ z, P.tgt.cell F =
        connectedComponentIn ((tgtDom \ tgtOuter) \ P.tgt.skeletonSet) z := by
  have hne := P.tgt_isFaceJordan.nonempty hF
  obtain ⟨z, hz⟩ := hne
  exact ⟨P.tgt_face_subset_interior hF, z,
    P.tgt_isCellDecomposition.face_eq_connectedComponentIn P.tgt_isFaceJordan hF
      (P.tgt_face_subset_interior hF) z hz⟩

 







 

noncomputable def split (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : P.str.CombInvariants) (d : P.str.SplitData)
    (srcPos : γ → Plane) (srcDraw : γ → ℝ → Plane)
    (tgtPos : γ → Plane) (tgtDraw : γ → ℝ → Plane)
    (hsrc : d.EarCrosscut P.src srcPos srcDraw)
    (htgt : d.EarCrosscut P.tgt tgtPos tgtDraw)
    (m : d.EarHomeo srcPos srcDraw tgtPos tgtDraw)
    (hsrcEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc srcDraw e))
    (htgtEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc tgtDraw e)) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom where
  str := P.str.splitFace d
  generated := .splitFace P.generated d
  str_combInvariants := d.combInvariants hS
  str_boundaryCycles := d.boundaryCycles P.str_boundaryCycles hS
  src := d.realize P.src srcPos srcDraw hsrc
  tgt := d.realize P.tgt tgtPos tgtDraw htgt
  homeo := d.splitHomeo P.homeo hsrc htgt m
  src_isCellDecomposition :=
    (d.isCellDecomposition_and_isFaceJordan_realize hsrc hS
      P.src_isCellDecomposition P.src_isFaceJordan).1
  tgt_isCellDecomposition :=
    (d.isCellDecomposition_and_isFaceJordan_realize htgt hS
      P.tgt_isCellDecomposition P.tgt_isFaceJordan).1
  src_isFaceJordan :=
    (d.isCellDecomposition_and_isFaceJordan_realize hsrc hS
      P.src_isCellDecomposition P.src_isFaceJordan).2.1
  tgt_isFaceJordan :=
    (d.isCellDecomposition_and_isFaceJordan_realize htgt hS
      P.tgt_isCellDecomposition P.tgt_isFaceJordan).2.1
  tgtInterior_isOpen := P.tgtInterior_isOpen
  tgtInterior_frontier_subset := P.tgtInterior_frontier_subset.trans
    (d.skeletonSet_subset_realize htgt)
  tgt_isPolygonal := by
    intro e he
    change e ∈ E(d.skeleton) at he
    rcases he with he | he
    · change IsPolygonal (edgeArc (d.splitDrawing P.tgt tgtDraw) e)
      rw [CellStructure.SplitData.edgeArc_splitDrawing_of_mem_skel he]
      exact P.tgt_isPolygonal he
    · change IsPolygonal (edgeArc (d.splitDrawing P.tgt tgtDraw) e)
      rw [CellStructure.SplitData.edgeArc_splitDrawing_of_mem_ear he]
      exact htgtEdgePoly he
  src_isWeaklyAdmissible := hsrc.isWeaklyAdmissible_realize P.src_isWeaklyAdmissible
    P.src_isCellDecomposition hsrcEdgePoly
  tgt_isWeaklyAdmissible := htgt.isWeaklyAdmissible_realize P.tgt_isWeaklyAdmissible
    P.tgt_isCellDecomposition htgtEdgePoly

@[simp] theorem split_str (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : P.str.CombInvariants) (d : P.str.SplitData)
    (srcPos : γ → Plane) (srcDraw : γ → ℝ → Plane)
    (tgtPos : γ → Plane) (tgtDraw : γ → ℝ → Plane)
    (hsrc : d.EarCrosscut P.src srcPos srcDraw)
    (htgt : d.EarCrosscut P.tgt tgtPos tgtDraw)
    (m : d.EarHomeo srcPos srcDraw tgtPos tgtDraw)
    (hsrcEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc srcDraw e))
    (htgtEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) → IsPolygonal (edgeArc tgtDraw e)) :
    (P.split hS d srcPos srcDraw tgtPos tgtDraw hsrc htgt m hsrcEdgePoly
      htgtEdgePoly).str =
      P.str.splitFace d := rfl

end GeneratedPair

 
















 
structure IsSourceExtension {S : CellStructure γ} (R : S.Realization) (outer dom : Set Plane)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop where
   
  finite : H.Finite
   
  isDrawing : IsDrawing H Hdraw
   
  isTwoConnected : H.IsTwoConnected
   
  vertexSet_subset : V(R.graph) ⊆ V(H)
   
  skeletonSet_subset : R.skeletonSet ⊆ pointSet H Hdraw
   



  edge_subset : ∀ ⦃e⦄, e ∈ E(S.skel) → ∀ ⦃f⦄, f ∈ E(H) →
    (edgeArc Hdraw f ∩ (R.cell e \ V(H))).Nonempty →
      edgeArc Hdraw f ⊆ edgeArc R.drawing e
   
  pointSet_subset : pointSet H Hdraw ⊆ dom
   

  edge_dichotomy : ∀ ⦃f⦄, f ∈ E(H) → edgeArc Hdraw f ⊆ outer ∨
    (IsPolygonal (edgeArc Hdraw f) ∧ edgeArc Hdraw f \ V(H) ⊆ dom \ outer)
   
  isConnected : IsConnected (pointSet H Hdraw \ outer)

namespace IsSourceExtension

variable {S : CellStructure γ} {R : S.Realization} {outer dom : Set Plane}
  {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}

 
theorem not_isLoopAt (h : IsSourceExtension R outer dom H Hdraw) ⦃f : γ⦄ ⦃x : Plane⦄ :
    ¬ H.IsLoopAt f x := h.isDrawing.not_isLoopAt f x

end IsSourceExtension

 











variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

 


theorem exists_injective_avoiding [Infinite γ] (used : Set γ) (hused : used.Finite)
    (ι : Type*) [Finite ι] :
    ∃ fresh : ι → γ, Function.Injective fresh ∧ ∀ i, fresh i ∉ used := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let code : ι ↪ ℕ := (Fintype.equivFin ι).toEmbedding.trans Fin.valEmbedding
  let supply : ℕ ↪ {x // x ∈ (usedᶜ : Set γ)} :=
    hused.infinite_compl.natEmbedding (usedᶜ : Set γ)
  refine ⟨fun i => supply (code i), ?_, fun i => (supply (code i)).2⟩
  intro i j hij
  exact code.injective (supply.injective (Subtype.ext hij))

 

theorem exists_injective_pinned_avoiding {α : Type*} [Infinite γ]
    {used : Set γ} (hused : used.Finite) {u v : γ}
    (hu : u ∈ used) (hv : v ∈ used) (huv : u ≠ v)
    {s : Set α} (hs : s.Finite) {a b : α} (hab : a ≠ b) :
    ∃ name : α → γ, name a = u ∧ name b = v ∧ InjOn name s ∧
      ∀ x ∈ s, x ≠ a → x ≠ b → name x ∉ used := by
  classical
  let inner := {x : α // x ∈ s ∧ x ≠ a ∧ x ≠ b}
  letI : Finite inner := Set.finite_coe_iff.mpr (hs.subset fun x hx => hx.1)
  obtain ⟨fresh, hfresh, havoid⟩ := exists_injective_avoiding used hused inner
  let name : α → γ := fun x =>
    if hxa : x = a then u else if hxb : x = b then v
    else if hx : x ∈ s then fresh ⟨x, hx, hxa, hxb⟩ else u
  have hnamea : name a = u := by simp [name]
  have hnameb : name b = v := by simp [name, Ne.symm hab]
  have hname_inner (x : α) (hx : x ∈ s) (hxa : x ≠ a) (hxb : x ≠ b) :
      name x = fresh (⟨x, hx, hxa, hxb⟩ : inner) := by
    simp [name, hxa, hxb, hx]
  refine ⟨name, hnamea, hnameb, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · exact hya.symm
      by_cases hyb : y = b
      · subst y
        exact absurd (hnamea.symm.trans (hxy.trans hnameb)) huv
      · exfalso
        apply havoid ⟨y, hy, hya, hyb⟩
        rw [← hname_inner y hy hya hyb, ← hxy, hnamea]
        exact hu
    · by_cases hxb : x = b
      · subst x
        by_cases hya : y = a
        · subst y
          exact absurd (hnameb.symm.trans (hxy.trans hnamea)) huv.symm
        by_cases hyb : y = b
        · exact hyb.symm
        · exfalso
          apply havoid ⟨y, hy, hya, hyb⟩
          rw [← hname_inner y hy hya hyb, ← hxy, hnameb]
          exact hv
      · by_cases hya : y = a
        · subst y
          exfalso
          apply havoid ⟨x, hx, hxa, hxb⟩
          rw [← hname_inner x hx hxa hxb, hxy, hnamea]
          exact hu
        by_cases hyb : y = b
        · subst y
          exfalso
          apply havoid ⟨x, hx, hxa, hxb⟩
          rw [← hname_inner x hx hxa hxb, hxy, hnameb]
          exact hv
        · have hsub : (⟨x, hx, hxa, hxb⟩ : inner) = ⟨y, hy, hya, hyb⟩ := by
            apply hfresh
            calc
            fresh (⟨x, hx, hxa, hxb⟩ : inner) = name x :=
              (hname_inner x hx hxa hxb).symm
            _ = name y := hxy
            _ = fresh (⟨y, hy, hya, hyb⟩ : inner) := hname_inner y hy hya hyb
          exact congrArg (fun z : inner => z.1) hsub
  · intro x hx hxa hxb
    rw [hname_inner x hx hxa hxb]
    exact havoid ⟨x, hx, hxa, hxb⟩

 
structure IsPartialTransferOf (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop where
   
  refines_src : T.src.Refines P.src par
   

  refines_tgt : T.tgt.Refines P.tgt par
   
  sourceSkeletonSet_subset : P.src.skeletonSet ⊆ T.src.skeletonSet
   
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet
   
  skeletonSet_eq : T.src.skeletonSet = pointSet B Hdraw
   

  vertexSet_subset : V(B) ⊆ V(T.src.graph)

 







 
structure EarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
   
  splitData : T.str.SplitData
   
  srcPos : γ → Plane
  srcDraw : γ → ℝ → Plane
   
  tgtPos : γ → Plane
  tgtDraw : γ → ℝ → Plane
   
  srcCrosscut : splitData.EarCrosscut T.src srcPos srcDraw
  tgtCrosscut : splitData.EarCrosscut T.tgt tgtPos tgtDraw
   
  earHomeo : splitData.EarHomeo srcPos srcDraw tgtPos tgtDraw
   
  srcEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (edgeArc srcDraw e)
  tgtEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (edgeArc tgtDraw e)
   
  srcEarSet_eq : splitData.earSet srcPos srcDraw = Graph.edgesCover Hdraw D
   
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.src srcPos srcDraw srcCrosscut).graph)

namespace EarStepData

variable {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {a : Plane} {D : List γ}

 
noncomputable def pair (w : EarStepData T B H Hdraw a D) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom :=
  T.split T.str_combInvariants w.splitData w.srcPos w.srcDraw w.tgtPos w.tgtDraw
    w.srcCrosscut w.tgtCrosscut w.earHomeo w.srcEdgePolygonal w.tgtEdgePolygonal

@[simp] theorem pair_src (w : EarStepData T B H Hdraw a D) :
    w.pair.src = w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut := rfl

@[simp] theorem pair_tgt (w : EarStepData T B H Hdraw a D) :
    w.pair.tgt = w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut := rfl

 


theorem isPartialTransferOf_pair
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {b : Plane}
    {par : γ → γ} (w : EarStepData T B H Hdraw a D)
    (hdraw : H.IsDrawing Hdraw) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (hT : IsPartialTransferOf T P B Hdraw par) :
    IsPartialTransferOf w.pair P (B.union (H.pathGraphOf a D)) Hdraw
      (par ∘ w.splitData.parent) where
  refines_src :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.srcCrosscut
      T.str_combInvariants T.src_isCellDecomposition T.src_isFaceJordan).2.2).trans hT.refines_src
  refines_tgt :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.tgtCrosscut
      T.str_combInvariants T.tgt_isCellDecomposition T.tgt_isFaceJordan).2.2).trans hT.refines_tgt
  sourceSkeletonSet_subset :=
    hT.sourceSkeletonSet_subset.trans
      (w.splitData.skeletonSet_subset_realize w.srcCrosscut)
  homeo_eqOn := by
    intro x hx
    calc
      w.pair.homeo.toFun x = T.homeo.toFun x :=
        w.splitData.splitHomeo_eqOn
          (g := T.homeo) (hE₁ := w.srcCrosscut) (hE₂ := w.tgtCrosscut)
          (m := w.earHomeo) (hT.sourceSkeletonSet_subset hx)
      _ = P.homeo.toFun x := hT.homeo_eqOn hx
  skeletonSet_eq := by
    change (w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut).skeletonSet = _
    rw [w.splitData.skeletonSet_realize, hT.skeletonSet_eq, w.srcEarSet_eq,
      Graph.pointSet_union, hdraw.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)]
  vertexSet_subset := by
    change V(B.union (H.pathGraphOf a D)) ⊆
      V((w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut).graph)
    exact w.vertexSet_subset

end EarStepData

 

 



theorem exists_source_face_of_ear
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {par : γ → γ}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hBH : B ≤ H) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    (hT : IsPartialTransferOf T P B Hdraw par) :
    ∃ u v F, u ∈ V(T.str.skel) ∧ v ∈ V(T.str.skel) ∧ u ≠ v ∧
      T.src.pos u = a ∧ T.src.pos v = b ∧ F ∈ T.str.faces ∧
      Graph.edgesCover Hdraw D \ {a, b} ⊆ T.src.cell F ∧
      T.str.sub u F ∧ T.str.sub v F := by
  have haT := hT.vertexSet_subset haB
  have hbT := hT.vertexSet_subset hbB
  rw [CellStructure.Realization.vertexSet_graph] at haT hbT
  obtain ⟨u, hu, hua⟩ := haT
  obtain ⟨v, hv, hvb⟩ := hbT
  have huv : u ≠ v := by
    intro huv
    apply hab
    rw [← hua, ← hvb, huv]
  have harc : IsArcBetween (Graph.edgesCover Hdraw D) a b :=
    hH.isDrawing.path_isArcBetween hpath (hpath.ne_nil hab)
  let N := Graph.edgesCover Hdraw D \ {a, b}
  have hNconn : IsPreconnected N := harc.isConnected_diff.isPreconnected
  have hNne : N.Nonempty := harc.isConnected_diff.nonempty
  have hND : N ⊆ srcDom := by
    intro x hx
    exact hH.pointSet_subset
      (Graph.edgesCover_subset_pointSet (fun g hg => hpath.edge_mem hg) hx.1)
  have hNdisj : Disjoint N T.src.skeletonSet := by
    rw [hT.skeletonSet_eq]
    refine Set.disjoint_left.2 fun x hx hxB ↦ hx.2 ?_
    exact hH.isDrawing.edgesCover_inter_pointSet hBH hpath hint hnew ⟨hx.1, hxB⟩
  obtain ⟨F, hF, hNF, huF, hvF, -⟩ :=
    T.src_isCellDecomposition.exists_face_of_ear
      (T.src_isCellDecomposition.cellsAbsorb T.src_isFaceJordan)
      hNconn hNne hND hNdisj hu hv
      (hua ▸ harc.left_mem_closure_diff) (hvb ▸ harc.right_mem_closure_diff)
  exact ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hNF, huF, hvF⟩

 



theorem source_ear_edge_polygonal
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {F : γ}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hpath : H.IsPath a D b) (hF : F ∈ T.str.faces)
    (hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.src.cell F) :
    ∀ e ∈ D, IsPolygonal (edgeArc Hdraw e) := by
  intro e he
  rcases hH.edge_dichotomy (hpath.edge_mem he) with houter | hpoly
  · exfalso
    have houterSkel : srcOuter ⊆ T.src.skeletonSet := by
      intro z hz
      apply T.src.outerSet_subset_skeletonSet
      rw [T.src_isWeaklyAdmissible.outerSet_eq]
      exact hz
    have harcPair : edgeArc Hdraw e ⊆ ({a, b} : Set Plane) := by
      intro z hz
      by_contra hzpair
      have hzCell : z ∈ T.src.cell F :=
        hinside ⟨Graph.mem_edgesCover he hz, hzpair⟩
      have hzSkel : z ∈ T.src.skeletonSet := houterSkel (houter hz)
      exact Set.disjoint_left.1
        (T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition hF) hzCell hzSkel
    obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet (hpath.edge_mem he)
    have harc := hH.isDrawing.edge_isArcBetween hxy
    have hxyne := hH.isDrawing.ne_of_isLink hxy
    rcases harcPair harc.left_mem with rfl | rfl <;>
      rcases harcPair harc.right_mem with rfl | rfl
    · exact hxyne rfl
    · exact harc.not_subset_pair harcPair
    · exact harc.not_subset_pair (by simpa [Set.pair_comm] using harcPair)
    · exact hxyne rfl
  · exact hpoly.1

 
structure IsTransferOf (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop
    extends IsPartialTransferOf T P H Hdraw par where
   
  src_isAdmissible : T.src.IsAdmissible srcOuter srcDom
   

  tgt_isAdmissible : T.tgt.IsAdmissible tgtOuter tgtDom

 






































 
def CommonSubdivision (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsPartialTransferOf T₀ P K Hdraw par₀

 








def EarStep [Infinite γ] (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P B Hdraw par →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par' : γ → γ),
        IsPartialTransferOf T' P (B.union (H.pathGraphOf a D)) Hdraw par'

 



def EarStepConstruction [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (_hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P B Hdraw par → Nonempty (EarStepData T B H Hdraw a D)

structure SourceEarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
  splitData : T.str.SplitData
  srcPos : γ → Plane
  srcDraw : γ → ℝ → Plane
  srcCrosscut : splitData.EarCrosscut T.src srcPos srcDraw
  srcEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) → IsPolygonal (Graph.edgeArc srcDraw e)
  srcEarSet_eq : splitData.earSet srcPos srcDraw = Graph.edgesCover Hdraw D
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.src srcPos srcDraw srcCrosscut).graph)

 

theorem exists_sourceEarStepData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
      H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      (∀ g ∈ D, g ∉ E(B)) →
      ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
        IsPartialTransferOf T P B Hdraw par → Nonempty (SourceEarStepData T B H Hdraw a D) := by
  classical
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hinside, huF, hvF⟩ :=
    exists_source_face_of_ear hH hBH hpath hab haB hbB hint hnew hT
  let paths := T.str_boundaryCycles.boundaryPaths F hF u v hu hv huF hvF huv
  let Q : Graph Plane γ := H.pathGraphOf a D
  have hQle : Q ≤ H := Graph.pathGraphOf_le hpath.isWalk
  have hQpath : Q.IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  have haQ : a ∈ V(Q) := Graph.mem_vertexSet_pathGraphOf_self
  have hbQ : b ∈ V(Q) := by
    rw [Graph.pathGraphOf_vertexSet]
    exact hpath.target_mem_walkVertices
  have hQfinV : V(Q).Finite := hpath.isWalk.finite_vertexSet_pathGraphOf
  have hQfinE : E(Q).Finite := hpath.isWalk.finite_edgeSet_pathGraphOf
  have huCell : u ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hu
  have hvCell : v ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hv
  obtain ⟨vname, vname_a, vname_b, vname_inj, vname_fresh⟩ :=
    exists_injective_pinned_avoiding T.str.finite_cells huCell hvCell huv
      hQfinV hab
  let newVertices : Set γ := vname '' (V(Q) \ {a, b})
  have hnewVertices_fin : newVertices.Finite := hQfinV.sdiff.image vname
  have hnewVertices_avoid : Disjoint newVertices T.str.cells := by
    rw [Set.disjoint_left]
    rintro z ⟨x, ⟨hxQ, hxab⟩, rfl⟩ hzCell
    exact vname_fresh x hxQ (fun h => hxab (Or.inl h)) (fun h => hxab (Or.inr h)) hzCell
  let edgeUsed : Set γ := T.str.cells ∪ newVertices
  have hedgeUsed_fin : edgeUsed.Finite := T.str.finite_cells.union hnewVertices_fin
  letI : Finite E(Q) := Set.finite_coe_iff.mpr hQfinE
  obtain ⟨freshEdge, freshEdge_inj, freshEdge_avoid⟩ :=
    exists_injective_avoiding edgeUsed hedgeUsed_fin E(Q)
  let ename : γ → γ := fun e => if he : e ∈ E(Q) then freshEdge ⟨e, he⟩ else u
  have ename_apply {e : γ} (he : e ∈ E(Q)) : ename e = freshEdge ⟨e, he⟩ := by
    simp [ename, he]
  have ename_inj : InjOn ename E(Q) := by
    intro e he f hf hef
    have hsub : (⟨e, he⟩ : E(Q)) = ⟨f, hf⟩ := by
      apply freshEdge_inj
      calc
        freshEdge ⟨e, he⟩ = ename e := (ename_apply he).symm
        _ = ename f := hef
        _ = freshEdge ⟨f, hf⟩ := ename_apply hf
    exact congrArg (fun z : E(Q) => z.1) hsub
  have ename_avoid {e : γ} (he : e ∈ E(Q)) : ename e ∉ edgeUsed := by
    rw [ename_apply he]
    exact freshEdge_avoid ⟨e, he⟩
  let newEdges : Set γ := ename '' E(Q)
  have hnewEdges_fin : newEdges.Finite := hQfinE.image ename
  have hnewEdges_avoid : Disjoint newEdges edgeUsed := by
    rw [Set.disjoint_left]
    rintro z ⟨e, he, rfl⟩
    exact ename_avoid he
  let faceUsed : Set γ := edgeUsed ∪ newEdges
  have hfaceUsed_fin : faceUsed.Finite := hedgeUsed_fin.union hnewEdges_fin
  obtain ⟨freshFace, freshFace_inj, freshFace_avoid⟩ :=
    exists_injective_avoiding faceUsed hfaceUsed_fin (Fin 2)
  let face₁ : γ := freshFace 0
  let face₂ : γ := freshFace 1
  let relabelled : Graph Plane γ := Q.relabelEdges ename ename_inj
  let ear : Graph γ γ := relabelled.map vname
  have hVear : V(ear) = vname '' V(Q) := by simp [ear, relabelled]
  have hEear : E(ear) = ename '' E(Q) := by simp [ear, relabelled]
  have hearPath : ear.IsPathGraph u (D.map ename) v := by
    have hrel := hQpath.relabelEdges ename_inj
    have hmap := hrel.map (by simpa [relabelled] using vname_inj)
    simpa [ear, relabelled, vname_a, vname_b] using hmap
  have hear_disjoint : Disjoint V(ear) E(ear) := by
    rw [Set.disjoint_left]
    rintro z hzV hzE
    rw [hVear] at hzV
    rw [hEear] at hzE
    obtain ⟨x, hxQ, rfl⟩ := hzV
    obtain ⟨e, heQ, heq⟩ := hzE
    have hedgeAvoid := ename_avoid heQ
    apply hedgeAvoid
    rcases eq_or_ne x a with rfl | hxa
    · exact Or.inl (by rw [heq, vname_a]; exact huCell)
    rcases eq_or_ne x b with rfl | hxb
    · exact Or.inl (by rw [heq, vname_b]; exact hvCell)
    · exact Or.inr ⟨x, ⟨hxQ, by simp [hxa, hxb]⟩, heq.symm⟩
  have hvertex_inter : V(ear) ∩ V(T.str.skel) = {u, v} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzEar, hzOld⟩
      rw [hVear] at hzEar
      obtain ⟨x, hxQ, rfl⟩ := hzEar
      rcases eq_or_ne x a with rfl | hxa
      · simp [vname_a]
      rcases eq_or_ne x b with rfl | hxb
      · simp [vname_b]
      exfalso
      exact vname_fresh x hxQ hxa hxb
        (T.str.mem_cells_of_mem_vertexSet hzOld)
    · rintro z (rfl | rfl)
      · exact ⟨hVear ▸ ⟨a, haQ, vname_a⟩, hu⟩
      · exact ⟨hVear ▸ ⟨b, hbQ, vname_b⟩, hv⟩
  have hface₁Avoid : face₁ ∉ faceUsed := freshFace_avoid 0
  have hface₂Avoid : face₂ ∉ faceUsed := freshFace_avoid 1
  let d : T.str.SplitData := {
    face := F
    face₁ := face₁
    face₂ := face₂
    ear := ear
    source := u
    target := v
    earWalk := D.map ename
    path₁ := paths.path₁
    path₂ := paths.path₂
    isPathGraph := hearPath
    isPath₁ := paths.isPath₁
    isPath₂ := paths.isPath₂
    ear_disjoint := hear_disjoint
    source_ne_target := huv
    face_mem := hF
    vertexSet_inter := hvertex_inter
    edge_fresh := by
      intro e he
      rw [hEear] at he
      obtain ⟨f, hf, rfl⟩ := he
      exact fun hmem => ename_avoid hf (Or.inl hmem)
    vertex_fresh := by
      intro z hz hzu hzv
      rw [hVear] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxa : x ≠ a := fun h => hzu (h ▸ vname_a)
      have hxb : x ≠ b := fun h => hzv (h ▸ vname_b)
      exact vname_fresh x hx hxa hxb
    face₁_notMem := fun h => hface₁Avoid (Or.inl (Or.inl h))
    face₂_notMem := fun h => hface₂Avoid (Or.inl (Or.inl h))
    face₁_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₁Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₁Avoid (Or.inr hz)
    face₂_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₂Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₂Avoid (Or.inr hz)
    face_ne := fun h => Fin.zero_ne_one (freshFace_inj h)
    sub_face := paths.sub_face
    paths_meet := paths.paths_meet
  }
  let srcPos : γ → Plane := Function.invFunOn vname V(Q)
  let srcDraw : γ → ℝ → Plane := Graph.relabelDrawing Q ename Hdraw
  have hQdraw : Graph.IsDrawing Q Hdraw := hH.isDrawing.mono hQle
  have hrelDraw : Graph.IsDrawing relabelled srcDraw := by
    exact hQdraw.relabelEdges ename_inj
  have hearGraph : d.earGraph srcPos = relabelled := by
    change (relabelled.map vname).map srcPos = relabelled
    simpa [srcPos, relabelled] using
      (Graph.map_map_invFunOn (G := relabelled) (f := vname)
        (by simpa [relabelled] using vname_inj))
  have hsrcSet : d.earSet srcPos srcDraw = Graph.edgesCover Hdraw D := by
    rw [CellStructure.SplitData.earSet, hearGraph, Graph.pointSet_relabelEdges ename_inj]
    simpa [Q] using hH.isDrawing.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)
  have hsrcEdgeOrig := source_ear_edge_polygonal hH hpath hF hinside
  have hsrcEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) →
      IsPolygonal (Graph.edgeArc srcDraw e) := by
    intro e he
    change e ∈ E(ear) at he
    rw [hEear] at he
    obtain ⟨f, hfQ, rfl⟩ := he
    rw [Graph.edgeArc_relabelDrawing ename_inj hfQ]
    apply hsrcEdgeOrig f
    rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ
  have hsrcPoly : IsPolygonal (d.earSet srcPos srcDraw) := by
    rw [hsrcSet]
    exact hQdraw.isPolygonal_edgesCover
      (fun f hfQ => hsrcEdgeOrig f (by rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ))
      hpath.pathGraphOf.isWalk (hpath.ne_nil hab)
  have hsrc : d.EarCrosscut T.src srcPos srcDraw := {
    pos_source := by
      change srcPos u = T.src.pos u
      rw [hua]
      change Function.invFunOn vname V(Q) u = a
      rw [← vname_a, vname_inj.leftInvOn_invFunOn haQ]
    pos_target := by
      change srcPos v = T.src.pos v
      rw [hvb]
      change Function.invFunOn vname V(Q) v = b
      rw [← vname_b, vname_inj.leftInvOn_invFunOn hbQ]
    injOn := by
      change InjOn (Function.invFunOn vname V(Q)) V(ear)
      rw [hVear]
      exact Function.invFunOn_injOn_image vname V(Q)
    isDrawing := by rw [hearGraph]; exact hrelDraw
    subset_face := by
      rw [hsrcSet]
      simpa [d, hua, hvb] using hinside
    disjoint_skeleton := T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition hF
    polygonal := hsrcPoly
  }
  refine ⟨{
    splitData := d
    srcPos := srcPos
    srcDraw := srcDraw
    srcCrosscut := hsrc
    srcEdgePolygonal := hsrcEdgePoly
    srcEarSet_eq := hsrcSet
    vertexSet_subset := ?_
  }⟩
  change V(B.union (H.pathGraphOf a D)) ⊆
    V((T.str.splitFace d).skel.map (d.splitPos T.src srcPos))
  rw [hsrc.splitGraph_eq]
  intro x hx
  rcases hx with hxB | hxQ
  · exact Or.inl (hT.vertexSet_subset hxB)
  · apply Or.inr
    rw [hearGraph, Graph.vertexSet_relabelEdges]
    exact hxQ

 



theorem earStep_of_data [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hbuild : EarStepConstruction P H Hdraw hH) :
    EarStep P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint T par hT
  rcases Graph.ear_edges_notMem_or_union_eq hBH hpath hab haB hbB hint with hnew | hsame
  · obtain ⟨w⟩ := hbuild B a b D hB hBH hpath hab haB hbB hint hnew T par hT
    exact ⟨w.pair, par ∘ w.splitData.parent,
      w.isPartialTransferOf_pair hH.isDrawing hpath hab hT⟩
  · refine ⟨T, par, ?_⟩
    rw [hsame]
    exact hT

 

 







theorem transfer_of_ears_of_commonSubdivision_of_earStep [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) (hstep : EarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P H Hdraw par := by
  haveI := hH.finite
  obtain ⟨K, T₀, par₀, hK, hKH, hbase⟩ := hsub
  refine hH.isTwoConnected.ear_decomposition
    (motive := fun B => ∃ T par, IsPartialTransferOf T P B Hdraw par)
    (fun g x => hH.isDrawing.not_isLoopAt g x) hK hKH ⟨T₀, par₀, hbase⟩ ?_
  rintro B a b D hB - hBH ⟨T, par, hT⟩ hpath hab haB hbB hint
  exact hstep B a b D hB hBH hpath hab haB hbB hint T par hT

 

 









theorem finite_transfer_toward_square_of_commonSubdivision_of_earStep [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) (hstep : EarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par := by
  obtain ⟨T, par, hT⟩ :=
    transfer_of_ears_of_commonSubdivision_of_earStep hH hsub hstep
  
  
  
  have hconn : IsConnected T.src.nonboundary := by
    rw [T.src_nonboundary_eq, hT.skeletonSet_eq]
    exact hH.isConnected
  exact ⟨T, par, hT, T.src_isAdmissible hconn, T.tgt_isAdmissible hconn⟩

 














section TargetEar

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {Q F J P A₁ A₂ : Set Plane} {cells : Set (Set Plane)} {v w : Plane}

 

theorem isOpen_isPreconnected_disjoint_of_target_cell [G.Finite] (h : IsDrawing G drawing)
    (hQ : IsOpen Q)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) :
    IsOpen F ∧ IsPreconnected F ∧ Disjoint F (pointSet G drawing) := by
  obtain ⟨-, z, rfl⟩ := hcell F hF
  have hopen : IsOpen (Q \ pointSet G drawing) := hQ.sdiff h.isClosed_pointSet
  exact ⟨hopen.connectedComponentIn, isPreconnected_connectedComponentIn,
    Set.disjoint_left.2 fun _ hx => (connectedComponentIn_subset _ _ hx).2⟩

 






theorem exists_target_crosscut [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) (hJ : J ⊆ pointSet G drawing)
    (hvw : v ≠ w) (hvJ : v ∈ J) (hwJ : w ∈ J)
    (hv : v ∈ closure F) (hw : w ∈ closure F) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P v w ∧ P \ {v, w} ⊆ F ∧ P ∩ J = {v, w} := by
  obtain ⟨hopen, hconn, hdisj⟩ :=
    isOpen_isPreconnected_disjoint_of_target_cell h hQ hcell hF
  obtain ⟨ws, -, -, -, hsub, harc, hmeet⟩ :=
    exists_crosscut_of_polyAccessible hopen hconn (hdisj.mono_right hJ) hvw hvJ hwJ
      (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hv)
      (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hw)
  exact ⟨poly ws, ⟨ws, rfl⟩, harc, hsub, hmeet⟩

 










theorem exists_target_crosscut_split [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) (hJ : J ⊆ pointSet G drawing) (hJc : IsJordanCurve J) (hFJ : F = inside J)
    (hvw : v ≠ w) (hvJ : v ∈ J) (hwJ : w ∈ J)
    (hv : v ∈ closure F) (hw : w ∈ closure F) (hcut : IsCutPair J v w A₁ A₂) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P v w ∧ P \ {v, w} ⊆ F ∧ P ∩ J = {v, w} ∧
      IsCrosscut J P v w ∧
      F = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∪ (P \ {v, w}) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      Disjoint (inside (A₁ ∪ P)) (P \ {v, w}) ∧
      Disjoint (inside (A₂ ∪ P)) (P \ {v, w}) ∧
      IsOpen (inside (A₁ ∪ P)) ∧ IsOpen (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) ∧
      closure (inside (A₂ ∪ P)) = inside (A₂ ∪ P) ∪ (A₂ ∪ P) := by
  obtain ⟨P, hPpoly, hParc, hPsub, hPmeet⟩ :=
    exists_target_crosscut h hpoly hQ hQK hcell hF hJ hvw hvJ hwJ hv hw
  have hcross : IsCrosscut J P v w :=
    ⟨hJc, hParc, hPpoly, hvJ, hwJ, by rw [← hFJ]; exact hPsub⟩
  have hpart := crosscut_cell_partition (fun _ hS => jordan_curve_theorem hS) hcross hcut
    hcross.hasArcCollars
  exact ⟨P, hPpoly, hParc, hPsub, hPmeet, hcross, by rw [hFJ]; exact hpart.1, hpart.2.1,
    hpart.2.2.1, hpart.2.2.2.1, hpart.2.2.2.2.1, hpart.2.2.2.2.2.1, hpart.2.2.2.2.2.2.1,
    hpart.2.2.2.2.2.2.2.1, hpart.2.2.2.2.2.2.2.2.1, hpart.2.2.2.2.2.2.2.2.2⟩

end TargetEar

 


theorem GeneratedPair.exists_target_crosscut
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {u v F : γ} (hu : u ∈ V(P.str.skel)) (hv : v ∈ V(P.str.skel))
    (huv : u ≠ v) (hF : F ∈ P.str.faces) (huF : P.str.sub u F)
    (hvF : P.str.sub v F) :
    ∃ A : Set Plane, IsPolygonal A ∧
      IsArcBetween A (P.tgt.pos u) (P.tgt.pos v) ∧
      A \ {P.tgt.pos u, P.tgt.pos v} ⊆ P.tgt.cell F ∧
      A ∩ frontier (P.tgt.cell F) = {P.tgt.pos u, P.tgt.pos v} := by
  have hucl : P.tgt.pos u ∈ closure (P.tgt.cell F) := by
    have hsub := P.tgt_isCellDecomposition.subset_closure
      (P.str.mem_cells_of_mem_vertexSet hu) (P.str.mem_cells_of_mem_faces hF) huF
    rw [P.tgt.cell_vertex hu] at hsub
    exact hsub (Set.mem_singleton _)
  have hvcl : P.tgt.pos v ∈ closure (P.tgt.cell F) := by
    have hsub := P.tgt_isCellDecomposition.subset_closure
      (P.str.mem_cells_of_mem_vertexSet hv) (P.str.mem_cells_of_mem_faces hF) hvF
    rw [P.tgt.cell_vertex hv] at hsub
    exact hsub (Set.mem_singleton _)
  have huJ : P.tgt.pos u ∈ frontier (P.tgt.cell F) := by
    rw [(P.tgt_isFaceJordan.isOpen hF).frontier_eq]
    refine ⟨hucl, ?_⟩
    exact fun hmem => Set.disjoint_left.1
      (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hF) hmem
      (P.tgt.pos_mem_skeletonSet hu)
  have hvJ : P.tgt.pos v ∈ frontier (P.tgt.cell F) := by
    rw [(P.tgt_isFaceJordan.isOpen hF).frontier_eq]
    refine ⟨hvcl, ?_⟩
    exact fun hmem => Set.disjoint_left.1
      (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hF) hmem
      (P.tgt.pos_mem_skeletonSet hv)
  letI : (P.str.skel.map P.tgt.pos).Finite := {
    finite_vertexSet := by
      rw [Graph.vertexSet_map]
      exact P.str.finite_vertexSet.image _
    finite_edgeSet := by
      rw [Graph.edgeSet_map]
      exact P.str.finite_edgeSet
  }
  have hcell : ∀ A ∈ {A : Set Plane | ∃ T ∈ P.str.faces, A = P.tgt.cell T},
      A ⊆ tgtDom \ tgtOuter ∧
        ∃ z, A = connectedComponentIn ((tgtDom \ tgtOuter) \ P.tgt.skeletonSet) z := by
    rintro A ⟨T, hT, rfl⟩
    exact P.tgt_face_isComponent hT
  have hfaceMem : P.tgt.cell F ∈
      {A : Set Plane | ∃ T ∈ P.str.faces, A = P.tgt.cell T} := ⟨F, hF, rfl⟩
  exact Schoenflies.exists_target_crosscut P.tgt.isDrawing P.tgt_isPolygonal
    P.tgtInterior_isOpen P.tgtInterior_frontier_subset
    hcell hfaceMem
    (P.tgt_isCellDecomposition.frontier_cell_subset_skeletonSet P.tgt_isFaceJordan hF)
    (fun h => huv (P.tgt.injOn_pos hu hv h)) huJ hvJ hucl hvcl

 

 


theorem earStepConstruction [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    EarStepConstruction P H Hdraw hH := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨w⟩ := exists_sourceEarStepData P H Hdraw hH
    B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  obtain ⟨A, hApoly, hAarc, hAsub, -⟩ :=
    T.exists_target_crosscut d.source_mem_skel d.target_mem_skel d.source_ne_target
      d.face_mem hsourceSub htargetSub
  obtain ⟨tgtPos, tgtDraw, earHomeo, htgt, htgtEdgePoly⟩ :=
    w.srcCrosscut.exists_matched_target hApoly hAarc hAsub
      (T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition d.face_mem)
  exact ⟨{
    splitData := d
    srcPos := w.srcPos
    srcDraw := w.srcDraw
    tgtPos := tgtPos
    tgtDraw := tgtDraw
    srcCrosscut := w.srcCrosscut
    tgtCrosscut := htgt
    earHomeo := earHomeo
    srcEdgePolygonal := w.srcEdgePolygonal
    tgtEdgePolygonal := htgtEdgePoly
    srcEarSet_eq := w.srcEarSet_eq
    vertexSet_subset := w.vertexSet_subset
  }⟩

 
theorem earStep [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) : EarStep P H Hdraw :=
  earStep_of_data hH (earStepConstruction P H Hdraw hH)

 
theorem transfer_of_ears_of_commonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P H Hdraw par :=
  transfer_of_ears_of_commonSubdivision_of_earStep hH hsub (earStep P H Hdraw hH)

 
theorem finite_transfer_toward_square_of_commonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par :=
  finite_transfer_toward_square_of_commonSubdivision_of_earStep hH hsub
    (earStep P H Hdraw hH)

 







section EndpointTransfer

variable {S : CellStructure γ} {R₁ R₂ : S.Realization} {D₁ D₂ Q J A₁ A₂ : Set Plane} {a b F : γ}

 

theorem CellStructure.Realization.pos_mem_closure_cell_congr
    (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂)
    (ha : a ∈ V(S.skel)) (hF : F ∈ S.faces) (hmem : R₁.pos a ∈ closure (R₁.cell F)) :
    R₂.pos a ∈ closure (R₂.cell F) := by
  have := h₂.subset_closure (S.mem_cells_of_mem_vertexSet ha) (S.mem_cells_of_mem_faces hF)
    (h₁.sub_of_pos_mem_closure_cell ha hF hmem)
  rw [R₂.cell_vertex ha] at this
  exact this (Set.mem_singleton _)

 










theorem exists_target_ear (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂)
    (hpoly : ∀ ⦃e⦄, e ∈ E(S.skel) → IsPolygonal (edgeArc R₂.drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ R₂.skeletonSet)
    (hcell : ∀ T ∈ S.faces, R₂.cell T ⊆ Q ∧
      ∃ z, R₂.cell T = connectedComponentIn (Q \ R₂.skeletonSet) z)
    (hF : F ∈ S.faces) (hJ : J ⊆ R₂.skeletonSet) (hJc : IsJordanCurve J)
    (hFJ : R₂.cell F = inside J)
    (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel)) (hab : R₂.pos a ≠ R₂.pos b)
    (haJ : R₂.pos a ∈ J) (hbJ : R₂.pos b ∈ J)
    (hacl : R₁.pos a ∈ closure (R₁.cell F)) (hbcl : R₁.pos b ∈ closure (R₁.cell F))
    (hcut : IsCutPair J (R₂.pos a) (R₂.pos b) A₁ A₂) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P (R₂.pos a) (R₂.pos b) ∧
      P \ {R₂.pos a, R₂.pos b} ⊆ R₂.cell F ∧ P ∩ J = {R₂.pos a, R₂.pos b} ∧
      IsCrosscut J P (R₂.pos a) (R₂.pos b) ∧
      R₂.cell F = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∪ (P \ {R₂.pos a, R₂.pos b}) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      Disjoint (inside (A₁ ∪ P)) (P \ {R₂.pos a, R₂.pos b}) ∧
      Disjoint (inside (A₂ ∪ P)) (P \ {R₂.pos a, R₂.pos b}) ∧
      IsOpen (inside (A₁ ∪ P)) ∧ IsOpen (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) ∧
      closure (inside (A₂ ∪ P)) = inside (A₂ ∪ P) ∪ (A₂ ∪ P) := by
  
  have hcell' : ∀ T ∈ {A : Set Plane | ∃ T ∈ S.faces, A = R₂.cell T},
      T ⊆ Q ∧ ∃ z, T = connectedComponentIn (Q \ pointSet R₂.graph R₂.drawing) z := by
    rintro T ⟨T', hT', rfl⟩
    exact hcell T' hT'
  have hpoly' : ∀ e ∈ E(R₂.graph), IsPolygonal (edgeArc R₂.drawing e) := by
    intro e he
    rw [CellStructure.Realization.edgeSet_graph] at he
    exact hpoly he
  have hdraw : IsDrawing R₂.graph R₂.drawing := R₂.isDrawing
  exact exists_target_crosscut_split hdraw hpoly' hQ hQK hcell'
    ⟨F, hF, rfl⟩ hJ hJc hFJ hab haJ hbJ
    (CellStructure.Realization.pos_mem_closure_cell_congr h₁ h₂ ha hF hacl)
    (CellStructure.Realization.pos_mem_closure_cell_congr h₁ h₂ hb hF hbcl) hcut

end EndpointTransfer

 




















 




theorem exists_overlay_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hnd : ∀ i ∈ s, ∃ a ∈ A i, ∃ b ∈ A i, a ≠ b) :
    ∃ G : Graph Plane Piece, Graph.Finite G ∧ IsDrawing G segmentDrawing ∧
      pointSet G segmentDrawing = ⋃ i ∈ s, A i := by
  classical
  
  have hex : ∀ i : ι, ∃ ws : List Plane, i ∈ s → A i = poly ws := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨ws, hws⟩ := hA i hi
      exact ⟨ws, fun _ => hws⟩
    · exact ⟨[], fun h => absurd h hi⟩
  choose vsf hvsf using hex
  
  set l : List ι := hs.toFinset.toList with hl
  have hlmem : ∀ i, i ∈ l ↔ i ∈ s := by
    intro i; rw [hl, Finset.mem_toList, hs.mem_toFinset]
  
  have hAcov : ∀ i ∈ s, cover (segsOf (vsf i)) = A i := by
    intro i hi
    obtain ⟨a, ha, b, hb, hab⟩ := hnd i hi
    rw [hvsf i hi] at ha hb ⊢
    exact cover_segsOf_eq ha hb hab
  have hcov : cover (l.flatMap fun i => segsOf (vsf i)) = ⋃ i ∈ s, A i := by
    rw [cover_flatMap_list]
    exact Set.iUnion_congr fun i => Set.iUnion_congr_Prop (hlmem i) fun hi => hAcov i hi
  have hnd' : ∀ P ∈ l.flatMap fun i => segsOf (vsf i), P.Nondeg := by
    intro P hP
    obtain ⟨i, -, hPi⟩ := List.mem_flatMap.1 hP
    exact segsOf_nondeg _ P hPi
  obtain ⟨G, hfin, hdraw, hpt⟩ := polygonal_overlay _ hnd'
  exact ⟨G, hfin, hdraw, by rw [hpt, hcov]⟩

 










example [Nonempty γ] {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}
    (h₀ : S₀.CombInvariants) (P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (hT : IsTransferOf T P H Hdraw par) {x : Plane} (hx : x ∈ srcDom) :
    par (T.src.carrier x) = P.src.carrier x ∧
      T.tgt.star (T.src.carrier x) ⊆ P.tgt.star (P.src.carrier x) :=
  ⟨hT.refines_src.parent_carrier P.src_isCellDecomposition T.src_isCellDecomposition hx,
    hT.refines_src.target_star_subset hT.refines_tgt (T.combInvariants h₀)
      P.src_isCellDecomposition T.src_isCellDecomposition hx⟩

end Schoenflies
