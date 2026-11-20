/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/CombinatorialInvariance.lean.
-/
import Mathlib.Combinatorics.Graph.Maps
import FiniteAvalanches.Support.Schoenflies.Graph.Drawing
import FiniteAvalanches.Support.Schoenflies.Graph.TwoConnected

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 











































































open Set Schoenflies
open scoped Graph

namespace Graph

variable {α α' β : Type*} {G : Graph α β} {f : α → α'} {u v x : α} {W : List β}

theorem IsWalk.map (f : α → α') (h : G.IsWalk u W v) : (G.map f).IsWalk (f u) W (f v) := by
  induction h with
  | nil hx => exact .nil (by simpa using Set.mem_image_of_mem f hx)
  | cons hl _ ih => exact .cons (hl.map f) ih

theorem Reaches.map (f : α → α') (h : G.Reaches u v) : (G.map f).Reaches (f u) (f v) :=
  ⟨h.choose, h.choose_spec.map f⟩

theorem Connected.map (f : α → α') (h : G.Connected) : (G.map f).Connected := by
  obtain ⟨⟨u, hu⟩, hreach⟩ := h
  refine ⟨⟨f u, by simpa using Set.mem_image_of_mem f hu⟩, ?_⟩
  rintro a ha b hb
  simp only [vertexSet_map, Set.mem_image] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  exact (hreach ha' hb').map f

theorem HasThreeVertices.map (hf : InjOn f V(G)) (h : G.HasThreeVertices) :
    (G.map f).HasThreeVertices := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  have hmem : ∀ {z}, z ∈ V(G) → f z ∈ V(G.map f) := fun hz => by
    simpa using Set.mem_image_of_mem f hz
  exact ⟨f p, hmem hp, f q, hmem hq, f r, hmem hr, fun hcon => hpq (hf hp hq hcon),
    fun hcon => hpr (hf hp hr hcon), fun hcon => hqr (hf hq hr hcon)⟩

 
theorem map_deleteVerts_singleton (hf : InjOn f V(G)) (hx : x ∈ V(G)) :
    (G.map f).deleteVerts {f x} = (G.deleteVerts {x}).map f := by
  refine Graph.ext ?_ ?_
  · rw [vertexSet_deleteVerts, vertexSet_map, vertexSet_map, vertexSet_deleteVerts]
    rw [hf.image_sdiff_subset (Set.singleton_subset_iff.2 hx), Set.image_singleton]
  · intro e a b
    rw [deleteVerts_isLink]
    simp only [map_isLink, Relation.map_apply, deleteVerts_isLink, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨p, q, hpq, rfl, rfl⟩, hp, hq⟩
      exact ⟨p, q, ⟨hpq, fun h => hp (by rw [h]), fun h => hq (by rw [h])⟩, rfl, rfl⟩
    · rintro ⟨p, q, ⟨hpq, hp, hq⟩, rfl, rfl⟩
      exact ⟨⟨p, q, hpq, rfl, rfl⟩, fun h => hp (hf hpq.left_mem hx h),
        fun h => hq (hf hpq.right_mem hx h)⟩

theorem IsTwoConnected.map (hf : InjOn f V(G)) (h : G.IsTwoConnected) :
    (G.map f).IsTwoConnected where
  hasThreeVertices := h.hasThreeVertices.map hf
  connected := h.connected.map f
  deleteVerts_connected := by
    intro a ha
    simp only [vertexSet_map, Set.mem_image] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [map_deleteVerts_singleton hf hx]
    exact (h.deleteVerts_connected hx).map f

 
theorem map_map_invFunOn [Nonempty α] (hf : InjOn f V(G)) :
    (G.map f).map (Function.invFunOn f V(G)) = G := by
  have key : G.map (Function.invFunOn f V(G) ∘ f) = G.map id :=
    map_eq_of_eqOn fun z hz => hf.leftInvOn_invFunOn hz
  rw [map_map, key, map_id]

theorem connected_map_iff (hf : InjOn f V(G)) : (G.map f).Connected ↔ G.Connected := by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  obtain ⟨a, ha⟩ := h.nonempty
  rw [vertexSet_map] at ha
  obtain ⟨z, hz, -⟩ := ha
  have : Nonempty α := ⟨z⟩
  have himg : InjOn (Function.invFunOn f V(G)) V(G.map f) := by
    rw [vertexSet_map]; exact Function.invFunOn_injOn_image f V(G)
  have := h.map (Function.invFunOn f V(G))
  rwa [map_map_invFunOn hf] at this

theorem isTwoConnected_map_iff (hf : InjOn f V(G)) :
    (G.map f).IsTwoConnected ↔ G.IsTwoConnected := by
  refine ⟨fun h => ?_, fun h => h.map hf⟩
  obtain ⟨a, ha⟩ := h.connected.nonempty
  rw [vertexSet_map] at ha
  obtain ⟨z, hz, -⟩ := ha
  have : Nonempty α := ⟨z⟩
  have himg : InjOn (Function.invFunOn f V(G)) V(G.map f) := by
    rw [vertexSet_map]; exact Function.invFunOn_injOn_image f V(G)
  have := h.map himg
  rwa [map_map_invFunOn hf] at this

 

variable {δ : Type*} {H K : Graph Plane δ} {drawing : δ → ℝ → Plane}

theorem pointSet_mono (h : H ≤ K) : pointSet H drawing ⊆ pointSet K drawing :=
  Set.union_subset_union h.vertexSet_mono
    (Set.biUnion_subset_biUnion_left h.edgeSet_mono)

end Graph

namespace Schoenflies

open Graph

variable {γ : Type*}

 












structure CellStructure (γ : Type*) where
   
  skel : Graph γ γ
   
  faces : Set γ
   
  outerGraph : Graph γ γ
   
  outerGraph_le : outerGraph ≤ skel
   


  boundary : γ → List γ
   
  sub : γ → γ → Prop
   
  finite_vertexSet : V(skel).Finite
   
  finite_edgeSet : E(skel).Finite
   
  finite_faces : faces.Finite
   
  disjoint_vertexSet_edgeSet : Disjoint V(skel) E(skel)
   
  disjoint_faces_vertexSet : Disjoint faces V(skel)
   
  disjoint_faces_edgeSet : Disjoint faces E(skel)

namespace CellStructure

variable (S : CellStructure γ)

 
def cells : Set γ := V(S.skel) ∪ E(S.skel) ∪ S.faces

 
def outerCells : Set γ := V(S.outerGraph) ∪ E(S.outerGraph)

 
def supercells (σ : γ) : Set γ := {τ | S.sub σ τ}

 

def MeetsOuter (τ : γ) : Prop := ∃ κ ∈ S.outerCells, S.sub κ τ

theorem mem_supercells {σ τ : γ} : τ ∈ S.supercells σ ↔ S.sub σ τ := Iff.rfl

theorem supercells_subset_of_sub (htrans : ∀ ⦃a b c⦄, S.sub a b → S.sub b c → S.sub a c)
    {σ τ : γ} (h : S.sub σ τ) :
    S.supercells τ ⊆ S.supercells σ := fun _ hρ => htrans h hρ

 

 










structure Realization (S : CellStructure γ) where
   
  pos : γ → Plane
   
  drawing : γ → ℝ → Plane
   
  injOn_pos : InjOn pos V(S.skel)
   
  isDrawing : IsDrawing (S.skel.map pos) drawing
   
  cell : γ → Set Plane
   
  cell_vertex : ∀ ⦃v⦄, v ∈ V(S.skel) → cell v = {pos v}
   
  cell_edge : ∀ ⦃e x y⦄, S.skel.IsLink e x y → cell e = edgeArc drawing e \ {pos x, pos y}

namespace Realization

variable {S}
variable (R : S.Realization)

 
def graph : Graph Plane γ := S.skel.map R.pos

@[simp] theorem vertexSet_graph : V(R.graph) = R.pos '' V(S.skel) := vertexSet_map _ _

@[simp] theorem edgeSet_graph : E(R.graph) = E(S.skel) := edgeSet_map _ _

instance finite_graph : (R.graph).Finite where
  finite_vertexSet := by rw [vertexSet_graph]; exact S.finite_vertexSet.image _
  finite_edgeSet := by rw [edgeSet_graph]; exact S.finite_edgeSet

 
def skeletonSet : Set Plane := pointSet R.graph R.drawing

 
def outerSet : Set Plane := pointSet (S.outerGraph.map R.pos) R.drawing

 
def nonboundary : Set Plane := R.skeletonSet \ R.outerSet

 

def star (σ : γ) : Set Plane := ⋃ τ ∈ S.supercells σ, closure (R.cell τ)

theorem outerSet_subset_skeletonSet : R.outerSet ⊆ R.skeletonSet :=
  pointSet_mono (S.outerGraph_le.map R.pos)

theorem isCompact_skeletonSet : IsCompact R.skeletonSet :=
  @IsDrawing.isCompact_pointSet _ _ _ R.finite_graph R.isDrawing

 





theorem cell_subset_skeletonSet {R : S.Realization} {κ : γ}
    (hκ : κ ∈ V(S.skel) ∪ E(S.skel)) : R.cell κ ⊆ R.skeletonSet := by
  rcases hκ with hv | he
  · rw [R.cell_vertex hv]
    exact Set.singleton_subset_iff.2 (vertexSet_subset_pointSet
      (by rw [Realization.vertexSet_graph]; exact ⟨κ, hv, rfl⟩))
  · obtain ⟨a, b, hl⟩ := exists_isLink_of_mem_edgeSet he
    rw [R.cell_edge hl]
    exact Set.sdiff_subset.trans (edgeArc_subset_pointSet
      (by rw [Realization.edgeSet_graph]; exact he))

end Realization

 

 













structure SkeletonHomeo {S : CellStructure γ} (R₁ R₂ : S.Realization) where
   
  toFun : Plane → Plane
   
  invFun : Plane → Plane
   
  continuousOn_toFun : ContinuousOn toFun R₁.skeletonSet
   
  continuousOn_invFun : ContinuousOn invFun R₂.skeletonSet
   
  leftInvOn : LeftInvOn invFun toFun R₁.skeletonSet
   
  rightInvOn : RightInvOn invFun toFun R₂.skeletonSet
   
  pos_apply : ∀ ⦃v⦄, v ∈ V(S.skel) → toFun (R₁.pos v) = R₂.pos v
   
  edgeArc_image : ∀ ⦃e⦄, e ∈ E(S.skel) → toFun '' edgeArc R₁.drawing e = edgeArc R₂.drawing e

namespace SkeletonHomeo

variable {S} {R₁ R₂ : S.Realization} (g : SkeletonHomeo R₁ R₂)

 

theorem image_pointSet_map {H : Graph γ γ} (hH : H ≤ S.skel) :
    g.toFun '' pointSet (H.map R₁.pos) R₁.drawing = pointSet (H.map R₂.pos) R₂.drawing := by
  rw [pointSet, pointSet, Set.image_union, Set.image_iUnion₂]
  congr 1
  · rw [vertexSet_map, vertexSet_map, ← Set.image_comp]
    exact Set.image_congr fun v hv => g.pos_apply (hH.vertexSet_mono hv)
  · rw [edgeSet_map]
    exact Set.iUnion₂_congr fun e he => g.edgeArc_image (hH.edgeSet_mono he)

theorem image_skeletonSet : g.toFun '' R₁.skeletonSet = R₂.skeletonSet :=
  g.image_pointSet_map le_rfl

 

theorem image_outerSet : g.toFun '' R₁.outerSet = R₂.outerSet :=
  g.image_pointSet_map S.outerGraph_le

theorem injOn : InjOn g.toFun R₁.skeletonSet := g.leftInvOn.injOn

 
def symm : SkeletonHomeo R₂ R₁ where
  toFun := g.invFun
  invFun := g.toFun
  continuousOn_toFun := g.continuousOn_invFun
  continuousOn_invFun := g.continuousOn_toFun
  leftInvOn := g.rightInvOn
  rightInvOn := g.leftInvOn
  pos_apply := by
    intro v hv
    have hmem : R₁.pos v ∈ R₁.skeletonSet :=
      vertexSet_subset_pointSet (by rw [Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)
    rw [← g.pos_apply hv, g.leftInvOn hmem]
  edgeArc_image := by
    intro e he
    have hsub : edgeArc R₁.drawing e ⊆ R₁.skeletonSet :=
      edgeArc_subset_pointSet (by rwa [Realization.edgeSet_graph])
    rw [← g.edgeArc_image he]
    exact g.leftInvOn.image_image' hsub

@[simp] theorem symm_toFun : g.symm.toFun = g.invFun := rfl

 


theorem image_nonboundary : g.toFun '' R₁.nonboundary = R₂.nonboundary := by
  have : g.toFun '' (R₁.skeletonSet \ R₁.outerSet) = R₂.skeletonSet \ R₂.outerSet := by
    rw [g.injOn.image_sdiff_subset R₁.outerSet_subset_skeletonSet, g.image_skeletonSet,
      g.image_outerSet]
  exact this

 


theorem isConnected_nonboundary_iff (g : SkeletonHomeo R₁ R₂) :
    IsConnected R₁.nonboundary ↔ IsConnected R₂.nonboundary := by
  constructor
  · intro h
    rw [← g.image_nonboundary]
    exact h.image _ (g.continuousOn_toFun.mono Set.sdiff_subset)
  · intro h
    rw [← g.symm.image_nonboundary]
    exact h.image _ (g.symm.continuousOn_toFun.mono Set.sdiff_subset)

theorem isPreconnected_nonboundary_iff (g : SkeletonHomeo R₁ R₂) :
    IsPreconnected R₁.nonboundary ↔ IsPreconnected R₂.nonboundary := by
  constructor
  · intro h
    rw [← g.image_nonboundary]
    exact h.image _ (g.continuousOn_toFun.mono Set.sdiff_subset)
  · intro h
    rw [← g.symm.image_nonboundary]
    exact h.image _ (g.symm.continuousOn_toFun.mono Set.sdiff_subset)

end SkeletonHomeo

 

variable {S}

 

theorem Realization.graph_eq_map (R : S.Realization) : R.graph = S.skel.map R.pos := rfl

theorem Realization.edgeSet_graph_congr (R₁ R₂ : S.Realization) : E(R₁.graph) = E(R₂.graph) := by
  rw [Realization.edgeSet_graph, Realization.edgeSet_graph]

 
theorem Realization.connected_congr (R₁ R₂ : S.Realization) :
    R₁.graph.Connected ↔ R₂.graph.Connected :=
  (connected_map_iff R₁.injOn_pos).trans (connected_map_iff R₂.injOn_pos).symm

 


theorem Realization.isTwoConnected_congr (R₁ R₂ : S.Realization) :
    R₁.graph.IsTwoConnected ↔ R₂.graph.IsTwoConnected :=
  (isTwoConnected_map_iff R₁.injOn_pos).trans (isTwoConnected_map_iff R₂.injOn_pos).symm

 



theorem Realization.star_mono (R : S.Realization) {σ τ : γ}
    (h : S.supercells σ ⊆ S.supercells τ) : R.star σ ⊆ R.star τ :=
  Set.biUnion_subset_biUnion_left h

 
theorem Realization.star_transfer (R₁ R₂ : S.Realization) {σ τ : γ}
    (h : S.supercells σ ⊆ S.supercells τ) :
    R₁.star σ ⊆ R₁.star τ ∧ R₂.star σ ⊆ R₂.star τ :=
  ⟨R₁.star_mono h, R₂.star_mono h⟩

 
theorem Realization.star_subset_of_sub (R : S.Realization)
    (htrans : ∀ ⦃a b c⦄, S.sub a b → S.sub b c → S.sub a c) {σ τ : γ} (h : S.sub σ τ) :
    R.star τ ⊆ R.star σ :=
  R.star_mono (S.supercells_subset_of_sub htrans h)

 

def OuterEdgeUniqueFace (S : CellStructure γ) : Prop :=
  ∀ ⦃e⦄, e ∈ E(S.outerGraph) → ∃! F, F ∈ S.faces ∧ S.sub e F

 


theorem outerEdge_face_corresponds (h : OuterEdgeUniqueFace S) {e : γ}
    (he : e ∈ E(S.outerGraph)) :
    ∃ F, F ∈ S.faces ∧ S.sub e F ∧ ∀ T, T ∈ S.faces → S.sub e T → T = F := by
  obtain ⟨F, ⟨hF, hsub⟩, huniq⟩ := h he
  exact ⟨F, hF, hsub, fun T hT hTsub => huniq T ⟨hT, hTsub⟩⟩

 















theorem combinatorial_invariance {R₁ R₂ : S.Realization} (g : SkeletonHomeo R₁ R₂) :
    (E(R₁.graph) = E(R₂.graph) ∧
      (R₁.graph.IsTwoConnected ↔ R₂.graph.IsTwoConnected) ∧
      g.toFun '' R₁.outerSet = R₂.outerSet) ∧
    (g.toFun '' R₁.nonboundary = R₂.nonboundary ∧
      (IsConnected R₁.nonboundary ↔ IsConnected R₂.nonboundary)) ∧
    (∀ σ τ : γ, S.supercells σ ⊆ S.supercells τ →
      R₁.star σ ⊆ R₁.star τ ∧ R₂.star σ ⊆ R₂.star τ) :=
  ⟨⟨R₁.edgeSet_graph_congr R₂, R₁.isTwoConnected_congr R₂, g.image_outerSet⟩,
    ⟨g.image_nonboundary, g.isConnected_nonboundary_iff⟩,
    fun _ _ h => Realization.star_transfer R₁ R₂ h⟩

end CellStructure

end Schoenflies
