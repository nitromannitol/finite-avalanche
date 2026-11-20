/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/BoundaryContinuity.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.AccessibleJoin
import FiniteAvalanches.Support.Schoenflies.JordanClosed
import FiniteAvalanches.Support.Schoenflies.Inversion
import FiniteAvalanches.Support.Schoenflies.ModelCurve
import FiniteAvalanches.Support.Schoenflies.ArcComplementPrep
import FiniteAvalanches.Support.Schoenflies.Graph.Drawing

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




































open Metric Set Schoenflies
open scoped Graph

 









namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {C D : Set Plane}

 
def Nonboundary (drawing : β → ℝ → Plane) (C : Set Plane) (e : β) : Prop :=
  ¬ edgeArc drawing e ⊆ C

 








structure IsStageOn (G : Graph Plane β) (drawing : β → ℝ → Plane) (C D : Set Plane) : Prop where
   
  isDrawing : IsDrawing G drawing
   







  polygonal : ∀ ⦃e⦄, e ∈ E(G) → Nonboundary drawing C e →
    Schoenflies.IsPolygonal (edgeArc drawing e)
   
  disjoint : Disjoint C D
   
  vertex_mem : ∀ ⦃v⦄, v ∈ V(G) → v ∉ C → v ∈ D
   
  edge_split : ∀ ⦃e x y⦄, G.IsLink e x y →
    edgeArc drawing e ⊆ C ∨ edgeArc drawing e \ {x, y} ⊆ D
   
  isConnected_diff : IsConnected (pointSet G drawing \ C)

namespace IsStageOn

theorem notMem_of_mem_curve (h : IsStageOn G drawing C D) {z : Plane} (hz : z ∈ C) : z ∉ D :=
  fun hD => (h.disjoint.ne_of_mem hz hD) rfl

theorem notMem_curve (h : IsStageOn G drawing C D) {z : Plane} (hz : z ∈ D) : z ∉ C :=
  fun hzC => h.notMem_of_mem_curve hzC hz

 

theorem pointSet_diff_subset (h : IsStageOn G drawing C D) :
    pointSet G drawing \ C ⊆ D := by
  rintro p ⟨hp, hpC⟩
  rcases hp with hv | hp
  · exact h.vertex_mem hv hpC
  · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.1 hp
    obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet he
    rcases h.edge_split hl with hsub | hsub
    · exact absurd (hsub hpe) hpC
    · 
      by_cases hpxy : p ∈ ({x, y} : Set Plane)
      · rcases hpxy with rfl | rfl
        · exact h.vertex_mem hl.left_mem hpC
        · exact h.vertex_mem hl.right_mem hpC
      · exact hsub ⟨hpe, hpxy⟩

 
theorem edgeArc_inter_curve (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e) :
    edgeArc drawing e ∩ C ⊆ {x, y} := by
  rcases h.edge_split hl with hsub | hsub
  · exact absurd hsub hnb
  · rintro p ⟨hpe, hpC⟩
    by_contra hp
    exact h.notMem_of_mem_curve hpC (hsub ⟨hpe, hp⟩)

 
theorem left_mem_edgeArc (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) : x ∈ edgeArc drawing e :=
  (h.isDrawing.edge_isArcBetween hl).left_mem

theorem right_mem_edgeArc (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) : y ∈ edgeArc drawing e :=
  (h.isDrawing.edge_isArcBetween hl).right_mem

 
theorem edgeArc_subset_of_ends (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e) (hx : x ∈ D) (hy : y ∈ D) :
    edgeArc drawing e ⊆ D := by
  intro p hp
  by_cases hpxy : p ∈ ({x, y} : Set Plane)
  · simp only [mem_insert_iff, mem_singleton_iff] at hpxy
    rcases hpxy with rfl | rfl
    · exact hx
    · exact hy
  · rcases h.edge_split hl with hc | hd
    · exact absurd hc hnb
    · exact hd ⟨hp, hpxy⟩

 





 




theorem diff_subset_edgeArc [G.Finite] (h : IsStageOn G drawing C D)
    {e : β} {x y : Plane} (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e)
    (hx : x ∈ C) (hy : y ∈ C) : pointSet G drawing \ C ⊆ edgeArc drawing e := by
  classical
  
  set R : Set Plane := V(G) ∪ ⋃ f ∈ {f | f ∈ E(G) ∧ f ≠ e}, edgeArc drawing f with hRdef
  have hRclosed : IsClosed R := by
    refine (Graph.finite_vertexSet (G := G)).isCompact.isClosed.union ?_
    refine (Set.Finite.isCompact_biUnion ?_
      fun f hf => h.isDrawing.isCompact_edgeArc hf.1).isClosed
    exact (Graph.finite_edgeSet (G := G)).subset fun f hf => hf.1
  have hcover : pointSet G drawing ⊆ edgeArc drawing e ∪ R := by
    rintro p (hv | hp)
    · exact Or.inr (Or.inl hv)
    · obtain ⟨f, hf, hpf⟩ := mem_iUnion₂.1 hp
      by_cases hfe : f = e
      · exact Or.inl (hfe ▸ hpf)
      · exact Or.inr (Or.inr (mem_iUnion₂.2 ⟨f, ⟨hf, hfe⟩, hpf⟩))
  
  have hmeet : (pointSet G drawing \ C) ∩ (edgeArc drawing e ∩ R) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro p ⟨⟨-, hpC⟩, hpe, hpR⟩
    have hpV : p ∈ V(G) := by
      rcases hpR with hv | hp
      · exact hv
      · obtain ⟨f, ⟨hf, hfe⟩, hpf⟩ := mem_iUnion₂.1 hp
        exact h.isDrawing.arcs_meet_at_vertex hl.edge_mem hf (Ne.symm hfe) hpe hpf
    rcases h.isDrawing.vertex_mem_edgeArc hl hpV hpe with h1 | h1
    · exact hpC (h1 ▸ hx)
    · exact hpC (h1 ▸ hy)
  intro p hp
  by_contra hpe
  have hne1 : ((pointSet G drawing \ C) ∩ edgeArc drawing e).Nonempty := by
    obtain ⟨z, hze, hzC⟩ := not_subset.1 hnb
    exact ⟨z, ⟨edgeArc_subset_pointSet hl.edge_mem hze, hzC⟩, hze⟩
  have hne2 : ((pointSet G drawing \ C) ∩ R).Nonempty :=
    ⟨p, hp, (hcover hp.1).resolve_left hpe⟩
  have hcon := isPreconnected_closed_iff.1 h.isConnected_diff.2 _ _
    (h.isDrawing.isCompact_edgeArc hl.edge_mem).isClosed hRclosed
    (fun z hz => hcover hz.1) hne1 hne2
  rw [hmeet] at hcon
  exact hcon.ne_empty rfl

 

theorem isLink_of_ends_mem [G.Finite] (h : IsStageOn G drawing C D)
    {e : β} {x y : Plane} (hl : G.IsLink e x y) (hnb : Nonboundary drawing C e)
    (hx : x ∈ C) (hy : y ∈ C) {a b : Plane} (hab : a ≠ b)
    (ha : ∃ f, G.Inc f a ∧ Nonboundary drawing C f)
    (hb : ∃ f, G.Inc f b ∧ Nonboundary drawing C f) : G.IsLink e a b := by
  have hsub := h.diff_subset_edgeArc hl hnb hx hy
  
  have key : ∀ f, f ∈ E(G) → Nonboundary drawing C f → f = e := by
    intro f hfE hf
    obtain ⟨z, hzf, hzC⟩ := not_subset.1 hf
    have hze : z ∈ edgeArc drawing e :=
      hsub ⟨edgeArc_subset_pointSet hfE hzf, hzC⟩
    by_contra hfe
    have hzV : z ∈ V(G) :=
      h.isDrawing.arcs_meet_at_vertex hl.edge_mem hfE (Ne.symm hfe) hze hzf
    rcases h.isDrawing.vertex_mem_edgeArc hl hzV hze with h1 | h1
    · exact hzC (h1 ▸ hx)
    · exact hzC (h1 ▸ hy)
  obtain ⟨fa, hfa, hfanb⟩ := ha
  obtain ⟨fb, hfb, hfbnb⟩ := hb
  have hia : G.Inc e a := key fa hfa.edge_mem hfanb ▸ hfa
  have hib : G.Inc e b := key fb hfb.edge_mem hfbnb ▸ hfb
  have h1 := hia.eq_or_eq_of_isLink hl
  have h2 := hib.eq_or_eq_of_isLink hl
  rw [hl.isLink_iff]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hab
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩
  · exact absurd (h1.trans h2.symm) hab

end IsStageOn

 





 

def interiorPart (G : Graph Plane β) (drawing : β → ℝ → Plane) (D : Set Plane) : Set Plane :=
  (V(G) ∩ D) ∪ ⋃ e ∈ {e | e ∈ E(G) ∧ edgeArc drawing e ⊆ D}, edgeArc drawing e

theorem interiorPart_subset : interiorPart G drawing D ⊆ D := by
  rintro p (⟨-, hp⟩ | hp)
  · exact hp
  · obtain ⟨e, ⟨-, hsub⟩, hpe⟩ := mem_iUnion₂.1 hp
    exact hsub hpe

theorem interiorPart_subset_pointSet : interiorPart G drawing D ⊆ pointSet G drawing := by
  rintro p (⟨hp, -⟩ | hp)
  · exact Or.inl hp
  · obtain ⟨e, ⟨heE, -⟩, hpe⟩ := mem_iUnion₂.1 hp
    exact edgeArc_subset_pointSet heE hpe

theorem isClosed_interiorPart [G.Finite] (h : IsDrawing G drawing) :
    IsClosed (interiorPart G drawing D) := by
  refine ((Graph.finite_vertexSet (G := G)).inter_of_left D).isCompact.isClosed.union ?_
  refine (Set.Finite.isCompact_biUnion ?_ fun e he => h.isCompact_edgeArc he.1).isClosed
  exact (Graph.finite_edgeSet (G := G)).subset fun e he => he.1

 



def attachEdges (G : Graph Plane β) (drawing : β → ℝ → Plane) (S : Set Plane) : Set Plane :=
  S ∪ ⋃ e ∈ {e | e ∈ E(G) ∧ (edgeArc drawing e ∩ S).Nonempty}, edgeArc drawing e

theorem subset_attachEdges {S : Set Plane} : S ⊆ attachEdges G drawing S := subset_union_left

theorem isClosed_attachEdges [G.Finite] (h : IsDrawing G drawing) {S : Set Plane}
    (hS : IsClosed S) : IsClosed (attachEdges G drawing S) := by
  refine hS.union ?_
  refine (Set.Finite.isCompact_biUnion ?_ fun e he => h.isCompact_edgeArc he.1).isClosed
  exact (Graph.finite_edgeSet (G := G)).subset fun e he => he.1

namespace IsStageOn

variable (hcase : ∀ ⦃e : β⦄ ⦃x y : Plane⦄, G.IsLink e x y → Nonboundary drawing C e →
  x ∈ C → y ∉ C)

 

theorem edgeArc_inter_interiorPart (h : IsStageOn G drawing C D) {e : β} {x y : Plane}
    (hl : G.IsLink e x y) (hx : x ∈ C) :
    edgeArc drawing e ∩ interiorPart G drawing D ⊆ {y} := by
  rintro p ⟨hpe, hpL⟩
  have hpD : p ∈ D := interiorPart_subset hpL
  have hpV : p ∈ V(G) := by
    rcases hpL with ⟨hv, -⟩ | hp
    · exact hv
    · obtain ⟨f, ⟨hfE, hfD⟩, hpf⟩ := mem_iUnion₂.1 hp
      by_cases hfe : f = e
      · 
        exact absurd (hfD (hfe ▸ h.left_mem_edgeArc hl)) (h.notMem_of_mem_curve hx)
      · exact h.isDrawing.arcs_meet_at_vertex hl.edge_mem hfE (Ne.symm hfe) hpe hpf
  rcases h.isDrawing.vertex_mem_edgeArc hl hpV hpe with h1 | h1
  · exact absurd (h1 ▸ hpD) (h.notMem_of_mem_curve hx)
  · exact h1

 




theorem edgeArc_inter_interiorPart_subset (h : IsStageOn G drawing C D)
    {S S' : Set Plane} (hSc : IsClosed S) (hS'c : IsClosed S')
    (hunion : S ∪ S' = interiorPart G drawing D) (hinter : S ∩ S' = ∅)
    {e : β} (heE : e ∈ E(G)) (hmeet : (edgeArc drawing e ∩ S).Nonempty) :
    edgeArc drawing e ∩ interiorPart G drawing D ⊆ S := by
  obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heE
  obtain ⟨z, hze, hzS⟩ := hmeet
  have hzL : z ∈ interiorPart G drawing D := hunion ▸ Or.inl hzS
  have hzD : z ∈ D := interiorPart_subset hzL
  have hnb : Nonboundary drawing C e := fun hsub => h.notMem_of_mem_curve (hsub hze) hzD
  by_cases hxC : x ∈ C
  · 
    have hy := h.edgeArc_inter_interiorPart hl hxC
    intro p hp
    rw [show p = y from hy hp, ← show z = y from hy ⟨hze, hzL⟩]
    exact hzS
  · by_cases hyC : y ∈ C
    · 
      have hx := h.edgeArc_inter_interiorPart hl.symm hyC
      intro p hp
      rw [show p = x from hx hp, ← show z = x from hx ⟨hze, hzL⟩]
      exact hzS
    · 
      have hxD : x ∈ D := h.vertex_mem hl.left_mem hxC
      have hyD : y ∈ D := h.vertex_mem hl.right_mem hyC
      have heD : edgeArc drawing e ⊆ D := h.edgeArc_subset_of_ends hl hnb hxD hyD
      have heL : edgeArc drawing e ⊆ interiorPart G drawing D :=
        fun p hp => Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, heD⟩, hp⟩)
      have hconn : IsPreconnected (edgeArc drawing e) :=
        ((h.isDrawing.edge_isArcBetween hl).isArc.isConnected).2
      have hsub : edgeArc drawing e ⊆ S := by
        by_contra hcon
        obtain ⟨w, hwe, hwS⟩ := not_subset.1 hcon
        have hwS' : w ∈ S' := by
          have := heL hwe
          rw [← hunion] at this
          exact this.resolve_left hwS
        have := isPreconnected_closed_iff.1 hconn S S' hSc hS'c
          (fun p hp => by rw [← hunion] at heL; exact heL hp) ⟨z, hze, hzS⟩ ⟨w, hwe, hwS'⟩
        obtain ⟨v, -, hv⟩ := this
        rw [hinter] at hv
        exact hv
      exact fun p hp => hsub hp.1

include hcase in
 


theorem isPreconnected_interiorPart [G.Finite] (h : IsStageOn G drawing C D) :
    IsPreconnected (interiorPart G drawing D) := by
  classical
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcov hmt hmt'
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  set S : Set Plane := interiorPart G drawing D ∩ t with hSdef
  set S' : Set Plane := interiorPart G drawing D ∩ t' with hS'def
  have hSc : IsClosed S := (isClosed_interiorPart h.isDrawing).inter ht
  have hS'c : IsClosed S' := (isClosed_interiorPart h.isDrawing).inter ht'
  have hunion : S ∪ S' = interiorPart G drawing D := by
    refine subset_antisymm (fun p hp => hp.elim (fun h' => h'.1) (fun h' => h'.1)) ?_
    intro p hp
    rcases hcov hp with h' | h'
    · exact Or.inl ⟨hp, h'⟩
    · exact Or.inr ⟨hp, h'⟩
  have hinter : S ∩ S' = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro p ⟨⟨hp, hpt⟩, -, hpt'⟩
    rw [eq_empty_iff_forall_notMem] at hempty
    exact hempty p ⟨hp, hpt, hpt'⟩
  have hSsub : S ⊆ interiorPart G drawing D := fun p hp => hp.1
  have hS'sub : S' ⊆ interiorPart G drawing D := fun p hp => hp.1
  
  have hsel : ∀ R R' : Set Plane, IsClosed R → IsClosed R' → R ∪ R' = interiorPart G drawing D →
      R ∩ R' = ∅ → ∀ e ∈ E(G), (edgeArc drawing e ∩ R).Nonempty →
      edgeArc drawing e ∩ interiorPart G drawing D ⊆ R :=
    fun R R' hR hR' hu hi e he hm =>
      h.edgeArc_inter_interiorPart_subset hR hR' hu hi he hm
  have hSsel := hsel S S' hSc hS'c hunion hinter
  have hS'sel := hsel S' S hS'c hSc (by rw [union_comm]; exact hunion)
    (by rw [inter_comm]; exact hinter)
  
  have hcovX : pointSet G drawing \ C ⊆
      attachEdges G drawing S ∪ attachEdges G drawing S' := by
    rintro p hp
    have hpD : p ∈ D := h.pointSet_diff_subset hp
    rcases hp.1 with hv | hpe
    · have : p ∈ interiorPart G drawing D := Or.inl ⟨hv, hpD⟩
      rw [← hunion] at this
      exact this.elim (fun h' => Or.inl (subset_attachEdges h'))
        (fun h' => Or.inr (subset_attachEdges h'))
    · obtain ⟨e, heE, hpe⟩ := mem_iUnion₂.1 hpe
      obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heE
      have hnb : Nonboundary drawing C e := fun hsub => h.notMem_of_mem_curve (hsub hpe) hpD
      
      have hend : ∃ w, w ∈ edgeArc drawing e ∧ w ∈ interiorPart G drawing D := by
        by_cases hxC : x ∈ C
        · have hyC : y ∉ C := hcase hl hnb hxC
          exact ⟨y, h.right_mem_edgeArc hl, Or.inl ⟨hl.right_mem, h.vertex_mem hl.right_mem hyC⟩⟩
        · exact ⟨x, h.left_mem_edgeArc hl, Or.inl ⟨hl.left_mem, h.vertex_mem hl.left_mem hxC⟩⟩
      obtain ⟨w, hwe, hwL⟩ := hend
      rw [← hunion] at hwL
      rcases hwL with hwS | hwS
      · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, ⟨w, hwe, hwS⟩⟩, hpe⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, ⟨w, hwe, hwS⟩⟩, hpe⟩))
  
  have hdisjX : (pointSet G drawing \ C) ∩
      (attachEdges G drawing S ∩ attachEdges G drawing S') = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro p ⟨hp, hpT, hpT'⟩
    have hpD : p ∈ D := h.pointSet_diff_subset hp
    
    have hkey : ∀ R R' : Set Plane, R ⊆ interiorPart G drawing D →
        (∀ e ∈ E(G), (edgeArc drawing e ∩ R).Nonempty →
          edgeArc drawing e ∩ interiorPart G drawing D ⊆ R) →
        p ∈ attachEdges G drawing R → p ∈ attachEdges G drawing R' →
        p ∈ interiorPart G drawing D → p ∈ R := by
      rintro R R' hRsub hRsel (hpR | hpR) - hpL
      · exact hpR
      · obtain ⟨e, ⟨heE, hme⟩, hpe⟩ := mem_iUnion₂.1 hpR
        exact hRsel e heE hme ⟨hpe, hpL⟩
    have hpL : p ∈ interiorPart G drawing D := by
      rcases hpT with hpS | hpe
      · exact hSsub hpS
      · obtain ⟨e, ⟨heE, hme⟩, hpe⟩ := mem_iUnion₂.1 hpe
        rcases hpT' with hpS' | hpe'
        · exact hS'sub hpS'
        · obtain ⟨f, ⟨hfE, hmf⟩, hpf⟩ := mem_iUnion₂.1 hpe'
          by_cases hef : e = f
          · 
            obtain ⟨v, hve, hvS⟩ := hme
            have hvL : v ∈ interiorPart G drawing D := hSsub hvS
            have := hS'sel f hfE hmf ⟨hef ▸ hve, hvL⟩
            rw [eq_empty_iff_forall_notMem] at hinter
            exact absurd ⟨hvS, this⟩ (hinter v)
          · have : p ∈ V(G) := h.isDrawing.arcs_meet_at_vertex heE hfE hef hpe hpf
            exact Or.inl ⟨this, hpD⟩
    have h1 := hkey S S' hSsub hSsel hpT hpT' hpL
    have h2 := hkey S' S hS'sub hS'sel hpT' hpT hpL
    rw [eq_empty_iff_forall_notMem] at hinter
    exact hinter p ⟨h1, h2⟩
  obtain ⟨p, hpL, hpt⟩ := hmt
  obtain ⟨q, hqL, hqt'⟩ := hmt'
  have hne1 : ((pointSet G drawing \ C) ∩ attachEdges G drawing S).Nonempty :=
    ⟨p, ⟨interiorPart_subset_pointSet hpL, h.notMem_curve (interiorPart_subset hpL)⟩,
      subset_attachEdges ⟨hpL, hpt⟩⟩
  have hne2 : ((pointSet G drawing \ C) ∩ attachEdges G drawing S').Nonempty :=
    ⟨q, ⟨interiorPart_subset_pointSet hqL, h.notMem_curve (interiorPart_subset hqL)⟩,
      subset_attachEdges ⟨hqL, hqt'⟩⟩
  have hcon := isPreconnected_closed_iff.1 h.isConnected_diff.2 _ _
    (isClosed_attachEdges h.isDrawing hSc) (isClosed_attachEdges h.isDrawing hS'c)
    hcovX hne1 hne2
  rw [hdisjX] at hcon
  exact hcon.ne_empty rfl

 

 






theorem exists_crosscut [G.Finite] (h : IsStageOn G drawing C D) {a b : Plane}
    (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (ha : ∃ e, G.Inc e a ∧ Nonboundary drawing C e)
    (hb : ∃ e, G.Inc e b ∧ Nonboundary drawing C e) :
    ∃ P ⊆ pointSet G drawing, IsPolygonal P ∧ IsArcBetween P a b ∧
      P ∩ C = {a, b} ∧ P \ {a, b} ⊆ D := by
  classical
  by_cases hbig : ∃ (e : β) (x y : Plane),
      G.IsLink e x y ∧ Nonboundary drawing C e ∧ x ∈ C ∧ y ∈ C
  · 
    obtain ⟨e, x, y, hl, hnb, hx, hy⟩ := hbig
    have hlab : G.IsLink e a b := h.isLink_of_ends_mem hl hnb hx hy hab ha hb
    refine ⟨edgeArc drawing e, edgeArc_subset_pointSet hlab.edge_mem,
      h.polygonal hlab.edge_mem hnb, h.isDrawing.edge_isArcBetween hlab, ?_, ?_⟩
    · refine subset_antisymm (h.edgeArc_inter_curve hlab hnb) ?_
      rintro p (rfl | rfl)
      · exact ⟨h.left_mem_edgeArc hlab, haC⟩
      · exact ⟨h.right_mem_edgeArc hlab, hbC⟩
    · rcases h.edge_split hlab with hc | hd
      · exact absurd hc hnb
      · exact hd
  · 
    have hcase : ∀ ⦃e : β⦄ ⦃x y : Plane⦄, G.IsLink e x y → Nonboundary drawing C e →
        x ∈ C → y ∉ C := fun e x y hl hnb hx hy => hbig ⟨e, x, y, hl, hnb, hx, hy⟩
    obtain ⟨ea, ⟨ya, hla⟩, hanb⟩ := ha
    obtain ⟨eb, ⟨yb, hlb⟩, hbnb⟩ := hb
    have hyaD : ya ∈ D := h.vertex_mem hla.right_mem (hcase hla hanb haC)
    have hybD : yb ∈ D := h.vertex_mem hlb.right_mem (hcase hlb hbnb hbC)
    have hyaL : ya ∈ interiorPart G drawing D := Or.inl ⟨hla.right_mem, hyaD⟩
    have hybL : yb ∈ interiorPart G drawing D := Or.inl ⟨hlb.right_mem, hybD⟩
    have hLconn : IsConnected (interiorPart G drawing D) :=
      ⟨⟨ya, hyaL⟩, h.isPreconnected_interiorPart hcase⟩
    set EE : Set β := {e | e ∈ E(G) ∧ (edgeArc drawing e ⊆ D ∨ e = ea ∨ e = eb)} with hEEdef
    set Y : Set Plane := (V(G) ∩ D) ∪ ⋃ e ∈ EE, edgeArc drawing e with hYdef
    have hbi : (⋃ i ∈ (Sum.inl '' (V(G) ∩ D) ∪ Sum.inr '' EE : Set (Plane ⊕ β)),
        Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing) i) = Y := by
      rw [hYdef, biUnion_union, biUnion_image, biUnion_image]
      simp only [Sum.elim_inl, Sum.elim_inr, biUnion_of_singleton]
    
    have hYeq : Y = (interiorPart G drawing D ∪ edgeArc drawing ea) ∪ edgeArc drawing eb := by
      refine subset_antisymm ?_ ?_
      · rintro p (hp | hp)
        · exact Or.inl (Or.inl (Or.inl hp))
        · obtain ⟨e, ⟨heE, hcond⟩, hpe⟩ := mem_iUnion₂.1 hp
          rcases hcond with hD | rfl | rfl
          · exact Or.inl (Or.inl (Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, hD⟩, hpe⟩)))
          · exact Or.inl (Or.inr hpe)
          · exact Or.inr hpe
      · rintro p ((hp | hp) | hp)
        · rcases hp with hp | hp
          · exact Or.inl hp
          · obtain ⟨e, ⟨heE, hD⟩, hpe⟩ := mem_iUnion₂.1 hp
            exact Or.inr (mem_iUnion₂.2 ⟨e, ⟨heE, Or.inl hD⟩, hpe⟩)
        · exact Or.inr (mem_iUnion₂.2 ⟨ea, ⟨hla.edge_mem, Or.inr (Or.inl rfl)⟩, hp⟩)
        · exact Or.inr (mem_iUnion₂.2 ⟨eb, ⟨hlb.edge_mem, Or.inr (Or.inr rfl)⟩, hp⟩)
    have hYconn : IsPreconnected Y := by
      rw [hYeq]
      refine (IsConnected.union ⟨yb, Or.inl hybL, h.right_mem_edgeArc hlb⟩
        (IsConnected.union ⟨ya, hyaL, h.right_mem_edgeArc hla⟩ hLconn
          (h.isDrawing.edge_isArcBetween hla).isArc.isConnected)
        (h.isDrawing.edge_isArcBetween hlb).isArc.isConnected).2
    have hYpoint : Y ⊆ pointSet G drawing := by
      rintro p (⟨hp, -⟩ | hp)
      · exact Or.inl hp
      · obtain ⟨e, ⟨heE, -⟩, hpe⟩ := mem_iUnion₂.1 hp
        exact edgeArc_subset_pointSet heE hpe
    have haY : a ∈ Y := hYeq ▸ Or.inl (Or.inr (h.left_mem_edgeArc hla))
    have hbY : b ∈ Y := hYeq ▸ Or.inr (h.left_mem_edgeArc hlb)
    have hYcurve : Y ∩ C ⊆ {a, b} := by
      rintro p ⟨hpY, hpC⟩
      rw [hYeq] at hpY
      rcases hpY with (hp | hp) | hp
      · exact absurd hpC (h.notMem_curve (interiorPart_subset hp))
      · rcases h.edgeArc_inter_curve hla hanb ⟨hp, hpC⟩ with h1 | h1
        · exact Or.inl h1
        · exact absurd (h1 ▸ hpC) (h.notMem_curve hyaD)
      · rcases h.edgeArc_inter_curve hlb hbnb ⟨hp, hpC⟩ with h1 | h1
        · exact Or.inr h1
        · exact absurd (h1 ▸ hpC) (h.notMem_curve hybD)
    
    
    have hEEnb : ∀ e ∈ EE, Nonboundary drawing C e := by
      rintro e ⟨heG, hD | rfl | rfl⟩
      · intro hC
        obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet heG
        exact (h.disjoint.ne_of_mem (hC (h.left_mem_edgeArc hl)) (hD (h.left_mem_edgeArc hl))) rfl
      · exact hanb
      · exact hbnb
    have hfin : (Sum.inl '' (V(G) ∩ D) ∪ Sum.inr '' EE : Set (Plane ⊕ β)).Finite :=
      (((Graph.finite_vertexSet (G := G)).inter_of_left D).image _).union
        (((Graph.finite_edgeSet (G := G)).subset fun e he => he.1).image _)
    have hApoly : ∀ i ∈ (Sum.inl '' (V(G) ∩ D) ∪ Sum.inr '' EE : Set (Plane ⊕ β)),
        IsPolygonal (Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing) i) := by
      rintro (v | e) hi
      · exact ⟨[v], rfl⟩
      · have he : e ∈ EE := by
          rcases hi with ⟨w, -, hw⟩ | ⟨w, hw, hw'⟩
          · exact absurd hw (by simp)
          · exact (Sum.inr_injective hw') ▸ hw
        exact h.polygonal he.1 (hEEnb e he)
    obtain ⟨P, hPsub, hPpoly, hParc, hPcut, hPD⟩ :=
      exists_crosscut_arc_of_biUnion_finite (ι := Plane ⊕ β)
        (s := Sum.inl '' (V(G) ∩ D) ∪ Sum.inr '' EE)
        (A := Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing))
        (D := D) hfin hApoly (by rw [hbi]; exact hYconn) hab haC hbC
        (by rw [hbi]; exact haY) (by rw [hbi]; exact hbY)
        (by rw [hbi]; exact hYcurve)
        (by rw [hbi]; exact fun p hp => h.pointSet_diff_subset ⟨hYpoint hp.1, hp.2⟩)
    rw [hbi] at hPsub
    exact ⟨P, hPsub.trans hYpoint, hPpoly, hParc, hPcut, hPD⟩

end IsStageOn

end Graph
