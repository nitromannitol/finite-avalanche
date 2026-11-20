/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/CycleJordan.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Concatenate
import FiniteAvalanches.Support.Schoenflies.Graph.Cycle
import FiniteAvalanches.Support.Schoenflies.Graph.Drawing
import FiniteAvalanches.Support.Schoenflies.Polygonal

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 

















































open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z : Plane} {W D : List β}

 

 

def edgesCover (drawing : β → ℝ → Plane) (W : List β) : Set Plane :=
  ⋃ e ∈ W, edgeArc drawing e

theorem mem_edgesCover_iff :
    z ∈ edgesCover drawing W ↔ ∃ e ∈ W, z ∈ edgeArc drawing e := by
  simp [edgesCover]

theorem mem_edgesCover (he : e ∈ W) (hz : z ∈ edgeArc drawing e) : z ∈ edgesCover drawing W :=
  mem_edgesCover_iff.2 ⟨e, he, hz⟩

@[simp]
theorem edgesCover_nil : edgesCover drawing ([] : List β) = ∅ := by
  simp [edgesCover]

@[simp]
theorem edgesCover_cons :
    edgesCover drawing (e :: W) = edgeArc drawing e ∪ edgesCover drawing W := by
  ext z
  simp [edgesCover]

theorem edgesCover_mono (h : W ⊆ D) : edgesCover drawing W ⊆ edgesCover drawing D :=
  fun _ hz ↦ let ⟨_, he, hze⟩ := mem_edgesCover_iff.1 hz; mem_edgesCover (h he) hze

 
theorem edgesCover_subset_pointSet (hW : ∀ e ∈ W, e ∈ E(G)) :
    edgesCover drawing W ⊆ pointSet G drawing := by
  intro z hz
  obtain ⟨e, he, hze⟩ := mem_edgesCover_iff.1 hz
  exact edgeArc_subset_pointSet (hW e he) hze

 




 

theorem IsDrawing.ne_of_isLink (h : IsDrawing G drawing) (hl : G.IsLink e u v) : u ≠ v := by
  rintro rfl
  obtain ⟨g, -, hinj, -, hg0, hg1⟩ := h.edge_isArcBetween hl
  have : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (hg0.trans hg1.symm)
  norm_num at this

theorem IsDrawing.not_isLoopAt (h : IsDrawing G drawing) (e : β) (u : Plane) :
    ¬ G.IsLoopAt e u :=
  fun hloop ↦ h.ne_of_isLink hloop rfl

 




 





theorem IsDrawing.first_edge_meets_rest (h : IsDrawing G drawing) (hl : G.IsLink e u w)
    (hW : ∀ f ∈ W, f ∈ E(G)) (hfresh : u ∉ G.walkVertices w W)
    (hze : z ∈ edgeArc drawing e) (hzW : z ∈ edgesCover drawing W) : z = w := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzW
  
  have hef : e ≠ f := by
    rintro rfl
    exact hfresh (mem_walkVertices_of_mem_covered ⟨e, hf, hl.inc_left⟩)
  obtain ⟨-, hinc, hincf⟩ := h.edge_inter hl.edge_mem (hW f hf) hef hze hzf
  rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
  · exact absurd (mem_walkVertices_of_mem_covered ⟨f, hf, hincf⟩) hfresh
  · rfl

 






theorem IsDrawing.path_isArcBetween (h : IsDrawing G drawing) (hP : G.IsPath u W v)
    (hne : W ≠ []) : IsArcBetween (edgesCover drawing W) u v := by
  induction hP with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hP hfresh ih =>
    rcases eq_or_ne W [] with rfl | hW
    · 
      obtain rfl : w = v := hP.isWalk.eq_of_nil
      simpa using h.edge_isArcBetween hl
    · refine edgesCover_cons ▸ (h.edge_isArcBetween hl).concatenate (ih hW) ?_
      exact fun z hze hzW ↦
        h.first_edge_meets_rest hl (fun f hf ↦ hP.edge_mem hf) hfresh hze hzW

 

 


theorem IsDrawing.detour_isArcBetween (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    IsArcBetween (edgesCover drawing D) u v := by
  refine h.path_isArcBetween hc.isPath fun hD ↦ ?_
  exact h.ne_of_isLink hc.isLink (hD ▸ hc.isPath.isWalk).eq_of_nil

 


theorem IsDrawing.detour_meets_edge (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D)
    (hzD : z ∈ edgesCover drawing D) (hze : z ∈ edgeArc drawing e) : z = u ∨ z = v := by
  obtain ⟨f, hf, hzf⟩ := mem_edgesCover_iff.1 hzD
  have hef : e ≠ f := fun hEq ↦ hc.notMem (hEq ▸ hf)
  obtain ⟨-, hinc, -⟩ :=
    h.edge_inter hc.isLink.edge_mem (hc.isPath.edge_mem hf) hef hze hzf
  exact hinc.eq_or_eq_of_isLink hc.isLink

 


theorem IsDrawing.cycle_inter (h : IsDrawing G drawing) (hc : G.IsCycleThrough e u v D) :
    edgesCover drawing D ∩ edgeArc drawing e = {u, v} := by
  have hD := h.detour_isArcBetween hc
  have hE := h.edge_isArcBetween hc.isLink
  refine Set.eq_of_subset_of_subset (fun z hz ↦ h.detour_meets_edge hc hz.1 hz.2) ?_
  rintro z (rfl | rfl)
  exacts [⟨hD.left_mem, hE.left_mem⟩, ⟨hD.right_mem, hE.right_mem⟩]

 


theorem IsDrawing.cycle_isJordanCurve (h : IsDrawing G drawing)
    (hc : G.IsCycleThrough e u v D) : IsJordanCurve (edgesCover drawing (e :: D)) := by
  have hJ : IsJordanCurve (edgesCover drawing D ∪ edgeArc drawing e) :=
    IsJordanCurve.of_two_arcs (h.detour_isArcBetween hc)
      (h.edge_isArcBetween hc.isLink).reverse fun z hzD hze ↦ h.detour_meets_edge hc hzD hze
  rw [edgesCover_cons, Set.union_comm]
  exact hJ

 
theorem IsWalk.left_mem_edgesCover {u v : Plane} {W : List β} (hW : G.IsWalk u W v)
    (hd : IsDrawing G drawing) (hne : W ≠ []) : u ∈ edgesCover drawing W := by
  cases hW with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_edgesCover (List.mem_cons_self ..) (hd.edge_isArcBetween hl).left_mem

 

theorem IsDrawing.isPolygonal_edgesCover (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), Schoenflies.IsPolygonal (edgeArc drawing f)) :
    ∀ {u v : Plane} {W : List β}, G.IsWalk u W v → W ≠ [] →
      Schoenflies.IsPolygonal (edgesCover drawing W) := by
  intro u v W hW
  induction hW with
  | nil => exact fun h => absurd rfl h
  | @cons u w v f W hl hW ih =>
    intro _
    rcases eq_or_ne W [] with rfl | hWne
    · simpa using hpoly f hl.edge_mem
    · rw [edgesCover_cons]
      exact ((hpoly f hl.edge_mem).union (ih hWne)
        ⟨w, (hd.edge_isArcBetween hl).right_mem, hW.left_mem_edgesCover hd hWne⟩)

end Graph
