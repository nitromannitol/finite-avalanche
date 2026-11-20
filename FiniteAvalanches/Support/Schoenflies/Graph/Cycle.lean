/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/Cycle.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import Mathlib.Combinatorics.Graph.Delete
import FiniteAvalanches.Support.Schoenflies.Graph.Walk

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 



































































open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y : α} {e f : β} {F : Set β} {W P D : List β}

namespace Graph

 





 




 
theorem IsWalk.of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) : G.IsWalk u W v :=
  h.mono deleteEdges_le

 
theorem IsWalk.notMem_of_deleteEdges (h : (G.deleteEdges F).IsWalk u W v) (hf : f ∈ W) :
    f ∉ F :=
  (mem_edgeSet_deleteEdges_iff.1 (h.edge_mem hf)).2

theorem IsPath.of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) : G.IsPath u W v :=
  h.mono deleteEdges_le

theorem IsPath.deleteEdges (h : G.IsPath u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).IsPath u W v :=
  h.anti deleteEdges_le (by simpa using h.left_mem)
    fun f hf ↦ mem_edgeSet_deleteEdges_iff.2 ⟨h.edge_mem hf, hW f hf⟩

theorem IsPath.notMem_of_deleteEdges (h : (G.deleteEdges F).IsPath u W v) (hf : f ∈ W) :
    f ∉ F :=
  h.isWalk.notMem_of_deleteEdges hf

theorem Reaches.of_deleteEdges (h : (G.deleteEdges F).Reaches u v) : G.Reaches u v :=
  h.mono deleteEdges_le

theorem IsWalk.reaches_deleteEdges (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).Reaches u v :=
  ⟨W, h.deleteEdges hW⟩

 

 


def IsCycleThrough (G : Graph α β) (e : β) (u v : α) (D : List β) : Prop :=
  G.IsLink e u v ∧ G.IsPath u D v ∧ e ∉ D

 
def LiesOnCycle (G : Graph α β) (e : β) : Prop := ∃ u v D, G.IsCycleThrough e u v D

theorem IsCycleThrough.isLink (h : G.IsCycleThrough e u v D) : G.IsLink e u v := h.1

theorem IsCycleThrough.isPath (h : G.IsCycleThrough e u v D) : G.IsPath u D v := h.2.1

theorem IsCycleThrough.notMem (h : G.IsCycleThrough e u v D) : e ∉ D := h.2.2

theorem IsCycleThrough.liesOnCycle (h : G.IsCycleThrough e u v D) : G.LiesOnCycle e :=
  ⟨u, v, D, h⟩

theorem liesOnCycle_iff : G.LiesOnCycle e ↔ ∃ u v D, G.IsCycleThrough e u v D := Iff.rfl

 

theorem LiesOnCycle.edge_mem (h : G.LiesOnCycle e) : e ∈ E(G) :=
  let ⟨_, _, _, hc⟩ := h; hc.isLink.edge_mem

 

theorem liesOnCycle_of_isLoopAt (h : G.IsLoopAt e x) : G.LiesOnCycle e :=
  ⟨x, x, [], h, .nil h.left_mem, List.not_mem_nil⟩

 

theorem liesOnCycle_of_parallel (h : G.IsLink e u v) (h' : G.IsLink f u v) (hef : e ≠ f) :
    G.LiesOnCycle e := by
  by_cases huv : u = v
  · subst huv
    exact liesOnCycle_of_isLoopAt h
  exact ⟨u, v, [f], h, .single h' huv, by simpa using hef⟩

 
theorem LiesOnCycle.mono (hHG : H ≤ G) (h : H.LiesOnCycle e) : G.LiesOnCycle e :=
  let ⟨u, v, D, hl, hP, hD⟩ := h
  ⟨u, v, D, hl.mono hHG, hP.mono hHG, hD⟩

 





 




theorem LiesOnCycle.deleteEdges_reaches (hl : G.IsLink e u v) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Reaches u v := by
  obtain ⟨u', v', D, hl', hP, hD⟩ := h
  
  have hR : (G.deleteEdges {e}).Reaches u' v' :=
    hP.isWalk.reaches_deleteEdges fun f hf hmem ↦ hD (Set.mem_singleton_iff.1 hmem ▸ hf)
  rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hR, hR.symm]

 


theorem LiesOnCycle.of_deleteEdges_reaches (hl : G.IsLink e u v)
    (h : (G.deleteEdges {e}).Reaches u v) : G.LiesOnCycle e := by
  obtain ⟨D, hD⟩ := h.exists_isPath
  exact ⟨u, v, D, hl, hD.of_deleteEdges, fun hmem ↦ hD.notMem_of_deleteEdges hmem rfl⟩

 

theorem liesOnCycle_iff_deleteEdges_reaches (hl : G.IsLink e u v) :
    G.LiesOnCycle e ↔ (G.deleteEdges {e}).Reaches u v :=
  ⟨LiesOnCycle.deleteEdges_reaches hl, LiesOnCycle.of_deleteEdges_reaches hl⟩

 



theorem IsWalk.reaches_deleteEdges_of_liesOnCycle (h : G.LiesOnCycle e) (hW : G.IsWalk u W v) :
    (G.deleteEdges {e}).Reaches u v := by
  induction hW with
  | nil hx => exact .refl (by simpa using hx)
  | @cons u w v f W hl _ ih =>
    refine Reaches.trans ?_ ih
    by_cases hfe : f = e
    · subst hfe
      exact h.deleteEdges_reaches hl
    · refine (IsWalk.single hl).reaches_deleteEdges fun g hg ↦ ?_
      obtain rfl : g = f := by simpa using hg
      simpa using hfe

 


theorem Connected.deleteEdges_singleton (hG : G.Connected) (h : G.LiesOnCycle e) :
    (G.deleteEdges {e}).Connected := by
  refine ⟨by simpa using hG.nonempty, fun u hu v hv ↦ ?_⟩
  rw [vertexSet_deleteEdges] at hu hv
  exact (hG.reaches hu hv).choose_spec.reaches_deleteEdges_of_liesOnCycle h

 





 

theorem IsPath.chord_liesOnCycle (hP : G.IsPath u P v) (hl : G.IsLink e u x) (hoff : e ∉ P)
    (hx : x ∈ G.walkVertices u P) : G.LiesOnCycle e := by
  obtain ⟨P₁, P₂, rfl, h₁, -, -⟩ := hP.split hx
  exact ⟨u, x, P₁, hl, h₁, fun hmem ↦ hoff (List.mem_append_left _ hmem)⟩

 

 


def IsAcyclic (G : Graph α β) : Prop := ∀ ⦃e⦄, e ∈ E(G) → ¬ G.LiesOnCycle e

 
theorem IsAcyclic.not_liesOnCycle (h : G.IsAcyclic) (e : β) : ¬ G.LiesOnCycle e :=
  fun hc ↦ h hc.edge_mem hc

theorem isAcyclic_iff : G.IsAcyclic ↔ ∀ e, ¬ G.LiesOnCycle e :=
  ⟨fun h e ↦ h.not_liesOnCycle e, fun h _ _ ↦ h _⟩

 

theorem IsAcyclic.not_isLoopAt (h : G.IsAcyclic) (e : β) (x : α) : ¬ G.IsLoopAt e x :=
  fun hloop ↦ h.not_liesOnCycle e (liesOnCycle_of_isLoopAt hloop)

 
theorem IsAcyclic.eq_of_isLink (h : G.IsAcyclic) (hl : G.IsLink e u v) (hl' : G.IsLink f u v) :
    e = f := by
  by_contra hef
  exact h.not_liesOnCycle e (liesOnCycle_of_parallel hl hl' hef)

 
theorem IsAcyclic.anti (hHG : H ≤ G) (h : G.IsAcyclic) : H.IsAcyclic :=
  fun _ _ hc ↦ h.not_liesOnCycle _ (hc.mono hHG)

theorem IsAcyclic.deleteEdges (h : G.IsAcyclic) (F : Set β) : (G.deleteEdges F).IsAcyclic :=
  h.anti deleteEdges_le

 



theorem IsAcyclic.mem_of_isLink_of_mem_walkVertices (hac : G.IsAcyclic) (hP : G.IsPath u P v)
    (hl : G.IsLink e u x) (hx : x ∈ G.walkVertices u P) : e ∈ P := by
  by_contra hoff
  exact hac.not_liesOnCycle e (hP.chord_liesOnCycle hl hoff hx)

 

 


def IsBridge (G : Graph α β) (e : β) : Prop := e ∈ E(G) ∧ ¬ G.LiesOnCycle e

theorem IsBridge.edge_mem (h : G.IsBridge e) : e ∈ E(G) := h.1

theorem IsBridge.not_liesOnCycle (h : G.IsBridge e) : ¬ G.LiesOnCycle e := h.2

 
theorem IsBridge.not_reaches (h : G.IsBridge e) (hl : G.IsLink e u v) :
    ¬ (G.deleteEdges {e}).Reaches u v :=
  fun hR ↦ h.not_liesOnCycle (LiesOnCycle.of_deleteEdges_reaches hl hR)

 
theorem isBridge_of_not_reaches (hl : G.IsLink e u v)
    (h : ¬ (G.deleteEdges {e}).Reaches u v) : G.IsBridge e :=
  ⟨hl.edge_mem, fun hc ↦ h (hc.deleteEdges_reaches hl)⟩

 

theorem isBridge_iff_not_reaches (hl : G.IsLink e u v) :
    G.IsBridge e ↔ ¬ (G.deleteEdges {e}).Reaches u v :=
  ⟨fun h ↦ h.not_reaches hl, isBridge_of_not_reaches hl⟩

 
theorem IsBridge.not_isLoopAt (h : G.IsBridge e) (x : α) : ¬ G.IsLoopAt e x :=
  fun hloop ↦ h.not_liesOnCycle (liesOnCycle_of_isLoopAt hloop)

 


theorem isAcyclic_iff_forall_isBridge : G.IsAcyclic ↔ ∀ e ∈ E(G), G.IsBridge e :=
  ⟨fun h _ he ↦ ⟨he, h he⟩, fun h _ he ↦ (h _ he).not_liesOnCycle⟩

theorem IsAcyclic.isBridge (h : G.IsAcyclic) (he : e ∈ E(G)) : G.IsBridge e := ⟨he, h he⟩

end Graph
