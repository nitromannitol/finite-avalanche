/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/TwoConnected.lean.
-/
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Data.Set.Card
import FiniteAvalanches.Support.Schoenflies.Graph.Walk

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




























































































open Set

variable {α β : Type*} {G H K G₁ G₂ : Graph α β} {a b s t u v w x y z : α} {e f : β}
  {W : List β} {X : Set α} {F : Set β}

namespace Graph

 

theorem mem_deleteVerts_singleton : y ∈ V(G.deleteVerts {x}) ↔ y ∈ V(G) ∧ y ≠ x := by
  simp

theorem mem_deleteVerts_singleton_of_ne (hy : y ∈ V(G)) (hyx : y ≠ x) :
    y ∈ V(G.deleteVerts {x}) :=
  mem_deleteVerts_singleton.2 ⟨hy, hyx⟩

 

theorem deleteVerts_singleton_eq_self (hx : x ∉ V(G)) : G.deleteVerts {x} = G := by
  rw [deleteVerts, sdiff_singleton_eq_self hx, induce_vertexSet]

 
theorem deleteVerts_mono (h : G ≤ H) (X : Set α) : G.deleteVerts X ≤ H.deleteVerts X where
  vertexSet_mono := by
    simp only [vertexSet_deleteVerts]
    exact sdiff_subset_sdiff_left h.vertexSet_mono
  isLink_mono e x y hl := by
    rw [deleteVerts_isLink] at hl ⊢
    exact ⟨h.isLink_mono hl.1, hl.2.1, hl.2.2⟩

 

 

theorem IsWalk.deleteVerts_singleton (h : G.IsWalk u W v) (hx : x ∉ G.walkVertices u W) :
    (G.deleteVerts {x}).IsWalk u W v := by
  have hux : u ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_self)
  refine h.anti deleteVerts_le (mem_deleteVerts_singleton_of_ne h.left_mem hux) fun g hg ↦ ?_
  obtain ⟨c, d, hcd⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
  have hc : c ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_of_mem_covered ⟨g, hg, hcd.inc_left⟩)
  have hd : d ≠ x := fun hh ↦ hx (hh ▸ mem_walkVertices_of_mem_covered ⟨g, hg, hcd.inc_right⟩)
  rw [edgeSet_deleteVerts]
  exact ⟨c, d, hcd, by simpa using hc, by simpa using hd⟩

 
theorem IsWalk.notMem_of_inc_of_deleteVerts (h : (G.deleteVerts {x}).IsWalk u W v)
    (hx : G.Inc e x) : e ∉ W := by
  intro he
  have hmem := h.edge_mem he
  rw [edgeSet_deleteVerts] at hmem
  obtain ⟨c, d, hcd, hc, hd⟩ := hmem
  obtain ⟨y, hy⟩ := hx
  rcases hy.left_eq_or_eq hcd with rfl | rfl
  exacts [hc rfl, hd rfl]

 

theorem Reaches.deleteEdges_of_deleteVerts (h : (G.deleteVerts {x}).Reaches u v)
    (hx : G.Inc e x) : (G.deleteEdges {e}).Reaches u v := by
  obtain ⟨P, hP⟩ := h
  have he : e ∉ P := hP.notMem_of_inc_of_deleteVerts hx
  exact ⟨P, (hP.mono deleteVerts_le).deleteEdges fun g hg hgF ↦ he (mem_singleton_iff.1 hgF ▸ hg)⟩

 
theorem Connected.deleteVerts_singleton_of_notMem (h : G.Connected) (hx : x ∉ V(G)) :
    (G.deleteVerts {x}).Connected := by
  rwa [deleteVerts_singleton_eq_self hx]

 

 
def IsCutVertex (G : Graph α β) (x : α) : Prop :=
  x ∈ V(G) ∧ ¬ (G.deleteVerts {x}).Connected

 

 

def HasThreeVertices (G : Graph α β) : Prop :=
  ∃ a ∈ V(G), ∃ b ∈ V(G), ∃ c ∈ V(G), a ≠ b ∧ a ≠ c ∧ b ≠ c

 

theorem hasThreeVertices_iff_ncard (hV : V(G).Finite) : G.HasThreeVertices ↔ 3 ≤ V(G).ncard :=
  (Set.two_lt_ncard hV).symm

theorem HasThreeVertices.mono (h : G.HasThreeVertices) (hV : V(G) ⊆ V(H)) :
    H.HasThreeVertices := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  exact ⟨p, hV hp, q, hV hq, r, hV hr, hpq, hpr, hqr⟩

 


theorem HasThreeVertices.exists_ne_ne (h : G.HasThreeVertices) (u v : α) :
    ∃ w ∈ V(G), w ≠ u ∧ w ≠ v := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := h
  by_contra hcon
  push Not at hcon
  
  have key : ∀ z ∈ V(G), z = u ∨ z = v := fun z hz ↦ (em (z = u)).imp id (hcon z hz)
  rcases key p hp with rfl | rfl <;> rcases key q hq with rfl | rfl <;>
    rcases key r hr with rfl | rfl <;> simp_all

 

 

structure IsTwoConnected (G : Graph α β) : Prop where
   
  hasThreeVertices : G.HasThreeVertices
   
  connected : G.Connected
   
  deleteVerts_connected : ∀ ⦃x⦄, x ∈ V(G) → (G.deleteVerts {x}).Connected

 

theorem IsTwoConnected.deleteVerts_connected' (h : G.IsTwoConnected) (x : α) :
    (G.deleteVerts {x}).Connected := by
  by_cases hx : x ∈ V(G)
  · exact h.deleteVerts_connected hx
  · exact h.connected.deleteVerts_singleton_of_notMem hx

 
theorem IsTwoConnected.no_cut_vertex (h : G.IsTwoConnected) (x : α) : ¬ G.IsCutVertex x :=
  fun hcut ↦ hcut.2 (h.deleteVerts_connected hcut.1)

 




theorem not_isTwoConnected_banana (u v : α) (F : Set β) : ¬ (banana u v F).IsTwoConnected := by
  intro h
  obtain ⟨w, hw, hwu, hwv⟩ := h.hasThreeVertices.exists_ne_ne u v
  
  rcases (hw : w ∈ ({u, v} : Set α)) with rfl | rfl
  exacts [hwu rfl, hwv rfl]

 







theorem IsTwoConnected.no_bridge (h : G.IsTwoConnected) (hl : G.IsLink e u v) :
    (G.deleteEdges {e}).Reaches u v := by
  rcases eq_or_ne u v with rfl | huv
  · exact Reaches.refl (by simpa using hl.left_mem)
  obtain ⟨w, hw, hwu, hwv⟩ := h.hasThreeVertices.exists_ne_ne u v
  have h₁ : (G.deleteVerts {v}).Reaches u w :=
    (h.deleteVerts_connected' v).reaches (mem_deleteVerts_singleton_of_ne hl.left_mem huv)
      (mem_deleteVerts_singleton_of_ne hw hwv)
  have h₂ : (G.deleteVerts {u}).Reaches w v :=
    (h.deleteVerts_connected' u).reaches (mem_deleteVerts_singleton_of_ne hw hwu)
      (mem_deleteVerts_singleton_of_ne hl.right_mem (Ne.symm huv))
  exact (h₁.deleteEdges_of_deleteVerts hl.inc_right).trans
    (h₂.deleteEdges_of_deleteVerts hl.inc_left)

 

 



protected def union (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  IsLink e x y := G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y)
  isLink_symm e _ :=
    { symm := by
        rintro x y (hxy | ⟨he, hxy⟩)
        exacts [Or.inl hxy.symm, Or.inr ⟨he, hxy.symm⟩] }
  eq_or_eq_of_isLink_of_isLink := by
    rintro g x y c d (hxy | ⟨hg, hxy⟩) (hcd | ⟨hg', hcd⟩)
    · exact hxy.left_eq_or_eq hcd
    · exact absurd hxy.edge_mem hg'
    · exact absurd hcd.edge_mem hg
    · exact hxy.left_eq_or_eq hcd
  edge_mem_iff_exists_isLink g := by
    constructor
    · rintro (hg | hg)
      · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
        exact ⟨x, y, Or.inl hxy⟩
      · by_cases hgG : g ∈ E(G)
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hgG
          exact ⟨x, y, Or.inl hxy⟩
        · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hg
          exact ⟨x, y, Or.inr ⟨hgG, hxy⟩⟩
    · rintro ⟨x, y, (hxy | ⟨-, hxy⟩)⟩
      exacts [Or.inl hxy.edge_mem, Or.inr hxy.edge_mem]
  left_mem_of_isLink := by
    rintro g x y (hxy | ⟨-, hxy⟩)
    exacts [Or.inl hxy.left_mem, Or.inr hxy.left_mem]

@[simp]
theorem vertexSet_union (G H : Graph α β) : V(G.union H) = V(G) ∪ V(H) := rfl

@[simp]
theorem edgeSet_union (G H : Graph α β) : E(G.union H) = E(G) ∪ E(H) := rfl

theorem union_isLink :
    (G.union H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y) := Iff.rfl

theorem left_le_union (G H : Graph α β) : G ≤ G.union H where
  vertexSet_mono := subset_union_left
  isLink_mono _ _ _ h := Or.inl h

 
theorem union_le (hGK : G ≤ K) (hHK : H ≤ K) : G.union H ≤ K where
  vertexSet_mono := Set.union_subset hGK.vertexSet_mono hHK.vertexSet_mono
  isLink_mono := by
    rintro g p q (h | ⟨-, h⟩)
    exacts [hGK.isLink_mono h, hHK.isLink_mono h]

 

theorem Compatible.right_le_union (h : G.Compatible H) : H ≤ G.union H where
  vertexSet_mono := subset_union_right
  isLink_mono e x y hxy := by
    by_cases hg : e ∈ E(G)
    · exact Or.inl ((h.isLink_congr hg hxy.edge_mem).2 hxy)
    · exact Or.inr ⟨hg, hxy⟩

 
theorem Compatible.union_isLink (h : G.Compatible H) :
    (G.union H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  refine ⟨fun hxy ↦ hxy.imp id (·.2), fun hxy ↦ ?_⟩
  rcases hxy with hxy | hxy
  · exact Or.inl hxy
  · exact h.right_le_union.isLink_mono hxy

 


theorem Connected.of_two_subgraphs (h₁ : G₁ ≤ K) (h₂ : G₂ ≤ K) (hV : V(K) ⊆ V(G₁) ∪ V(G₂))
    (hc₁ : G₁.Connected) (hc₂ : G₂.Connected) (hs₁ : s ∈ V(G₁)) (hs₂ : s ∈ V(G₂)) :
    K.Connected := by
  refine Connected.of_hub (h₁.vertexSet_mono hs₁) fun z hz ↦ ?_
  rcases hV hz with hz' | hz'
  · exact (hc₁.reaches hs₁ hz').mono h₁
  · exact (hc₂.reaches hs₂ hz').mono h₂

theorem Compatible.union_connected (h : G.Compatible H) (hG : G.Connected) (hH : H.Connected)
    (hs : s ∈ V(G)) (hs' : s ∈ V(H)) : (G.union H).Connected :=
  Connected.of_two_subgraphs (left_le_union G H) h.right_le_union subset_rfl hG hH hs hs'

 







theorem IsTwoConnected.union (hcompat : G.Compatible H) (hG : G.IsTwoConnected)
    (hH : H.IsTwoConnected) (hab : a ≠ b) (haG : a ∈ V(G)) (haH : a ∈ V(H)) (hbG : b ∈ V(G))
    (hbH : b ∈ V(H)) : (G.union H).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G H).vertexSet_mono
  connected := hcompat.union_connected hG.connected hH.connected haG haH
  deleteVerts_connected := by
    intro x _
    
    obtain ⟨c, hcG, hcH, hcx⟩ : ∃ c, c ∈ V(G) ∧ c ∈ V(H) ∧ c ≠ x := by
      by_cases ha : a = x
      · exact ⟨b, hbG, hbH, by rintro rfl; exact hab ha⟩
      · exact ⟨a, haG, haH, ha⟩
    refine Connected.of_two_subgraphs (G₁ := G.deleteVerts {x}) (G₂ := H.deleteVerts {x})
      (deleteVerts_mono (left_le_union G H) _) (deleteVerts_mono hcompat.right_le_union _)
      ?_ (hG.deleteVerts_connected' x) (hH.deleteVerts_connected' x)
      (mem_deleteVerts_singleton_of_ne hcG hcx) (mem_deleteVerts_singleton_of_ne hcH hcx)
    simp [union_sdiff_distrib]

end Graph
