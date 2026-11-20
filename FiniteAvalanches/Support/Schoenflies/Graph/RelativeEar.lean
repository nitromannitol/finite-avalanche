/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/RelativeEar.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Graph.Component
import FiniteAvalanches.Support.Schoenflies.Graph.Ear
import FiniteAvalanches.Support.Schoenflies.Graph.Tree

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 



















































































open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G K B : Graph α β} {a b x y : α} {e f : β} {D : List β}

 




 


theorem mem_vertexSet_of_inc_of_mem_edgeSet (hKG : K ≤ G) (hf : f ∈ E(K)) (h : G.Inc f y) :
    y ∈ V(K) :=
  ((hKG.inc_congr hf).2 h).vertex_mem

 

theorem eq_of_le_of_subset_subset (hKG : K ≤ G) (hV : V(G) ⊆ V(K)) (hE : E(G) ⊆ E(K)) :
    K = G :=
  le_antisymm hKG ((Compatible.of_ge hKG).le_iff.2 ⟨hV, hE⟩)

 

 











theorem IsTwoConnected.relative_ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ D ≠ [] ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧ (∀ g ∈ D, g ∉ E(K)) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨x, hxG, hxK⟩ := hout
    
    obtain ⟨p, hp, q, hq, -, -, hpq, -, -⟩ := hK.hasThreeVertices
    obtain ⟨a, ha, b, hb, D, hab, hpath, hint, -, hedge⟩ :=
      hG.exists_path_through_component hKG.vertexSet_mono hp hq hpq hxG hxK
    refine ⟨a, b, D, hpath, hab, ha, hb, hpath.ne_nil hab, hint, fun f hf hfK ↦ ?_⟩
    
    obtain ⟨y, hy, hyK⟩ := hedge f hf
    exact hyK (mem_vertexSet_of_inc_of_mem_edgeSet hKG hfK hy)
  · 
    push Not at hout
    obtain ⟨f, hfG, hfK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hfG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    refine ⟨p, q, [f], .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      by simp, fun y hy hyp hyq ↦ ?_, fun g hg ↦ ?_⟩
    · 
      rw [walkVertices_cons hpq, walkVertices_nil] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      exacts [absurd rfl hyp, absurd rfl hyq]
    · obtain rfl : g = f := by simpa using hg
      exact hfK

 






theorem IsTwoConnected.relative_grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(K)) ∧
      (K.union (G.pathGraphOf a D)).IsTwoConnected ∧
      K ≤ K.union (G.pathGraphOf a D) ∧ K.union (G.pathGraphOf a D) ≤ G ∧
      ∃ g ∈ E(K.union (G.pathGraphOf a D)), g ∉ E(K) := by
  obtain ⟨a, b, D, hpath, hab, ha, hb, hDne, hint, hnew⟩ :=
    hG.relative_ear_exists hK hKG hnl hproper
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  obtain ⟨g, hgD⟩ : ∃ g, g ∈ D := by
    cases D with
    | nil => exact absurd rfl hDne
    | cons g t => exact ⟨g, List.mem_cons_self⟩
  exact ⟨a, b, D, hpath, hab, ha, hb, hint,
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab ha hb,
    left_le_union _ _, union_le hKG hearle,
    g, Set.mem_union_right _ (hearP.mem_edgeSet hgD), hnew g hgD⟩

 






@[simp]
theorem vertexSet_union_pathGraphOf (B G : Graph α β) (a : α) (D : List β) :
    V(B.union (G.pathGraphOf a D)) = V(B) ∪ G.walkVertices a D := rfl

theorem edgeSet_union_pathGraphOf (h : G.IsWalk a D b) :
    E(B.union (G.pathGraphOf a D)) = E(B) ∪ {e | e ∈ D} := by
  rw [edgeSet_union, pathGraphOf_edgeSet h]

 

 










theorem IsTwoConnected.ear_decomposition {motive : Graph α β → Prop} [G.Finite]
    (hG : G.IsTwoConnected) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hK : K.IsTwoConnected) (hKG : K ≤ G) (base : motive K)
    (step : ∀ (B : Graph α β) (a b : α) (D : List β), B.IsTwoConnected → K ≤ B → B ≤ G →
      motive B → G.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ G.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      motive (B.union (G.pathGraphOf a D))) :
    motive G := by
  
  have hstep : ∀ B : Graph α β, B ≠ G → B.IsTwoConnected → K ≤ B → B ≤ G → motive B →
      ∃ B' : Graph α β, B'.IsTwoConnected ∧ K ≤ B' ∧ B' ≤ G ∧ motive B' ∧
        (E(G) \ E(B')).ncard < (E(G) \ E(B)).ncard := by
    intro B hBne hB hKB hBG hmot
    
    have hproper : (∃ x ∈ V(G), x ∉ V(B)) ∨ (∃ g ∈ E(G), g ∉ E(B)) := by
      by_contra hcon
      push Not at hcon
      exact hBne (eq_of_le_of_subset_subset hBG (fun x hx ↦ hcon.1 x hx) fun g hg ↦ hcon.2 g hg)
    obtain ⟨a, b, D, hpath, hab, ha, hb, hint, hB'two, hBB', hB'G, g, hgB', hgB⟩ :=
      hG.relative_grows_by_ear hB hBG hnl hproper
    refine ⟨_, hB'two, hKB.trans hBB', hB'G,
      step B a b D hB hKB hBG hmot hpath hab ha hb hint, ?_⟩
    
    refine Set.ncard_lt_ncard ⟨fun f hf ↦ ⟨hf.1, fun hfB ↦ hf.2 (hBB'.edgeSet_mono hfB)⟩, ?_⟩
      ((finite_edgeSet G).subset sdiff_subset)
    exact fun hcon ↦ (hcon ⟨hB'G.edgeSet_mono hgB', hgB⟩).2 hgB'
  
  have key : ∀ n, ∀ B : Graph α β, (E(G) \ E(B)).ncard ≤ n → B.IsTwoConnected → K ≤ B →
      B ≤ G → motive B → motive G := by
    intro n
    induction n with
    | zero =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · 
        obtain ⟨B', -, -, -, -, hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact absurd (Nat.lt_of_lt_of_le hlt hcard) (Nat.not_lt_zero _)
    | succ n ih =>
      intro B hcard hB hKB hBG hmot
      by_cases hBne : B = G
      · exact hBne ▸ hmot
      · obtain ⟨B', hB', hKB', hB'G, hmot', hlt⟩ := hstep B hBne hB hKB hBG hmot
        exact ih B' (by omega) hB' hKB' hB'G hmot'
  exact key _ K le_rfl hK le_rfl hKG base

end Graph
