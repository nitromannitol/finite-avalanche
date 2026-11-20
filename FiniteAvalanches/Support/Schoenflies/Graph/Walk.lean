/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/Walk.lean.
Modified for this project: comments removed and replaced by a one-line module docstring.
-/
import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Data.List.Basic

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 








































































open Set

variable {α β : Type*} {G H : Graph α β} {u v w x y z : α} {e f : β} {W W₁ W₂ P : List β}

namespace Graph

 

 
def coveredVertices (G : Graph α β) (W : List β) : Set α := {x | ∃ e ∈ W, G.Inc e x}

 


def walkVertices (G : Graph α β) (u : α) (W : List β) : Set α := insert u (G.coveredVertices W)

theorem mem_coveredVertices_iff : x ∈ G.coveredVertices W ↔ ∃ e ∈ W, G.Inc e x := Iff.rfl

theorem mem_walkVertices_iff : x ∈ G.walkVertices u W ↔ x = u ∨ x ∈ G.coveredVertices W :=
  Set.mem_insert_iff

@[simp]
theorem coveredVertices_nil : G.coveredVertices ([] : List β) = ∅ := by
  simp [coveredVertices]

@[simp]
theorem walkVertices_nil : G.walkVertices u ([] : List β) = {u} := by
  simp [walkVertices]

theorem mem_coveredVertices (he : e ∈ W) (hx : G.Inc e x) : x ∈ G.coveredVertices W :=
  ⟨e, he, hx⟩

theorem mem_walkVertices_self : u ∈ G.walkVertices u W := Set.mem_insert _ _

theorem mem_walkVertices_of_mem_covered (hx : x ∈ G.coveredVertices W) :
    x ∈ G.walkVertices u W :=
  Set.mem_insert_of_mem _ hx

theorem coveredVertices_mono (h : W₁ ⊆ W₂) : G.coveredVertices W₁ ⊆ G.coveredVertices W₂ :=
  fun _ ⟨e, he, hx⟩ ↦ ⟨e, h he, hx⟩

theorem walkVertices_mono (h : W₁ ⊆ W₂) : G.walkVertices u W₁ ⊆ G.walkVertices u W₂ :=
  Set.insert_subset_insert (coveredVertices_mono h)

@[simp]
theorem coveredVertices_reverse : G.coveredVertices W.reverse = G.coveredVertices W := by
  simp [coveredVertices]

@[simp]
theorem walkVertices_reverse : G.walkVertices u W.reverse = G.walkVertices u W := by
  simp [walkVertices]

theorem coveredVertices_append :
    G.coveredVertices (W₁ ++ W₂) = G.coveredVertices W₁ ∪ G.coveredVertices W₂ := by
  ext x
  simp only [mem_coveredVertices_iff, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    exacts [Or.inl ⟨e, he, hx⟩, Or.inr ⟨e, he, hx⟩]
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    exacts [⟨e, Or.inl he, hx⟩, ⟨e, Or.inr he, hx⟩]

 
theorem coveredVertices_subset_vertexSet : G.coveredVertices W ⊆ V(G) :=
  fun _ ⟨_, _, hx⟩ ↦ hx.vertex_mem

theorem walkVertices_subset_vertexSet (hu : u ∈ V(G)) : G.walkVertices u W ⊆ V(G) :=
  Set.insert_subset hu coveredVertices_subset_vertexSet

 


theorem mem_walkVertices_cons (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices u (e :: W)) :
    x = u ∨ x ∈ G.walkVertices w W := by
  rcases mem_walkVertices_iff.1 hx with rfl | ⟨f, hf, hxf⟩
  · exact Or.inl rfl
  rcases List.mem_cons.1 hf with rfl | hf
  · rcases hxf.eq_or_eq_of_isLink hl with rfl | rfl
    exacts [Or.inl rfl, Or.inr mem_walkVertices_self]
  · exact Or.inr (mem_walkVertices_of_mem_covered ⟨f, hf, hxf⟩)

 
theorem mem_walkVertices_cons_of_mem (hl : G.IsLink e u w) (hx : x ∈ G.walkVertices w W) :
    x ∈ G.walkVertices u (e :: W) := by
  rcases mem_walkVertices_iff.1 hx with rfl | hx
  · exact mem_walkVertices_of_mem_covered ⟨e, List.mem_cons_self, hl.inc_right⟩
  · exact mem_walkVertices_of_mem_covered (coveredVertices_mono (List.subset_cons_self _ _) hx)

 

 


inductive IsWalk (G : Graph α β) : α → List β → α → Prop
   
  | nil {x : α} (hx : x ∈ V(G)) : G.IsWalk x [] x
   
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsWalk w W v) :
      G.IsWalk u (e :: W) v

theorem IsWalk.single (hl : G.IsLink e u v) : G.IsWalk u [e] v :=
  .cons hl (.nil hl.right_mem)

theorem IsWalk.left_mem (h : G.IsWalk u W v) : u ∈ V(G) := by
  cases h with
  | nil hx => exact hx
  | cons hl _ => exact hl.left_mem

theorem IsWalk.right_mem (h : G.IsWalk u W v) : v ∈ V(G) := by
  induction h with
  | nil hx => exact hx
  | cons _ _ ih => exact ih

 
theorem IsWalk.edge_mem (h : G.IsWalk u W v) (he : e ∈ W) : e ∈ E(G) := by
  induction h with
  | nil => simp at he
  | cons hl _ ih =>
    rcases List.mem_cons.1 he with rfl | he
    exacts [hl.edge_mem, ih he]

theorem IsWalk.edgeSet_subset (h : G.IsWalk u W v) : ∀ e ∈ W, e ∈ E(G) := fun _ he ↦ h.edge_mem he

theorem IsWalk.target_mem_walkVertices (h : G.IsWalk u W v) : v ∈ G.walkVertices u W := by
  induction h with
  | nil => exact mem_walkVertices_self
  | cons hl _ ih => exact mem_walkVertices_cons_of_mem hl ih

 

theorem IsWalk.walkVertices_subset (h : G.IsWalk u W v) : G.walkVertices u W ⊆ V(G) :=
  walkVertices_subset_vertexSet h.left_mem

@[simp]
theorem isWalk_nil_iff : G.IsWalk u [] v ↔ u = v ∧ u ∈ V(G) := by
  constructor
  · rintro ⟨hx⟩; exact ⟨rfl, hx⟩
  · rintro ⟨rfl, hx⟩; exact .nil hx

theorem IsWalk.eq_of_nil (h : G.IsWalk u [] v) : u = v := (isWalk_nil_iff.1 h).1

 



theorem IsWalk.target_unique (h : G.IsWalk u W v) (h' : G.IsWalk u W w) : v = w := by
  induction h generalizing w with
  | nil hx => exact h'.eq_of_nil.symm ▸ rfl
  | @cons u w' v e W hl _ ih =>
    cases h' with
    | cons hl' hW' => exact ih (hl.right_unique hl' ▸ hW')

 
theorem IsWalk.append (h₁ : G.IsWalk u W₁ w) (h₂ : G.IsWalk w W₂ v) :
    G.IsWalk u (W₁ ++ W₂) v := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hl _ ih => exact .cons hl (ih h₂)

 
theorem IsWalk.reverse (h : G.IsWalk u W v) : G.IsWalk v W.reverse u := by
  induction h with
  | nil hx => simpa using IsWalk.nil hx
  | @cons u w v e W hl _ ih =>
    rw [List.reverse_cons]
    exact ih.append (IsWalk.single hl.symm)

 
theorem IsWalk.mono (hHG : H ≤ G) (h : H.IsWalk u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | cons hl _ ih => exact .cons (hl.mono hHG) ih

 


theorem IsWalk.anti (hHG : H ≤ G) (h : G.IsWalk u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsWalk u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl _ ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))

 

theorem IsWalk.crossing {S : Set α} (h : G.IsWalk u W v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e ∈ W, ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∉ S := by
  induction h with
  | nil => exact absurd hu hv
  | @cons u w v e W hl _ ih =>
    by_cases hw : w ∈ S
    · obtain ⟨f, hf, x, y, hxy, hx, hy⟩ := ih hw hv
      exact ⟨f, List.mem_cons_of_mem _ hf, x, y, hxy, hx, hy⟩
    · exact ⟨e, List.mem_cons_self, u, w, hl, hu, hw⟩

 

 


inductive IsPath (G : Graph α β) : α → List β → α → Prop
   
  | nil {x : α} (hx : x ∈ V(G)) : G.IsPath x [] x
   
  | cons {u w v : α} {e : β} {W : List β} (hl : G.IsLink e u w) (hW : G.IsPath w W v)
      (hfresh : u ∉ G.walkVertices w W) : G.IsPath u (e :: W) v

theorem IsPath.isWalk (h : G.IsPath u W v) : G.IsWalk u W v := by
  induction h with
  | nil hx => exact .nil hx
  | cons hl _ _ ih => exact .cons hl ih

theorem IsPath.left_mem (h : G.IsPath u W v) : u ∈ V(G) := h.isWalk.left_mem

theorem IsPath.right_mem (h : G.IsPath u W v) : v ∈ V(G) := h.isWalk.right_mem

theorem IsPath.edge_mem (h : G.IsPath u W v) (he : e ∈ W) : e ∈ E(G) := h.isWalk.edge_mem he

 
theorem IsPath.single (hl : G.IsLink e u v) (huv : u ≠ v) : G.IsPath u [e] v :=
  .cons hl (.nil hl.right_mem) (by simpa using huv)

 

theorem IsPath.cons_ne (hW : G.IsPath w W v) (hfresh : u ∉ G.walkVertices w W) : u ≠ w := by
  rintro rfl
  exact hfresh mem_walkVertices_self

 


theorem IsPath.not_isLoopAt (h : G.IsPath u W v) (he : e ∈ W) (x : α) : ¬ G.IsLoopAt e x := by
  induction h with
  | nil => simp at he
  | @cons u w v f W hl hW hfresh ih =>
    rcases List.mem_cons.1 he with rfl | he
    · intro hloop
      
      rcases hl.eq_and_eq_or_eq_and_eq hloop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact IsPath.cons_ne hW hfresh rfl
    · exact ih he

 

theorem IsPath.nodup (h : G.IsPath u W v) : W.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons u w v e W hl hW hfresh ih =>
    refine List.nodup_cons.2 ⟨fun he ↦ hfresh ?_, ih⟩
    exact mem_walkVertices_of_mem_covered ⟨e, he, hl.inc_left⟩

 

theorem IsPath.mono (hHG : H ≤ G) (h : H.IsPath u W v) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil (hHG.vertexSet_mono hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.mono hHG) ih fun hmem ↦ hfresh ?_
    
    rcases mem_walkVertices_iff.1 hmem with rfl | ⟨f, hf, hinc⟩
    · exact mem_walkVertices_self
    · obtain ⟨y, hy⟩ := hinc
      exact mem_walkVertices_of_mem_covered
        ⟨f, hf, ((hHG.isLink_iff (hW.isWalk.edge_mem hf)).2 hy).inc_left⟩

theorem IsPath.target_mem_walkVertices (h : G.IsPath u W v) : v ∈ G.walkVertices u W :=
  h.isWalk.target_mem_walkVertices

 

theorem IsPath.extend_at_target (h : G.IsPath u P w) (hl : G.IsLink e w v)
    (hv : v ∉ G.walkVertices u P) : G.IsPath u (P ++ [e]) v := by
  induction h with
  | nil hx =>
    rw [walkVertices_nil] at hv
    exact List.nil_append _ ▸ IsPath.single hl (Ne.symm hv)
  | @cons u w₀ w f P₀ hl₀ hP₀ hfresh ih =>
    have hv₀ : v ∉ G.walkVertices w₀ P₀ := fun hmem ↦ hv (mem_walkVertices_cons_of_mem hl₀ hmem)
    refine List.cons_append .. ▸ .cons hl₀ (ih hl hv₀) fun hmem ↦ ?_
    
    
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | ⟨f', hf', hinc⟩
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · obtain rfl : f' = e := by simpa using hf'
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      · exact hfresh hP₀.target_mem_walkVertices
      · exact hv mem_walkVertices_self

 
theorem IsPath.reverse (h : G.IsPath u W v) : G.IsPath v W.reverse u := by
  induction h with
  | nil hx => simpa using IsPath.nil hx
  | @cons u w v e W hl hW hfresh ih =>
    rw [List.reverse_cons]
    refine ih.extend_at_target hl.symm fun hmem ↦ hfresh ?_
    
    rw [walkVertices_reverse] at hmem
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hW.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered hcov

 



theorem IsPath.from_visited (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ T, G.IsPath x T v ∧ T ⊆ W := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], .nil hx', List.nil_subset _⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨e :: W, .cons hl hW hfresh, List.Subset.refl _⟩
    · obtain ⟨T, hT, hTW⟩ := ih hx'
      exact ⟨T, hT, List.Subset.trans hTW (List.subset_cons_self _ _)⟩

 



theorem IsPath.split (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      (x = u ∨ u ∉ G.walkVertices x W₂) := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', Or.inl rfl⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh, Or.inl rfl⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, -⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem ↦ hfresh (walkVertices_mono hsub₁ hmem),
      h₂, Or.inr fun hmem ↦ hfresh ?_⟩
    
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hx'
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov)

 



theorem IsWalk.contains_path (h : G.IsWalk u W v) : ∃ P, G.IsPath u P v ∧ P ⊆ W := by
  induction h with
  | nil hx => exact ⟨[], .nil hx, List.Subset.refl _⟩
  | @cons u w v e W hl hW ih =>
    obtain ⟨P, hP, hPW⟩ := ih
    by_cases hu : u ∈ G.walkVertices w P
    · 
      obtain ⟨T, hT, hTP⟩ := hP.from_visited hu
      exact ⟨T, hT, List.Subset.trans (List.Subset.trans hTP hPW) (List.subset_cons_self _ _)⟩
    · exact ⟨e :: P, .cons hl hP hu, List.cons_subset_cons _ hPW⟩

 

 


def Reaches (G : Graph α β) (u v : α) : Prop := ∃ W, G.IsWalk u W v

theorem Reaches.left_mem (h : G.Reaches u v) : u ∈ V(G) := h.choose_spec.left_mem

theorem Reaches.right_mem (h : G.Reaches u v) : v ∈ V(G) := h.choose_spec.right_mem

@[refl]
theorem Reaches.refl (hu : u ∈ V(G)) : G.Reaches u u := ⟨[], .nil hu⟩

theorem Reaches.symm (h : G.Reaches u v) : G.Reaches v u :=
  let ⟨W, hW⟩ := h; ⟨W.reverse, hW.reverse⟩

theorem Reaches.trans (h₁ : G.Reaches u v) (h₂ : G.Reaches v w) : G.Reaches u w :=
  let ⟨W₁, hW₁⟩ := h₁; let ⟨W₂, hW₂⟩ := h₂; ⟨W₁ ++ W₂, hW₁.append hW₂⟩

theorem reaches_comm : G.Reaches u v ↔ G.Reaches v u := ⟨Reaches.symm, Reaches.symm⟩

theorem Reaches.of_isLink (hl : G.IsLink e u v) : G.Reaches u v := ⟨[e], .single hl⟩

theorem Reaches.of_adj (h : G.Adj u v) : G.Reaches u v :=
  let ⟨_, hl⟩ := h; .of_isLink hl

 
theorem Reaches.exists_isPath (h : G.Reaches u v) : ∃ P, G.IsPath u P v :=
  let ⟨_, hW⟩ := h; let ⟨P, hP, _⟩ := hW.contains_path; ⟨P, hP⟩

theorem Reaches.mono (hHG : H ≤ G) (h : H.Reaches u v) : G.Reaches u v :=
  let ⟨W, hW⟩ := h; ⟨W, hW.mono hHG⟩

 

 


def Connected (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ ∀ ⦃u⦄, u ∈ V(G) → ∀ ⦃v⦄, v ∈ V(G) → G.Reaches u v

theorem Connected.nonempty (h : G.Connected) : V(G).Nonempty := h.1

theorem Connected.reaches (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) : G.Reaches u v :=
  h.2 hu hv

 

theorem Connected.of_hub (hu : u ∈ V(G)) (h : ∀ v ∈ V(G), G.Reaches u v) : G.Connected :=
  ⟨⟨u, hu⟩, fun _ hx _ hy ↦ ((h _ hx).symm).trans (h _ hy)⟩

 

theorem Connected.exists_isPath (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    ∃ P, G.IsPath u P v :=
  (h.reaches hu hv).exists_isPath

 





theorem coveredVertices_mono_of_le (hHG : H ≤ G) : H.coveredVertices W ⊆ G.coveredVertices W :=
  fun _ ⟨f, hf, y, hy⟩ ↦ ⟨f, hf, y, hy.mono hHG⟩

theorem walkVertices_mono_of_le (hHG : H ≤ G) : H.walkVertices u W ⊆ G.walkVertices u W :=
  Set.insert_subset_insert (coveredVertices_mono_of_le hHG)

 


theorem IsPath.anti (hHG : H ≤ G) (h : G.IsPath u W v) (hu : u ∈ V(H))
    (hE : ∀ e ∈ W, e ∈ E(H)) : H.IsPath u W v := by
  induction h with
  | nil => exact .nil hu
  | @cons u w v e W hl hW hfresh ih =>
    have he : e ∈ E(H) := hE e List.mem_cons_self
    have hl' : H.IsLink e u w := (hHG.isLink_iff he).2 hl
    exact .cons hl' (ih hl'.right_mem fun f hf ↦ hE f (List.mem_cons_of_mem _ hf))
      fun hmem ↦ hfresh (walkVertices_mono_of_le hHG hmem)

theorem mem_edgeSet_deleteEdges_iff {F : Set β} {f : β} :
    f ∈ E(G.deleteEdges F) ↔ f ∈ E(G) ∧ f ∉ F := by
  simp

 
theorem IsWalk.deleteEdges {F : Set β} (h : G.IsWalk u W v) (hW : ∀ f ∈ W, f ∉ F) :
    (G.deleteEdges F).IsWalk u W v :=
  h.anti deleteEdges_le (by simpa using h.left_mem)
    fun f hf ↦ mem_edgeSet_deleteEdges_iff.2 ⟨h.edge_mem hf, hW f hf⟩

end Graph
