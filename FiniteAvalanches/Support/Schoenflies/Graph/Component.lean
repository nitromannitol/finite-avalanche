/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/Component.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Graph.Walk
import FiniteAvalanches.Support.Schoenflies.Graph.TwoConnected

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 






































































open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {u v w x y z a b c d p q : α} {e f : β}
  {W W' P Q : List β} {S : Set α}

 

 





def component (G : Graph α β) (u : α) : Set α := {v | G.Reaches u v}

theorem mem_component_iff : v ∈ G.component u ↔ G.Reaches u v := Iff.rfl

theorem component_subset_vertexSet : G.component u ⊆ V(G) := fun _ h ↦ Reaches.right_mem h

theorem mem_component_self (hu : u ∈ V(G)) : u ∈ G.component u := Reaches.refl hu

theorem component_nonempty (hu : u ∈ V(G)) : (G.component u).Nonempty :=
  ⟨u, mem_component_self hu⟩

 
theorem component_eq_empty (hu : u ∉ V(G)) : G.component u = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h ↦ hu (Reaches.left_mem h)

 

theorem mem_component_of_reaches (hv : v ∈ G.component u) (h : G.Reaches v w) :
    w ∈ G.component u :=
  Reaches.trans hv h

 
theorem mem_component_of_isLink (hx : x ∈ G.component u) (hl : G.IsLink e x y) :
    y ∈ G.component u :=
  mem_component_of_reaches hx (Reaches.of_isLink hl)

theorem mem_component_comm : v ∈ G.component u ↔ u ∈ G.component v := reaches_comm

 
theorem component_eq_of_mem (hv : v ∈ G.component u) : G.component v = G.component u :=
  Set.ext fun _ ↦ ⟨fun h ↦ Reaches.trans hv h, fun h ↦ Reaches.trans (Reaches.symm hv) h⟩

 
theorem component_eq_or_disjoint (u v : α) :
    G.component u = G.component v ∨ Disjoint (G.component u) (G.component v) := by
  rcases em (∃ w, w ∈ G.component u ∧ w ∈ G.component v) with ⟨w, hu, hv⟩ | hne
  · exact Or.inl ((component_eq_of_mem hu).symm.trans (component_eq_of_mem hv))
  · exact Or.inr (Set.disjoint_left.2 fun w hw hw' ↦ hne ⟨w, hw, hw'⟩)

 
theorem iUnion_component (G : Graph α β) : ⋃ u ∈ V(G), G.component u = V(G) :=
  Set.Subset.antisymm (Set.iUnion₂_subset fun _ _ ↦ component_subset_vertexSet)
    fun _ hx ↦ Set.mem_biUnion hx (mem_component_self hx)

 

theorem induce_component_le : G.induce (G.component u) ≤ G :=
  induce_le component_subset_vertexSet

@[simp]
theorem mem_vertexSet_induce_component : v ∈ V(G.induce (G.component u)) ↔ G.Reaches u v :=
  Iff.rfl

 

theorem IsWalk.walkVertices_subset_component (h : G.IsWalk x W y) (hx : x ∈ G.component u) :
    G.walkVertices x W ⊆ G.component u := by
  induction h with
  | nil => simpa using hx
  | @cons x' w y e W hl _ ih =>
    intro z hz
    rcases mem_walkVertices_cons hl hz with rfl | hz'
    · exact hx
    · exact ih (mem_component_of_isLink hx hl) hz'

 

theorem IsWalk.induce_component (h : G.IsWalk x W y) (hx : x ∈ G.component u) :
    (G.induce (G.component u)).IsWalk x W y := by
  refine h.anti induce_component_le hx fun g hg ↦ ?_
  obtain ⟨s, t, hst⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem hg)
  exact ⟨s, t, hst,
    h.walkVertices_subset_component hx (mem_walkVertices_of_mem_covered ⟨g, hg, hst.inc_left⟩),
    h.walkVertices_subset_component hx (mem_walkVertices_of_mem_covered ⟨g, hg, hst.inc_right⟩)⟩

 
theorem induce_component_connected (hu : u ∈ V(G)) : (G.induce (G.component u)).Connected := by
  refine Connected.of_hub (mem_component_self hu) fun z hz ↦ ?_
  obtain ⟨W, hW⟩ := mem_component_iff.1 hz
  exact ⟨W, hW.induce_component (mem_component_self hu)⟩

 

 

theorem exists_minLength_isWalk (h : G.Reaches u v) :
    ∃ W, G.IsWalk u W v ∧ ∀ W', G.IsWalk u W' v → W.length ≤ W'.length := by
  classical
  obtain ⟨W₀, hW₀⟩ := h
  have hex : ∃ n, ∃ W, G.IsWalk u W v ∧ W.length = n := ⟨W₀.length, W₀, hW₀, rfl⟩
  obtain ⟨W, hW, hlen⟩ := Nat.find_spec hex
  exact ⟨W, hW, fun W' hW' ↦ hlen ▸ Nat.find_le ⟨W', hW', rfl⟩⟩

 



theorem IsWalk.isPath_of_minLength (h : G.IsWalk u W v)
    (hmin : ∀ W', G.IsWalk u W' v → W.length ≤ W'.length) : G.IsPath u W v := by
  induction h with
  | nil hx => exact .nil hx
  | @cons u w v e W hl hW ih =>
    
    
    have hmin' : ∀ W', G.IsWalk w W' v → W.length ≤ W'.length := fun W' hW' ↦ by
      have := hmin (e :: W') (.cons hl hW')
      simp only [List.length_cons] at this
      omega
    have hP : G.IsPath w W v := ih hmin'
    refine .cons hl hP fun hmem ↦ ?_
    obtain ⟨T, hT, hTW⟩ := hP.from_visited hmem
    have h₁ : T.length ≤ W.length := (List.subperm_of_subset hT.nodup hTW).length_le
    have h₂ := hmin T hT.isWalk
    simp only [List.length_cons] at h₂
    omega

 

theorem exists_minLength_isPath (h : G.Reaches u v) :
    ∃ P, G.IsPath u P v ∧ ∀ W, G.IsWalk u W v → P.length ≤ W.length :=
  let ⟨W, hW, hmin⟩ := exists_minLength_isWalk h
  ⟨W, hW.isPath_of_minLength hmin, hmin⟩

theorem Connected.exists_minLength_isPath (h : G.Connected) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    ∃ P, G.IsPath u P v ∧ ∀ W, G.IsWalk u W v → P.length ≤ W.length :=
  _root_.Graph.exists_minLength_isPath (h.reaches hu hv)

 





 

theorem IsWalk.walkVertices_subset_of_deleteVerts (h : (G.deleteVerts S).IsWalk u W v) :
    G.walkVertices u W ⊆ V(G) \ S := by
  intro z hz
  rcases mem_walkVertices_iff.1 hz with rfl | ⟨g, hg, hinc⟩
  · simpa using h.left_mem
  
  have hgE := h.edge_mem hg
  rw [edgeSet_deleteVerts] at hgE
  obtain ⟨s, t, hst, hs, ht⟩ := hgE
  rcases hinc.eq_or_eq_of_isLink hst with rfl | rfl
  exacts [⟨hst.left_mem, hs⟩, ⟨hst.right_mem, ht⟩]

 
theorem component_deleteVerts_subset : (G.deleteVerts S).component x ⊆ V(G) \ S := by
  intro z hz
  have := component_subset_vertexSet hz
  rwa [vertexSet_deleteVerts] at this

 

theorem mem_component_deleteVerts_of_isLink (hp : p ∈ (G.deleteVerts S).component x)
    (hl : G.IsLink e p q) (hq : q ∉ S) : q ∈ (G.deleteVerts S).component x :=
  mem_component_of_isLink hp
    ((deleteVerts_isLink G S).2 ⟨hl, (component_deleteVerts_subset hp).2, hq⟩)

 





theorem exists_isLink_out_of_component {K : Graph α β} (hKG : K ≤ G)
    (h : K.IsWalk x W v) (hx : x ∈ (G.deleteVerts S).component x) (hv : v ∈ S) :
    ∃ p ∈ (G.deleteVerts S).component x, ∃ g ∈ W, ∃ t ∈ S, K.IsLink g p t := by
  have hvL : v ∉ (G.deleteVerts S).component x := fun hmem ↦
    (component_deleteVerts_subset hmem).2 hv
  obtain ⟨g, hg, s, t, hst, hs, ht⟩ := h.crossing hx hvL
  refine ⟨s, hs, g, hg, t, ?_, hst⟩
  by_contra htS
  exact ht (mem_component_deleteVerts_of_isLink hs (hst.mono hKG) htS)

 

 






theorem IsTwoConnected.component_two_neighbors (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧
      (∃ p ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g p c) ∧
      (∃ q ∈ (G.deleteVerts S).component x, ∃ g, G.IsLink g q d) := by
  have hxD : x ∈ V(G.deleteVerts S) := by rw [vertexSet_deleteVerts]; exact ⟨hx, hxS⟩
  have hxL : x ∈ (G.deleteVerts S).component x := mem_component_self hxD
  
  obtain ⟨W, hW⟩ := hG.connected.reaches hx (hS ha)
  obtain ⟨p, hp, g, -, c, hc, hgpc⟩ := exists_isLink_out_of_component le_rfl hW hxL ha
  
  obtain ⟨t, ht, htc⟩ : ∃ t ∈ S, t ≠ c := by
    rcases eq_or_ne a c with rfl | hac
    · exact ⟨b, hb, fun h ↦ hab h.symm⟩
    · exact ⟨a, ha, hac⟩
  have hxc : x ∈ V(G.deleteVerts {c}) :=
    mem_deleteVerts_singleton_of_ne hx fun h ↦ hxS (h ▸ hc)
  have htc' : t ∈ V(G.deleteVerts {c}) := mem_deleteVerts_singleton_of_ne (hS ht) htc
  obtain ⟨W', hW'⟩ := (hG.deleteVerts_connected' c).reaches hxc htc'
  obtain ⟨q, hq, g', -, d, hd, hgqd⟩ :=
    exists_isLink_out_of_component deleteVerts_le hW' hxL ht
  
  have hdc : d ≠ c := by
    have := ((deleteVerts_isLink G {c}).1 hgqd).2.2
    simpa using this
  exact ⟨c, hc, d, hd, fun h ↦ hdc h.symm, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd.mono deleteVerts_le⟩⟩

 


theorem mem_walkVertices_append_singleton (hy : y ∈ G.walkVertices u (W ++ [e])) :
    y ∈ G.walkVertices u W ∨ G.Inc e y := by
  rcases mem_walkVertices_iff.1 hy with rfl | hcov
  · exact Or.inl mem_walkVertices_self
  rw [coveredVertices_append] at hcov
  rcases hcov with h | ⟨g, hg, hinc⟩
  · exact Or.inl (mem_walkVertices_of_mem_covered h)
  · obtain rfl : g = e := by simpa using hg
    exact Or.inr hinc

 











theorem IsTwoConnected.exists_path_through_component (hG : G.IsTwoConnected) (hS : S ⊆ V(G))
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hx : x ∈ V(G)) (hxS : x ∉ S) :
    ∃ c ∈ S, ∃ d ∈ S, ∃ P, c ≠ d ∧ G.IsPath c P d ∧
      (∀ y ∈ G.walkVertices c P, y ≠ c → y ≠ d → y ∉ S) ∧
      (∃ y ∈ G.walkVertices c P, y ∉ S) ∧
      ∀ f ∈ P, ∃ y, G.Inc f y ∧ y ∉ S := by
  obtain ⟨c, hc, d, hd, hcd, ⟨p, hp, g, hgpc⟩, ⟨q, hq, g', hgqd⟩⟩ :=
    hG.component_two_neighbors hS ha hb hab hx hxS
  have hpS : p ∉ S := (component_deleteVerts_subset hp).2
  have hqS : q ∉ S := (component_deleteVerts_subset hq).2
  
  obtain ⟨Q, hQ⟩ := Reaches.exists_isPath (Reaches.trans (Reaches.symm hq) hp)
  have hQvert : G.walkVertices q Q ⊆ V(G) \ S :=
    hQ.isWalk.walkVertices_subset_of_deleteVerts
  have hQG : G.IsPath q Q p := hQ.mono deleteVerts_le
  
  have hcQ : c ∉ G.walkVertices q Q := fun hmem ↦ (hQvert hmem).2 hc
  have hQc : G.IsPath q (Q ++ [g]) c := hQG.extend_at_target hgpc hcQ
  
  have hdQc : d ∉ G.walkVertices q (Q ++ [g]) := by
    intro hmem
    rcases mem_walkVertices_append_singleton hmem with hmem' | hinc
    · exact (hQvert hmem').2 hd
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS hd, hcd rfl]
  have hpath : G.IsPath d (g' :: (Q ++ [g])) c := .cons hgqd.symm hQc hdQc
  refine ⟨d, hd, c, hc, _, fun h ↦ hcd h.symm, hpath, fun y hy hyd hyc ↦ ?_,
    ⟨q, mem_walkVertices_cons_of_mem hgqd.symm mem_walkVertices_self, hqS⟩, fun f hf ↦ ?_⟩
  · 
    rcases mem_walkVertices_cons hgqd.symm hy with rfl | hy'
    · exact absurd rfl hyd
    rcases mem_walkVertices_append_singleton hy' with hmem | hinc
    · exact (hQvert hmem).2
    · rcases hinc.eq_or_eq_of_isLink hgpc with rfl | rfl
      exacts [hpS, absurd rfl hyc]
  · 
    
    rcases List.mem_cons.1 hf with rfl | hf'
    · exact ⟨q, hgqd.inc_left, hqS⟩
    rcases List.mem_append.1 hf' with hf' | hf'
    · have hfE := hQ.isWalk.edge_mem hf'
      rw [edgeSet_deleteVerts] at hfE
      obtain ⟨s, t, hst, hs, -⟩ := hfE
      exact ⟨s, hst.inc_left, hs⟩
    · obtain rfl : f = g := by simpa using hf'
      exact ⟨p, hgpc.inc_left, hpS⟩

end Graph
