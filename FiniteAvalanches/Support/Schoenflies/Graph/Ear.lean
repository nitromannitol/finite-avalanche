/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/Ear.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Graph.TwoConnected
import FiniteAvalanches.Support.Schoenflies.Graph.PathGraph

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 

















































































open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G H K P : Graph α β} {a b c s t u v x y z : α} {e f : β}
  {W D : List β}

 






 

 







theorem Reaches.reroute (hV : V(G) ⊆ V(H))
    (hE : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → H.IsLink g p q)
    (hends : ∀ ⦃p q⦄, G.IsLink e p q → H.Reaches p q)
    (h : G.Reaches s t) : H.Reaches s t := by
  obtain ⟨R, hR⟩ := h
  induction hR with
  | nil hx => exact Reaches.refl (hV hx)
  | @cons p w q g R hl _ ih =>
    
    refine Reaches.trans ?_ ih
    by_cases hg : g = e
    · exact hends (hg ▸ hl)
    · exact Reaches.of_isLink (hE hl hg)

 






theorem Reaches.across_edge_replacement (hV : V(G.deleteVerts {c}) ⊆ V(H))
    (hl : G.IsLink e u v)
    (hE : ∀ ⦃g p q⦄, (G.deleteVerts {c}).IsLink g p q → g ≠ e → H.IsLink g p q)
    (routed : H.Reaches u v ∨ G.Inc e c)
    (h : (G.deleteVerts {c}).Reaches s t) : H.Reaches s t := by
  refine Reaches.reroute (e := e) hV hE (fun p q hpq ↦ ?_) h
  rw [deleteVerts_isLink] at hpq
  obtain ⟨hpq, hp, hq⟩ := hpq
  have hpc : p ≠ c := fun hh ↦ hp (by simp [hh])
  have hqc : q ≠ c := fun hh ↦ hq (by simp [hh])
  rcases routed with hr | ⟨w, hw⟩
  · 
    rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [hr, hr.symm]
  · 
    rcases hw.left_eq_or_eq hpq with hh | hh
    exacts [(hpc hh.symm).elim, (hqc hh.symm).elim]

 

 







theorem IsTwoConnected.ear (hG : G.IsTwoConnected) (hcompat : G.Compatible P)
    (hP : P.IsPathGraph u W v) (huv : u ≠ v) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    (G.union P).IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (left_le_union G P).vertexSet_mono
  connected := hcompat.union_connected hG.connected hP.connected hu hP.source_mem
  deleteVerts_connected := by
    intro c _
    
    obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
      by_cases hcu : u = c
      · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
      · exact ⟨u, hu, hcu⟩
    have hGle : G.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono (left_le_union G P) _
    have hPle : P.deleteVerts {c} ≤ (G.union P).deleteVerts {c} :=
      deleteVerts_mono hcompat.right_le_union _
    have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
    
    have key : ∀ x ∈ V(G), x ≠ c → ((G.union P).deleteVerts {c}).Reaches z x := fun x hx hxc ↦
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hzG hzc)
        (mem_deleteVerts_singleton_of_ne hx hxc)).mono hGle
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne
      ((left_le_union G P).vertexSet_mono hzG) hzc) fun x hx ↦ ?_
    rw [vertexSet_deleteVerts] at hx
    obtain ⟨hxS, hxc⟩ := hx
    have hxc' : x ≠ c := by simpa using hxc
    rcases (hxS : x ∈ V(G) ∪ V(P)) with hxG | hxP
    · exact key x hxG hxc'
    · 
      rcases hP.reaches_an_end hxP hxc' with hr | hr
      · have hune : u ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key u hu hune).trans (hr.mono hPle).symm
      · have hvne : v ≠ c := by
          have h₂ := hr.right_mem
          rw [vertexSet_deleteVerts] at h₂
          simpa using h₂.2
        exact (key v hv hvne).trans (hr.mono hPle).symm

 

 











theorem IsTwoConnected.replace_edge_by_path (hG : G.IsTwoConnected) (hl : G.IsLink e u v)
    (huv : u ≠ v) (hcompat : (G.deleteEdges {e}).Compatible P) (hP : P.IsPathGraph u W v)
    (hnew : ∀ x ∈ V(P), x ≠ u → x ≠ v → x ∉ V(G)) :
    ((G.deleteEdges {e}).union P).IsTwoConnected := by
  set T := G.deleteEdges {e} with hT
  set S := T.union P with hS
  have hTS : T ≤ S := left_le_union T P
  have hPS : P ≤ S := hcompat.right_le_union
  have hVT : V(T) = V(G) := by rw [hT]; simp
  have hu : u ∈ V(G) := hl.left_mem
  have hv : v ∈ V(G) := hl.right_mem
  
  have hGS : ∀ ⦃g p q⦄, G.IsLink g p q → g ≠ e → S.IsLink g p q := by
    intro g p q hg hge
    refine hTS.isLink_mono (show T.IsLink g p q from ?_)
    rw [hT]
    exact ⟨hg, by simpa using hge⟩
  have hVGS : V(G) ⊆ V(S) := by
    rw [hS, vertexSet_union, hVT]
    exact Set.subset_union_left
  
  have hPuv : P.Reaches u v := hP.connected.reaches hP.source_mem hP.target_mem
  refine ⟨hG.hasThreeVertices.mono hVGS, ?_, ?_⟩
  · refine Connected.of_hub (hVGS hu) fun x hx ↦ ?_
    rcases (hx : x ∈ V(T) ∪ V(P)) with hxT | hxP
    · refine Reaches.reroute (e := e) hVGS hGS ?_
        (hG.connected.reaches hu (by rwa [hVT] at hxT))
      intro p q hpq
      rcases hl.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [hPuv.mono hPS, (hPuv.mono hPS).symm]
    · exact (hP.connected.reaches hP.source_mem hxP).mono hPS
  intro c _
  
  obtain ⟨z, hzG, hzc⟩ : ∃ z, z ∈ V(G) ∧ z ≠ c := by
    by_cases hcu : u = c
    · exact ⟨v, hv, fun hh ↦ huv (hcu.trans hh.symm)⟩
    · exact ⟨u, hu, hcu⟩
  have hTle : T.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hTS _
  have hPle : P.deleteVerts {c} ≤ S.deleteVerts {c} := deleteVerts_mono hPS _
  have hGc : (G.deleteVerts {c}).Connected := hG.deleteVerts_connected' c
  
  have routed : (S.deleteVerts {c}).Reaches u v ∨ G.Inc e c := by
    by_cases hcu : c = u
    · exact Or.inr (hcu ▸ hl.inc_left)
    by_cases hcv : c = v
    · exact Or.inr (hcv ▸ hl.inc_right)
    by_cases hcG : c ∈ V(G)
    · 
      have hcP : c ∉ V(P) := fun hh ↦ hnew c hh hcu hcv hcG
      have hreach : (P.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcP]; exact hPuv
      exact Or.inl (hreach.mono hPle)
    · 
      have hcT : c ∉ V(T) := by rw [hVT]; exact hcG
      have hreach : (T.deleteVerts {c}).Reaches u v := by
        rw [deleteVerts_singleton_eq_self hcT, hT]
        exact hG.no_bridge hl
      exact Or.inl (hreach.mono hTle)
  
  have key : ∀ x ∈ V(G), x ≠ c → (S.deleteVerts {c}).Reaches x z := by
    intro x hx hxc
    refine Reaches.across_edge_replacement (e := e) ?_ hl ?_ routed
      (hGc.reaches (mem_deleteVerts_singleton_of_ne hx hxc)
        (mem_deleteVerts_singleton_of_ne hzG hzc))
    · rw [vertexSet_deleteVerts, vertexSet_deleteVerts]
      exact Set.sdiff_subset_sdiff_left hVGS
    · intro g p q hg hge
      rw [deleteVerts_isLink] at hg ⊢
      exact ⟨hGS hg.1 hge, hg.2.1, hg.2.2⟩
  refine Connected.of_hub (mem_deleteVerts_singleton_of_ne (hVGS hzG) hzc) fun x hx ↦ ?_
  rw [vertexSet_deleteVerts] at hx
  obtain ⟨hxS, hxc⟩ := hx
  have hxc' : x ≠ c := by simpa using hxc
  rcases (hxS : x ∈ V(T) ∪ V(P)) with hxT | hxP
  · exact (key x (by rwa [hVT] at hxT) hxc').symm
  · rcases hP.reaches_an_end hxP hxc' with hr | hr
    · have hune : u ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key u hu hune).symm.trans (hr.mono hPle).symm
    · have hvne : v ≠ c := by
        have h₂ := hr.right_mem
        rw [vertexSet_deleteVerts] at h₂
        simpa using h₂.2
      exact (key v hv hvne).symm.trans (hr.mono hPle).symm

 

 







theorem IsTwoConnected.ear_exists (hG : G.IsTwoConnected) (hK : K.IsTwoConnected) (hKG : K ≤ G)
    (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ a b D g, G.IsPath a D b ∧ a ≠ b ∧ a ∈ V(K) ∧ b ∈ V(K) ∧ g ∈ D ∧ g ∉ E(K) := by
  by_cases hout : ∃ x ∈ V(G), x ∉ V(K)
  · obtain ⟨o, hoG, hoK⟩ := hout
    
    obtain ⟨anchor, hanchor⟩ := hK.connected.nonempty
    obtain ⟨R, hR⟩ := hG.connected.reaches (hKG.vertexSet_mono hanchor) hoG
    obtain ⟨g, hgR, p, q, hlpq, hpK, hqK⟩ := hR.crossing hanchor hoK
    have hpq : p ≠ q := fun hh ↦ hqK (hh ▸ hpK)
    
    obtain ⟨b, hbK, hbp, -⟩ := hK.hasThreeVertices.exists_ne_ne p p
    have hqG : q ∈ V(G) := hlpq.right_mem
    have hbG : b ∈ V(G) := hKG.vertexSet_mono hbK
    
    obtain ⟨D, hD⟩ := ((hG.deleteVerts_connected' p).reaches
      (mem_deleteVerts_singleton_of_ne hqG (Ne.symm hpq))
      (mem_deleteVerts_singleton_of_ne hbG hbp)).exists_isPath
    have hfresh : p ∉ G.walkVertices q D := by
      rintro hmem
      rcases mem_walkVertices_iff.1 hmem with rfl | ⟨g', hg', hinc⟩
      · exact hpq rfl
      · exact hD.isWalk.notMem_of_inc_of_deleteVerts hinc hg'
    refine ⟨p, b, g :: D, g, .cons hlpq (hD.mono deleteVerts_le) hfresh, Ne.symm hbp, hpK,
      hbK, List.mem_cons_self, fun hgK ↦ ?_⟩
    
    exact hqK ((hKG.isLink_iff hgK).2 hlpq).right_mem
  · 
    push Not at hout
    obtain ⟨g, hgG, hgK⟩ := hproper.resolve_left (by rintro ⟨x, hx, hx'⟩; exact hx' (hout x hx))
    obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hgG
    have hne : p ≠ q := by rintro rfl; exact hnl hpq
    exact ⟨p, q, [g], g, .single hpq hne, hne, hout p hpq.left_mem, hout q hpq.right_mem,
      List.mem_cons_self, hgK⟩

 



theorem IsTwoConnected.grows_by_ear (hG : G.IsTwoConnected) (hK : K.IsTwoConnected)
    (hKG : K ≤ G) (hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x)
    (hproper : (∃ x ∈ V(G), x ∉ V(K)) ∨ (∃ g ∈ E(G), g ∉ E(K))) :
    ∃ B : Graph α β, B.IsTwoConnected ∧ K ≤ B ∧ B ≤ G ∧ ∃ g ∈ E(B), g ∉ E(K) := by
  obtain ⟨a, b, D, g, hpath, hab, haK, hbK, hgD, hgK⟩ := hG.ear_exists hK hKG hnl hproper
  
  have hearle : G.pathGraphOf a D ≤ G := pathGraphOf_le hpath.isWalk
  have hearP : (G.pathGraphOf a D).IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  exact ⟨K.union (G.pathGraphOf a D),
    hK.ear (Compatible.of_le_le hKG hearle) hearP hab haK hbK,
    left_le_union _ _, union_le hKG hearle, g,
    Set.mem_union_right _ (hearP.mem_edgeSet hgD), hgK⟩

end Graph
