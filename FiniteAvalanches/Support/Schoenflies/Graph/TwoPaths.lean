/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/TwoPaths.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Graph.PathGraph
import FiniteAvalanches.Support.Schoenflies.Graph.TwoConnected

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 























open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {K P Q : Graph α β} {u v c : α} {W₁ W₂ : List β}

 










theorem isTwoConnected_of_two_paths (hPK : P ≤ K) (hQK : Q ≤ K) (hV : V(K) ⊆ V(P) ∪ V(Q))
    (hP : P.IsPathGraph u W₁ v) (hQ : Q.IsPathGraph u W₂ v) (huv : u ≠ v)
    (hmeet : ∀ x ∈ V(P), x ∈ V(Q) → x = u ∨ x = v) (h3 : K.HasThreeVertices) :
    K.IsTwoConnected where
  hasThreeVertices := h3
  connected :=
    Connected.of_two_subgraphs hPK hQK hV hP.connected hQ.connected hP.source_mem hQ.source_mem
  deleteVerts_connected := by
    intro c _
    
    have hreach : ∀ x ∈ V(K), x ≠ c →
        (K.deleteVerts {c}).Reaches x u ∨ (K.deleteVerts {c}).Reaches x v := by
      intro x hx hxc
      rcases hV hx with h | h
      · exact (hP.reaches_an_end h hxc).imp (fun hr ↦ hr.mono (deleteVerts_mono hPK _))
          fun hr ↦ hr.mono (deleteVerts_mono hPK _)
      · exact (hQ.reaches_an_end h hxc).imp (fun hr ↦ hr.mono (deleteVerts_mono hQK _))
          fun hr ↦ hr.mono (deleteVerts_mono hQK _)
    have huK : u ∈ V(K) := hPK.vertexSet_mono hP.source_mem
    have hvK : v ∈ V(K) := hPK.vertexSet_mono hP.target_mem
    by_cases hcu : c = u
    · 
      
      refine Connected.of_hub
        (mem_deleteVerts_singleton_of_ne hvK (by rw [hcu]; exact Ne.symm huv)) ?_
      intro x hx
      rw [vertexSet_deleteVerts] at hx
      have hxc : x ≠ c := fun h ↦ hx.2 (by simp [h])
      rcases hreach x hx.1 hxc with hr | hr
      · exact absurd hcu.symm (mem_deleteVerts_singleton.1 hr.right_mem).2
      · exact hr.symm
    by_cases hcv : c = v
    · refine Connected.of_hub
        (mem_deleteVerts_singleton_of_ne huK (fun h ↦ hcu h.symm)) ?_
      intro x hx
      rw [vertexSet_deleteVerts] at hx
      have hxc : x ≠ c := fun h ↦ hx.2 (by simp [h])
      rcases hreach x hx.1 hxc with hr | hr
      · exact hr.symm
      · exact absurd hcv.symm (mem_deleteVerts_singleton.1 hr.right_mem).2
    
    have hvu : (K.deleteVerts {c}).Reaches v u := by
      by_cases hcP : c ∈ V(P)
      · have hcQ : c ∉ V(Q) := fun h ↦ by
          rcases hmeet c hcP h with h' | h'
          exacts [hcu h', hcv h']
        have hr := hQ.connected.reaches hQ.target_mem hQ.source_mem
        rw [← deleteVerts_singleton_eq_self hcQ] at hr
        exact hr.mono (deleteVerts_mono hQK _)
      · have hr := hP.connected.reaches hP.target_mem hP.source_mem
        rw [← deleteVerts_singleton_eq_self hcP] at hr
        exact hr.mono (deleteVerts_mono hPK _)
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne huK (fun h ↦ hcu h.symm)) ?_
    intro x hx
    rw [vertexSet_deleteVerts] at hx
    have hxc : x ≠ c := fun h ↦ hx.2 (by simp [h])
    rcases hreach x hx.1 hxc with hr | hr
    · exact hr.symm
    · exact (hr.trans hvu).symm

end Graph
