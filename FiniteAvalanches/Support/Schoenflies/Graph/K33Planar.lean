/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/K33Planar.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Graph.K33
import FiniteAvalanches.Support.Schoenflies.Graph.Redrawing
import FiniteAvalanches.Support.Schoenflies.AlternatingCrosscuts

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 



































































open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s t : Fin 3} {R : Set Plane}

 






 







def IsHexCrosscut (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁) (J₂ : ClosedPolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (yref : Plane),
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      IsPolygonalCrosscut C J₁ J₂ K a k yref

 

theorem isSeparating_hexSet (h : IsHexCrosscut drawing e s) :
    IsSeparating (hexSet drawing e) := by
  obtain ⟨_, _, _, C, _, _, _, _, _, _, hcar, _⟩ := h
  exact hcar ▸ C.isSeparating_carrier

namespace IsK33Config

 





 
theorem x_succ_mem_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    x (s + 1) ∈ edgesCover drawing (arcA e s) \ ({x s, y (s + 1)} : Set Plane) := by
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  refine ⟨mem_arcA_iff.2 ⟨(s + 1, s), by simp [arcAPairs],
    (hd.edge_isArcBetween (h.isLink (s + 1) s)).left_mem⟩, ?_⟩
  rintro (hc | hc)
  exacts [h.x_ne_x (hs1 s) hc, h.x_ne_y _ _ hc]

 
theorem y_succ_mem_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    y (s + 1 + 1) ∈ edgesCover drawing (arcB e s) \ ({x s, y (s + 1)} : Set Plane) := by
  have hsucc : ∀ s : Fin 3, s + 1 + 1 = s + 2 := by decide
  have hs2 : ∀ s : Fin 3, s + 2 ≠ s + 1 := by decide
  rw [hsucc s]
  refine ⟨mem_arcB_iff.2 ⟨(s + 2, s + 2), by simp [arcBPairs],
    (hd.edge_isArcBetween (h.isLink (s + 2) (s + 2))).right_mem⟩, ?_⟩
  rintro (hc | hc)
  exacts [h.y_ne_x _ _ hc, h.y_ne_y (hs2 s) hc]

 

 
theorem chord_openArc_subset_edgeArc (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : openArc (drawing (e s (s + 1))) ⊆ edgeArc drawing (e s (s + 1)) := by
  rw [h.chord_openArc_eq hd s]; exact Set.sdiff_subset

 



theorem exists_two_chords_same_region (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hsep : IsSeparating (hexSet drawing e)) :
    ∃ s t : Fin 3, s ≠ t ∧ ∃ R : Set Plane, IsRegionOf (hexSet drawing e) R ∧
      openArc (drawing (e s (s + 1))) ⊆ R ∧ openArc (drawing (e t (t + 1))) ⊆ R := by
  obtain ⟨s, t, hst, hcase⟩ := h.exists_two_chords_same_side hd hsep.isOpen_inside
    hsep.isOpen_outside disjoint_inside_outside (inside_union_outside _).ge
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨s, t, hst, _, IsRegionOf.inside _, h1, h2⟩
  · exact ⟨s, t, hst, _, IsRegionOf.outside _, h1, h2⟩

 







 
theorem endpoints_subset_arcA (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ({x s, y (s + 1)} : Set Plane) ⊆ edgesCover drawing (arcA e s) := by
  rintro p (rfl | rfl)
  · exact mem_arcA_iff.2 ⟨(s, s), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink s s)).left_mem⟩
  · exact mem_arcA_iff.2 ⟨(s + 1, s + 1), by simp [arcAPairs],
      (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1))).right_mem⟩

 
theorem endpoints_subset_arcB (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    ({x s, y (s + 1)} : Set Plane) ⊆ edgesCover drawing (arcB e s) := by
  rintro p (rfl | rfl)
  · exact mem_arcB_iff.2 ⟨(s, s + 2), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink s (s + 2))).left_mem⟩
  · exact mem_arcB_iff.2 ⟨(s + 2, s + 1), by simp [arcBPairs],
      (hd.edge_isArcBetween (h.isLink (s + 2) (s + 1))).right_mem⟩

 


theorem exists_reference_point (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hsep : IsSeparating (hexSet drawing e)) (s : Fin 3) :
    ∃ yref : Plane, yref ∉ hexSet drawing e ∧
      Disjoint (edgeArc drawing (e s (s + 1)))
        (connectedComponentIn (hexSet drawing e)ᶜ yref) := by
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzC : z ∉ hexSet drawing e := h.chord_openArc_subset_compl hd s hz
  
  have hpair := hsep.isRegionPair_farRegion hzC
  obtain ⟨yref, hyref⟩ := (hpair.right.isConnected hsep).nonempty
  refine ⟨yref, hpair.right.subset_compl hyref, ?_⟩
  rw [hpair.right.connectedComponentIn_eq hsep hyref, Set.disjoint_left]
  intro p hp hpfar
  by_cases hpin : p ∈ ({x s, y (s + 1)} : Set Plane)
  · refine hpfar.1 ?_
    rcases hpin with rfl | rfl
    exacts [h.x_mem_hexSet hd s, h.y_mem_hexSet hd (s + 1)]
  · refine hpfar.2 (h.chord_openArc_subset_connectedComponentIn hd s hz ?_)
    rw [h.chord_openArc_eq hd s]
    exact ⟨hp, hpin⟩

end IsK33Config

 







 







def IsHexRealization (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁) (J₂ : ClosedPolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ),
      k ≤ m + 3 ∧
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      SameEdges J₁.pieces (C.arcPieces a k ++ K) ∧
      SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K)

namespace IsK33Config

 



theorem isHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hr : IsHexRealization drawing e s) : IsHexCrosscut drawing e s := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, hk, hcar, hA, hB, hK, hE₁, hE₂⟩ := hr
  have hsep : IsSeparating (hexSet drawing e) := hcar ▸ C.isSeparating_carrier
  obtain ⟨yref, hyref, hdisj⟩ := h.exists_reference_point hd hsep s
  refine ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK,
    ⟨hk, hE₁, hE₂, ?_, ?_, ?_, ?_⟩⟩
  · rw [hK, hcar, hA, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcA hd s
  · rw [hK, hcar, hB, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcB hd s
  · rw [hcar]; exact hyref
  · rw [hK, hcar]; exact hdisj

 

 



theorem false_of_isHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : IsHexCrosscut drawing e s) (hsep : IsSeparating (hexSet drawing e))
    (hR : IsRegionOf (hexSet drawing e) R)
    (h1 : openArc (drawing (e s (s + 1))) ⊆ R)
    (h2 : openArc (drawing (e (s + 1) (s + 1 + 1))) ⊆ R) : False := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK, hcc⟩ := hcross
  
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzK : z ∈ cover K := by rw [hK]; exact h.chord_openArc_subset_edgeArc hd s hz
  have hzC : z ∉ C.carrier := by rw [hcar]; exact h.chord_openArc_subset_compl hd s hz
  have hzR : z ∈ R := h1 hz
  
  have hside : edgeArc drawing (e (s + 1) (s + 1 + 1)) \ ({x (s + 1), y (s + 1 + 1)} : Set Plane)
      ⊆ connectedComponentIn C.carrierᶜ z := by
    rw [hcar, hR.connectedComponentIn_eq hsep hzR, ← h.chord_openArc_eq hd (s + 1)]
    exact h2
  
  obtain ⟨w, hw₁, hw₂⟩ := hcc.alternating_inter_nonempty_of_same_side hzK hzC hA hB
    (h.arcs_inter hd s) (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1 + 1))) hside
    (h.x_succ_mem_arcA hd s) (h.y_succ_mem_arcB hd s)
  
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  have := h.chords_disjoint hd (hs1 s)
  rw [Set.eq_empty_iff_forall_notMem] at this
  exact this w ⟨hw₁, by rwa [hK] at hw₂⟩

 


theorem false_of_hexCrosscuts (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : ∀ s : Fin 3, IsHexCrosscut drawing e s) : False := by
  have hsep : IsSeparating (hexSet drawing e) := isSeparating_hexSet (hcross 0)
  obtain ⟨s, t, hst, R, hR, h1, h2⟩ := h.exists_two_chords_same_region hd hsep
  
  have hpair : ∀ s t : Fin 3, s ≠ t → t = s + 1 ∨ s = t + 1 := by decide
  rcases hpair s t hst with rfl | rfl
  · exact h.false_of_isHexCrosscut hd (hcross s) hsep hR h1 h2
  · exact h.false_of_isHexCrosscut hd (hcross t) hsep hR h2 h1

 
theorem false_of_hexRealizations (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hr : ∀ s : Fin 3, IsHexRealization drawing e s) : False :=
  h.false_of_hexCrosscuts hd fun s => h.isHexCrosscut hd (hr s)

 







theorem not_isDrawing [G.Finite] (h : IsK33Config G x y e)
    (hreal : ∀ dr : β → ℝ → Plane, IsDrawing G dr → (∀ f ∈ E(G), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : β → ℝ → Plane, IsDrawing G dr' ∧ ∀ s : Fin 3, IsHexRealization dr' e s) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly⟩ := polygonal_redrawing G dr hdr
  obtain ⟨dr'', hdr'', hr⟩ := hreal dr' hdr' hpoly
  exact h.false_of_hexRealizations hdr'' hr

end IsK33Config

 






 





structure IsArcK33 (x y : Fin 3 → Plane) (P : Fin 3 → Fin 3 → Set Plane) : Prop where
   
  arc : ∀ i j, IsArcBetween (P i j) (x i) (y j)
   
  x_injective : Function.Injective x
   
  y_injective : Function.Injective y
   
  ne : ∀ i j, x i ≠ y j
   
  meet : ∀ i j k l, (i, j) ≠ (k, l) →
    P i j ∩ P k l ⊆ ({x i, y j} : Set Plane) ∩ ({x k, y l} : Set Plane)

 


def k33Graph (x y : Fin 3 → Plane) : Graph Plane (Fin 3 × Fin 3) where
  vertexSet := Set.range x ∪ Set.range y
  edgeSet := Set.univ
  IsLink p u v := (u = x p.1 ∧ v = y p.2) ∨ (u = y p.2 ∧ v = x p.1)
  isLink_symm := by
    rintro ⟨i, j⟩ -
    constructor
    rintro u v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    exacts [Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩]
  eq_or_eq_of_isLink_of_isLink := by
    rintro ⟨i, j⟩ u v a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  edge_mem_iff_exists_isLink := by
    rintro ⟨i, j⟩
    exact ⟨fun _ => ⟨x i, y j, Or.inl ⟨rfl, rfl⟩⟩, fun _ => Set.mem_univ _⟩
  left_mem_of_isLink := by
    rintro ⟨i, j⟩ u v (⟨rfl, -⟩ | ⟨rfl, -⟩)
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩]

@[simp] theorem k33Graph_vertexSet (x y : Fin 3 → Plane) :
    V(k33Graph x y) = Set.range x ∪ Set.range y := rfl

@[simp] theorem k33Graph_edgeSet (x y : Fin 3 → Plane) :
    E(k33Graph x y) = (Set.univ : Set (Fin 3 × Fin 3)) := rfl

theorem k33Graph_isLink (x y : Fin 3 → Plane) (i j : Fin 3) :
    (k33Graph x y).IsLink (i, j) (x i) (y j) := Or.inl ⟨rfl, rfl⟩

 
theorem k33Graph_inc {x y : Fin 3 → Plane} {i j : Fin 3} {p : Plane}
    (hp : p ∈ ({x i, y j} : Set Plane)) : (k33Graph x y).Inc (i, j) p := by
  rcases hp with rfl | rfl
  · exact ⟨y j, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨x i, Or.inr ⟨rfl, rfl⟩⟩

instance (x y : Fin 3 → Plane) : (k33Graph x y).Finite where
  finite_vertexSet := (Set.finite_range x).union (Set.finite_range y)
  finite_edgeSet := Set.finite_univ

namespace IsArcK33

variable {x y : Fin 3 → Plane} {P : Fin 3 → Fin 3 → Set Plane}

 


noncomputable def arcDrawing (h : IsArcK33 x y P) : Fin 3 × Fin 3 → ℝ → Plane :=
  fun p => (h.arc p.1 p.2).choose

theorem edgeArc_eq (h : IsArcK33 x y P) (i j : Fin 3) :
    edgeArc h.arcDrawing (i, j) = P i j := (h.arc i j).choose_spec.2.2.1

theorem arcDrawing_zero (h : IsArcK33 x y P) (i j : Fin 3) : h.arcDrawing (i, j) 0 = x i :=
  (h.arc i j).choose_spec.2.2.2.1

theorem arcDrawing_one (h : IsArcK33 x y P) (i j : Fin 3) : h.arcDrawing (i, j) 1 = y j :=
  (h.arc i j).choose_spec.2.2.2.2

 

theorem mem_arc_elim (h : IsArcK33 x y P) {i j : Fin 3} {p : Plane}
    (hpV : p ∈ Set.range x ∪ Set.range y) (hp : p ∈ P i j) :
    p ∈ ({x i, y j} : Set Plane) := by
  have hsucc : ∀ i : Fin 3, i + 1 ≠ i := by decide
  rcases hpV with ⟨k, rfl⟩ | ⟨l, rfl⟩
  · 
    exact (h.meet i j k (j + 1) (fun hc => hsucc j (congrArg Prod.snd hc).symm)
      ⟨hp, (h.arc k (j + 1)).left_mem⟩).1
  · 
    exact (h.meet i j (i + 1) l (fun hc => hsucc i (congrArg Prod.fst hc).symm)
      ⟨hp, (h.arc (i + 1) l).right_mem⟩).1

 
theorem isDrawing (h : IsArcK33 x y P) : IsDrawing (k33Graph x y) h.arcDrawing := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, j⟩ -
    obtain ⟨hc, hi, -, -, -⟩ := (h.arc i j).choose_spec
    refine ⟨hc, hi, ?_⟩
    rw [show h.arcDrawing (i, j) 0 = x i from h.arcDrawing_zero i j,
      show h.arcDrawing (i, j) 1 = y j from h.arcDrawing_one i j]
    exact k33Graph_isLink x y i j
  · rintro ⟨i, j⟩ u v w hl hwV hw
    have hmem : w ∈ ({x i, y j} : Set Plane) :=
      h.mem_arc_elim hwV (by rwa [h.edgeArc_eq i j] at hw)
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem
    · exact hmem.symm
  · rintro ⟨i, j⟩ ⟨k, l⟩ - - hne p hp hq
    rw [h.edgeArc_eq i j] at hp
    rw [h.edgeArc_eq k l] at hq
    obtain ⟨hij, hkl⟩ := h.meet i j k l hne ⟨hp, hq⟩
    refine ⟨?_, k33Graph_inc hij, k33Graph_inc hkl⟩
    rcases hij with rfl | rfl
    exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨j, rfl⟩]

 
theorem isK33Config (h : IsArcK33 x y P) :
    IsK33Config (k33Graph x y) x y (fun i j => (i, j)) where
  isLink := k33Graph_isLink x y
  x_injective := h.x_injective
  y_injective := h.y_injective
  ne := h.ne

 

theorem false_of_realization (h : IsArcK33 x y P)
    (hreal : ∀ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr →
      (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr' ∧
        ∀ s : Fin 3, IsHexRealization dr' (fun i j => (i, j)) s) : False :=
  h.isK33Config.not_isDrawing hreal ⟨h.arcDrawing, h.isDrawing⟩

end IsArcK33

 

variable {H : Graph Plane β} {W : Fin 3 → Fin 3 → List β}

 





structure IsK33Subdivision (H : Graph Plane β) (x y : Fin 3 → Plane)
    (W : Fin 3 → Fin 3 → List β) : Prop where
   
  isPath : ∀ i j, H.IsPath (x i) (W i j) (y j)
   
  x_injective : Function.Injective x
   
  y_injective : Function.Injective y
   
  ne : ∀ i j, x i ≠ y j
   
  edge_ne : ∀ i j k l, (i, j) ≠ (k, l) → ∀ f ∈ W i j, f ∉ W k l
   
  vertex_meet : ∀ i j k l, (i, j) ≠ (k, l) → ∀ v ∈ H.walkVertices (x i) (W i j),
    v ∈ H.walkVertices (x k) (W k l) → v ∈ ({x i, y j} : Set Plane) ∩ ({x k, y l} : Set Plane)

namespace IsK33Subdivision

variable {x y : Fin 3 → Plane}

 
theorem ne_nil (h : IsK33Subdivision H x y W) (i j : Fin 3) : W i j ≠ [] := by
  intro hnil
  have hp := h.isPath i j
  rw [hnil] at hp
  exact h.ne i j hp.isWalk.eq_of_nil

 



theorem isArcK33 {drawing : β → ℝ → Plane} (hd : IsDrawing H drawing)
    (h : IsK33Subdivision H x y W) : IsArcK33 x y fun i j => edgesCover drawing (W i j) := by
  refine ⟨fun i j => hd.path_isArcBetween (h.isPath i j) (h.ne_nil i j), h.x_injective,
    h.y_injective, h.ne, ?_⟩
  rintro i j k l hne p ⟨hp1, hp2⟩
  obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hp1
  obtain ⟨g, hg, hpg⟩ := mem_edgesCover_iff.1 hp2
  have hfg : f ≠ g := fun hEq => h.edge_ne i j k l hne f hf (hEq ▸ hg)
  obtain ⟨-, hincf, hincg⟩ := hd.edge_inter ((h.isPath i j).edge_mem hf)
    ((h.isPath k l).edge_mem hg) hfg hpf hpg
  exact h.vertex_meet i j k l hne p (mem_walkVertices_of_mem_covered ⟨f, hf, hincf⟩)
    (mem_walkVertices_of_mem_covered ⟨g, hg, hincg⟩)

 



theorem false_of_realization {drawing : β → ℝ → Plane} (hd : IsDrawing H drawing)
    (h : IsK33Subdivision H x y W)
    (hreal : ∀ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr →
      (∀ f ∈ E(k33Graph x y), IsPolygonal (edgeArc dr f)) →
      ∃ dr' : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr' ∧
        ∀ s : Fin 3, IsHexRealization dr' (fun i j => (i, j)) s) : False :=
  (h.isArcK33 hd).false_of_realization hreal

end IsK33Subdivision

end Graph
