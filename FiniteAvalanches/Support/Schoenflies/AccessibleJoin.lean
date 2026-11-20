/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/AccessibleJoin.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.SimpleArc
import FiniteAvalanches.Support.Schoenflies.Accessible
import FiniteAvalanches.Support.Schoenflies.LocallyPolygonal

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 














































































open Metric Set

namespace Schoenflies

variable {Ω C D S : Set Plane} {a b z : Plane}

 

 



def PolyAccessible (Ω : Set Plane) (a : Plane) : Prop :=
  ∃ (vs : List Plane) (h : vs ≠ []), vs.head h = a ∧ vs.getLast h ∈ Ω ∧ poly vs \ {a} ⊆ Ω

 
theorem polyAccessible_of_mem (ha : a ∈ Ω) : PolyAccessible Ω a :=
  ⟨[a], by simp, rfl, by simpa using ha, by simp⟩

 
theorem PolyAccessible.mono (h : PolyAccessible Ω a) (hsub : Ω ⊆ S) : PolyAccessible S a := by
  obtain ⟨vs, hvs, hhead, hlast, hint⟩ := h
  exact ⟨vs, hvs, hhead, hsub hlast, hint.trans hsub⟩

 

theorem PolyAccessible.of_openSegment (hz : z ∈ Ω) (hseg : openSegment ℝ a z ⊆ Ω) :
    PolyAccessible Ω a := by
  refine ⟨[a, z], by simp, rfl, by simpa using hz, ?_⟩
  rw [poly_pair]
  rintro x ⟨hxseg, hxa⟩
  rw [mem_singleton_iff] at hxa
  
  rcases eq_or_ne x z with rfl | hxz
  · exact hz
  · exact hseg (mem_openSegment_of_ne_left_right (Ne.symm hxa) (Ne.symm hxz) hxseg)

 

theorem StronglyAccessible.polyAccessible (h : StronglyAccessible Ω a) : PolyAccessible Ω a := by
  obtain ⟨z, hz, -, hseg⟩ := h.openSegment_subset
  exact PolyAccessible.of_openSegment hz hseg

 





theorem polyAccessible_of_poly {vs : List Plane} (h : vs ≠ []) (hhead : vs.head h = a)
    (hlast : vs.getLast h ≠ a) (hsub : poly vs \ {a} ⊆ Ω) : PolyAccessible Ω a :=
  ⟨vs, h, hhead, hsub ⟨getLast_mem_poly h, hlast⟩, hsub⟩

 

theorem polyAccessible_of_poly' {vs : List Plane} (h : vs ≠ []) (hlast : vs.getLast h = a)
    (hhead : vs.head h ≠ a) (hsub : poly vs \ {a} ⊆ Ω) : PolyAccessible Ω a := by
  have hrev : vs.reverse ≠ [] := by simpa using h
  refine polyAccessible_of_poly hrev ?_ ?_ ?_
  · rw [List.head_reverse]; exact hlast
  · rw [List.getLast_reverse]; exact hhead
  · rw [poly_reverse]; exact hsub

 




theorem PolyAccessible.exists_simple (h : PolyAccessible Ω a) (ha : a ∉ Ω) :
    ∃ z ∈ Ω, a ≠ z ∧ ∃ (vs : List Plane) (hv : vs ≠ []),
      vs.head hv = a ∧ vs.getLast hv = z ∧ poly vs \ {a} ⊆ Ω ∧ IsArcBetween (poly vs) a z := by
  obtain ⟨vs, hvs, hhead, hlast, hint⟩ := h
  set z := vs.getLast hvs with hz
  have hne : a ≠ z := fun hcon => ha (hcon ▸ hlast)
  obtain ⟨ws, hws, hwhead, hwlast, hwsub, hwarc⟩ :=
    exists_simple_poly_of_poly (isConnected_poly hvs).2 hne
      (hhead ▸ head_mem_poly hvs) (getLast_mem_poly hvs)
  exact ⟨z, hlast, hne, ws, hws, hwhead, hwlast,
    fun x hx => hint ⟨hwsub hx.1, hx.2⟩, hwarc⟩

 





 

theorem biUnion_list_map {ι : Type*} (f : ι → Set Plane) (l : List ι) :
    (⋃ A ∈ l.map f, A) = ⋃ i ∈ l, f i := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, biUnion_list_cons (fun A : Set Plane => A),
      biUnion_list_cons f, ih]

 





theorem exists_simple_poly_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ i ∈ s, A i) ∧ IsArcBetween (poly ws) a b := by
  classical
  
  set l : List ι := hs.toFinset.toList with hl
  have hlmem : ∀ i, i ∈ l ↔ i ∈ s := by
    intro i; rw [hl, Finset.mem_toList, hs.mem_toFinset]
  have hU : (⋃ B ∈ l.map A, B) = ⋃ i ∈ s, A i := by
    rw [biUnion_list_map]
    exact iUnion_congr fun i => iUnion_congr_Prop (hlmem i) fun _ => rfl
  have hpoly : ∀ B ∈ l.map A, IsPolygonal B := by
    intro B hB
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hB
    exact hA i ((hlmem i).1 hi)
  have := exists_simple_poly_of_union hpoly (hU ▸ hconn) hab (hU ▸ ha) (hU ▸ hb)
  rwa [hU] at this

 









theorem exists_simple_poly_pinned {ι : Type*} {s : Set ι} {A : ι → Set Plane} {E : Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i)
    (hS : (⋃ i ∈ s, A i) \ E ⊆ S) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ i ∈ s, A i) ∧ poly ws \ E ⊆ S ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_biUnion_finite hs hA hconn hab ha hb
  exact ⟨ws, hws, hhead, hlast, hsub, fun x hx => hS ⟨hsub hx.1, hx.2⟩, harc⟩

 
theorem exists_simple_poly_of_isPolygonal_pinned {Y E : Set Plane} (hY : IsPolygonal Y)
    (hconn : IsPreconnected Y) (hab : a ≠ b) (ha : a ∈ Y) (hb : b ∈ Y) (hS : Y \ E ⊆ S) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ Y ∧ poly ws \ E ⊆ S ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_isPolygonal hY hconn hab ha hb
  exact ⟨ws, hws, hhead, hlast, hsub, fun x hx => hS ⟨hsub hx.1, hx.2⟩, harc⟩

 
theorem exists_simple_arc_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i) :
    ∃ P ⊆ (⋃ i ∈ s, A i), IsPolygonal P ∧ IsArcBetween P a b := by
  obtain ⟨ws, -, -, -, hsub, harc⟩ :=
    exists_simple_poly_of_biUnion_finite hs hA hconn hab ha hb
  exact ⟨poly ws, hsub, ⟨ws, rfl⟩, harc⟩

 









 






theorem exists_crosscut_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (haC : a ∈ C) (hbC : b ∈ C)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i)
    (hmeet : (⋃ i ∈ s, A i) ∩ C ⊆ {a, b}) (hD : (⋃ i ∈ s, A i) \ C ⊆ D) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ i ∈ s, A i) ∧ IsArcBetween (poly ws) a b ∧
      poly ws ∩ C = {a, b} ∧ poly ws \ {a, b} ⊆ D := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_biUnion_finite hs hA hconn hab ha hb
  have haw : a ∈ poly ws := hhead ▸ head_mem_poly hws
  have hbw : b ∈ poly ws := hlast ▸ getLast_mem_poly hws
  refine ⟨ws, hws, hhead, hlast, hsub, harc, ?_, ?_⟩
  · refine subset_antisymm (fun x hx => hmeet ⟨hsub hx.1, hx.2⟩) ?_
    rintro x (rfl | rfl)
    exacts [⟨haw, haC⟩, ⟨hbw, hbC⟩]
  · 
    rintro x ⟨hx, hxab⟩
    exact hD ⟨hsub hx, fun hxC => hxab (hmeet ⟨hsub hx, hxC⟩)⟩

 

theorem exists_crosscut_arc_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hconn : IsPreconnected (⋃ i ∈ s, A i)) (hab : a ≠ b)
    (haC : a ∈ C) (hbC : b ∈ C)
    (ha : a ∈ ⋃ i ∈ s, A i) (hb : b ∈ ⋃ i ∈ s, A i)
    (hmeet : (⋃ i ∈ s, A i) ∩ C ⊆ {a, b}) (hD : (⋃ i ∈ s, A i) \ C ⊆ D) :
    ∃ P ⊆ (⋃ i ∈ s, A i), IsPolygonal P ∧ IsArcBetween P a b ∧
      P ∩ C = {a, b} ∧ P \ {a, b} ⊆ D := by
  obtain ⟨ws, -, -, -, hsub, harc, hcut, hint⟩ :=
    exists_crosscut_of_biUnion_finite hs hA hconn hab haC hbC ha hb hmeet hD
  exact ⟨poly ws, hsub, ⟨ws, rfl⟩, harc, hcut, hint⟩

 

 








theorem exists_simple_poly_of_polyAccessible (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hab : a ≠ b) (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws \ {a, b} ⊆ Ω ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨as, has, hahead, halast, haint⟩ := ha
  obtain ⟨bs, hbs, hbhead, hblast, hbint⟩ := hb
  
  obtain ⟨ms, hms, hmsub, hmhead, hmlast⟩ :=
    exists_poly_of_isPreconnected hΩ hconn halast hblast
  
  set U : Set Plane := poly as ∪ (poly ms ∪ poly bs) with hU
  have hlist : (⋃ vs ∈ [as, ms, bs], poly vs) = U := by
    rw [biUnion_list_cons (fun vs : List Plane => poly vs),
      biUnion_list_cons (fun vs : List Plane => poly vs),
      biUnion_list_cons (fun vs : List Plane => poly vs), hU]
    simp
  have hconnU : IsPreconnected U := by
    refine (IsConnected.union ?_ (isConnected_poly has) (IsConnected.union ?_
      (isConnected_poly hms) (isConnected_poly hbs))).2
    · exact ⟨as.getLast has, getLast_mem_poly has,
        Or.inl (hmhead ▸ head_mem_poly hms)⟩
    · exact ⟨ms.getLast hms, getLast_mem_poly hms, hmlast ▸ getLast_mem_poly hbs⟩
  
  have hUΩ : U \ {a, b} ⊆ Ω := by
    rintro x ⟨hx, hxab⟩
    rcases hx with hx | hx | hx
    · exact haint ⟨hx, fun hxa => hxab (Or.inl (hahead ▸ hxa))⟩
    · exact hmsub hx
    · exact hbint ⟨hx, fun hxb => hxab (Or.inr (hbhead ▸ hxb))⟩
  have haU : a ∈ U := Or.inl (hahead ▸ head_mem_poly has)
  have hbU : b ∈ U := Or.inr (Or.inr (hbhead ▸ head_mem_poly hbs))
  obtain ⟨ws, hws, hwhead, hwlast, hwsub, hwarc⟩ :=
    exists_simple_poly_of_biUnion (L := [as, ms, bs]) (hlist ▸ hconnU) hab
      (hlist ▸ haU) (hlist ▸ hbU)
  rw [hlist] at hwsub
  exact ⟨ws, hws, hwhead, hwlast, fun x hx => hUΩ ⟨hwsub hx.1, hx.2⟩, hwarc⟩

 
theorem exists_simple_arc_of_polyAccessible (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hab : a ≠ b) (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P a b ∧ P \ {a, b} ⊆ Ω := by
  obtain ⟨ws, -, -, -, hsub, harc⟩ :=
    exists_simple_poly_of_polyAccessible hΩ hconn hab ha hb
  exact ⟨poly ws, ⟨ws, rfl⟩, harc, hsub⟩

 


theorem exists_crosscut_of_polyAccessible (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hdisj : Disjoint Ω C) (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws \ {a, b} ⊆ Ω ∧ IsArcBetween (poly ws) a b ∧ poly ws ∩ C = {a, b} := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_polyAccessible hΩ hconn hab ha hb
  refine ⟨ws, hws, hhead, hlast, hsub, harc, subset_antisymm ?_ ?_⟩
  · 
    rintro x ⟨hxw, hxC⟩
    by_contra hxab
    exact (hdisj.ne_of_mem (hsub ⟨hxw, hxab⟩) hxC) rfl
  · rintro x (rfl | rfl)
    exacts [⟨hhead ▸ head_mem_poly hws, haC⟩, ⟨hlast ▸ getLast_mem_poly hws, hbC⟩]

end Schoenflies

 







namespace Graph

open Schoenflies Set

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {a b : Plane}

 

theorem pointSet_eq_biUnion (G : Graph Plane β) (drawing : β → ℝ → Plane) :
    pointSet G drawing =
      ⋃ i ∈ (Sum.inl '' V(G) ∪ Sum.inr '' E(G) : Set (Plane ⊕ β)),
        Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing) i := by
  rw [biUnion_union, biUnion_image, biUnion_image]
  simp only [Sum.elim_inl, Sum.elim_inr, biUnion_of_singleton]
  rfl

 





theorem exists_simple_poly_of_pointSet [G.Finite]
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hconn : IsPreconnected (pointSet G drawing)) (hab : a ≠ b)
    (ha : a ∈ pointSet G drawing) (hb : b ∈ pointSet G drawing) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ pointSet G drawing ∧ IsArcBetween (poly ws) a b := by
  have hfin : (Sum.inl '' V(G) ∪ Sum.inr '' E(G) : Set (Plane ⊕ β)).Finite :=
    ((G.finite_vertexSet).image _).union ((G.finite_edgeSet).image _)
  have hA : ∀ i ∈ (Sum.inl '' V(G) ∪ Sum.inr '' E(G) : Set (Plane ⊕ β)),
      IsPolygonal (Sum.elim (fun v : Plane => ({v} : Set Plane)) (edgeArc drawing) i) := by
    rintro (v | e) hi
    · exact ⟨[v], rfl⟩
    · refine hpoly e ?_
      rcases hi with ⟨x, -, hx⟩ | ⟨x, hx, hx'⟩
      · exact absurd hx (by simp)
      · exact (Sum.inr_injective hx') ▸ hx
  rw [pointSet_eq_biUnion G drawing] at hconn ha hb ⊢
  exact exists_simple_poly_of_biUnion_finite hfin hA hconn hab ha hb

end Graph
