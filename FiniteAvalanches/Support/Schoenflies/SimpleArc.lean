/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/SimpleArc.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.OverlayGraph
import FiniteAvalanches.Support.Schoenflies.Graph.CycleJordan

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 






























































open Metric Set
open scoped Graph

namespace Schoenflies

variable {pieces : List Piece} {points : List Plane} {Ω : Set Plane} {a b x y : Plane}

 





 
theorem poly_cons_of_ne_nil {vs : List Plane} (h : vs ≠ []) (u : Plane) :
    poly (u :: vs) = segment ℝ u (vs.head h) ∪ poly vs := by
  match vs, h with
  | _ :: _, _ => rfl

 







open scoped Classical in
 

noncomputable def segsOf : List Plane → List Piece
  | [] => []
  | [_] => []
  | u :: v :: rest => if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest)

@[simp] theorem segsOf_nil : segsOf [] = [] := rfl

@[simp] theorem segsOf_singleton (v : Plane) : segsOf [v] = [] := rfl

open scoped Classical in
theorem segsOf_cons_cons (u v : Plane) (rest : List Plane) :
    segsOf (u :: v :: rest) =
      if u = v then segsOf (v :: rest) else (u, v) :: segsOf (v :: rest) := rfl

 
theorem segsOf_nondeg (vs : List Plane) : ∀ P ∈ segsOf vs, P.Nondeg := by
  classical
  induction vs with
  | nil => simp
  | cons u tl ih =>
    match tl, ih with
    | [], _ => simp
    | v :: rest, ih =>
      rw [segsOf_cons_cons]
      split_ifs with huv
      · exact ih
      · intro P hP
        rcases List.mem_cons.1 hP with rfl | hP
        · exact huv
        · exact ih P hP

 

theorem cover_segsOf (vs : List Plane) :
    cover (segsOf vs) = poly vs ∨ (segsOf vs = [] ∧ (poly vs).Subsingleton) := by
  classical
  induction vs with
  | nil => exact Or.inr ⟨rfl, by simp⟩
  | cons u tl ih =>
    match tl, ih with
    | [], _ => exact Or.inr ⟨rfl, by simp [Set.Subsingleton]⟩
    | v :: rest, ih =>
      rw [segsOf_cons_cons, poly_cons_cons]
      by_cases huv : u = v
      · 
        
        subst huv
        rw [if_pos rfl, segment_same]
        have hmem : u ∈ poly (u :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
        rcases ih with h | ⟨h1, h2⟩
        · exact Or.inl (by rw [h, union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)])
        · refine Or.inr ⟨h1, ?_⟩
          rw [union_eq_self_of_subset_left (singleton_subset_iff.2 hmem)]
          exact h2
      · rw [if_neg huv, cover_cons]
        refine Or.inl ?_
        rcases ih with h | ⟨h1, h2⟩
        · rw [h]; rfl
        · 
          rw [h1, cover_nil, union_empty,
            h2.eq_singleton_of_mem (mem_poly_of_mem (List.mem_cons_self ..)),
            union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ u v))]
          rfl

 

theorem cover_segsOf_eq {vs : List Plane} (ha : a ∈ poly vs) (hb : b ∈ poly vs)
    (hab : a ≠ b) : cover (segsOf vs) = poly vs := by
  rcases cover_segsOf vs with h | ⟨-, h⟩
  · exact h
  · exact absurd (h ha hb) hab

 




 




theorem exists_poly_eq_edgesCover {u v : Plane} {W : List Piece}
    (hW : (overlayGraph pieces points).IsWalk u W v) (hne : W ≠ []) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = u ∧ vs.getLast h = v ∧
      poly vs = Graph.edgesCover segmentDrawing W := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hW ih =>
    
    
    have hedge : Graph.edgeArc segmentDrawing e = segment ℝ u w := by
      rw [edgeArc_segmentDrawing]
      rcases (overlayGraph_isLink.1 hl).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact segment_symm ℝ _ _
    rcases eq_or_ne W [] with rfl | hWne
    · have hwv : w = v := hW.eq_of_nil
      subst hwv
      refine ⟨[u, w], by simp, rfl, by simp, ?_⟩
      rw [poly_pair, Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty, hedge]
    · obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := ih hWne
      refine ⟨u :: vs, by simp, rfl, ?_, ?_⟩
      · rw [List.getLast_cons hvs]; exact hlast
      · rw [poly_cons_of_ne_nil hvs, hhead, hpoly, Graph.edgesCover_cons, hedge]

 




 
theorem overlayGraph_reaches_end {P : Piece} (hP : P ∈ overlayPieces pieces points)
    (hz : x = P.1 ∨ x = P.2) :
    (overlayGraph pieces points).Reaches a P.1 ↔ (overlayGraph pieces points).Reaches a x := by
  have hlink : (overlayGraph pieces points).IsLink P P.1 P.2 :=
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  rcases hz with rfl | rfl
  · exact Iff.rfl
  · exact ⟨fun h => h.trans (Graph.Reaches.of_isLink hlink),
      fun h => h.trans (Graph.Reaches.of_isLink hlink).symm⟩

 

theorem overlayGraph_mem_vertexSet_of_mem_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hxp : x ∈ points) (hx : x ∈ cover pieces) : x ∈ V(overlayGraph pieces points) := by
  rw [← overlayPieces_cover pieces points] at hx
  simp only [cover, mem_iUnion, exists_prop] at hx
  obtain ⟨P, hP, hxP⟩ := hx
  have hint : x ∉ P.interior := overlayPieces_avoids hnd x hxp P hP
  refine ⟨P, hP, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

 







theorem overlayGraph_reaches (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces))
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points)
    (hap : a ∈ points) (hbp : b ∈ points) (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    (overlayGraph pieces points).Reaches a b := by
  classical
  have hdraw : Graph.IsDrawing (overlayGraph pieces points) segmentDrawing :=
    overlayGraph_isDrawing pieces points hnd hEnds hMeets
  have haV : a ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hap ha
  have hbV : b ∈ V(overlayGraph pieces points) :=
    overlayGraph_mem_vertexSet_of_mem_cover hnd hbp hb
  
  
  have hlink : ∀ P ∈ overlayPieces pieces points,
      (overlayGraph pieces points).IsLink P P.1 P.2 := fun P hP =>
    overlayGraph_isLink.2 ⟨hP, Or.inl ⟨rfl, rfl⟩⟩
  
  set S : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      (overlayGraph pieces points).Reaches a P.1}, P.seg with hS
  set T : Set Plane :=
    ⋃ P ∈ {P | P ∈ overlayPieces pieces points ∧
      ¬ (overlayGraph pieces points).Reaches a P.1}, P.seg with hT
  have hSclosed : IsClosed S :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  have hTclosed : IsClosed T :=
    ((Set.Finite.subset (overlayPieces pieces points).finite_toSet
      fun _ hP => hP.1).isCompact_biUnion fun P _ => isCompact_segment P.1 P.2).isClosed
  
  have hunion : ∀ z ∈ cover pieces, z ∈ S ∨ z ∈ T := by
    intro z hz
    rw [← overlayPieces_cover pieces points] at hz
    simp only [cover, mem_iUnion, exists_prop] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    by_cases hr : (overlayGraph pieces points).Reaches a P.1
    · exact Or.inl (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
    · exact Or.inr (mem_biUnion (show P ∈ _ from ⟨hP, hr⟩) hzP)
  
  have hdisj : ∀ z, z ∈ S → z ∈ T → False := by
    intro z hzS hzT
    simp only [hS, hT, mem_iUnion, mem_setOf_eq, exists_prop] at hzS hzT
    obtain ⟨P, ⟨hP, hPr⟩, hzP⟩ := hzS
    obtain ⟨Q, ⟨hQ, hQr⟩, hzQ⟩ := hzT
    have hPQ : P ≠ Q := by rintro rfl; exact hQr hPr
    obtain ⟨-, hincP, hincQ⟩ := hdraw.edge_inter (overlayGraph_mem_edgeSet.2 hP)
      (overlayGraph_mem_edgeSet.2 hQ) hPQ
      (by rwa [edgeArc_segmentDrawing]) (by rwa [edgeArc_segmentDrawing])
    have hzendP : z = P.1 ∨ z = P.2 := hincP.eq_or_eq_of_isLink (hlink P hP)
    have hzendQ : z = Q.1 ∨ z = Q.2 := hincQ.eq_or_eq_of_isLink (hlink Q hQ)
    exact hQr ((overlayGraph_reaches_end hQ hzendQ).2
      ((overlayGraph_reaches_end hP hzendP).1 hPr))
  
  have haS : a ∈ S := by
    obtain ⟨P, hP, hend⟩ := id haV
    refine mem_biUnion (show P ∈ _ from
      ⟨hP, (overlayGraph_reaches_end hP hend).2 (Graph.Reaches.refl haV)⟩) ?_
    rcases hend with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  
  have hbS : b ∈ S := by
    by_contra hbnot
    have hbT : b ∈ T := (hunion b hb).resolve_left hbnot
    have hsub : cover pieces ⊆ Tᶜ ∪ Sᶜ := by
      intro w hw
      rcases hunion w hw with h | h
      · exact Or.inl fun h' => hdisj w h h'
      · exact Or.inr fun h' => hdisj w h' h
    obtain ⟨z, hzc, hzT, hzS⟩ := hconn Tᶜ Sᶜ hTclosed.isOpen_compl hSclosed.isOpen_compl
      hsub ⟨a, ha, fun h => hdisj a haS h⟩ ⟨b, hb, fun h => hdisj b h hbT⟩
    exact (hunion z hzc).elim hzS hzT
  
  simp only [hS, mem_iUnion, mem_setOf_eq, exists_prop] at hbS
  obtain ⟨P, ⟨hP, hPr⟩, hbP⟩ := hbS
  have hbend : b = P.1 ∨ b = P.2 :=
    hdraw.vertex_mem_edgeArc (hlink P hP) hbV (by rwa [edgeArc_segmentDrawing])
  exact (overlayGraph_reaches_end hP hbend).1 hPr

 

 





theorem exists_simple_poly_of_cover (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hconn : IsPreconnected (cover pieces)) (hab : a ≠ b)
    (ha : a ∈ cover pieces) (hb : b ∈ cover pieces) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = a ∧ vs.getLast h = b ∧
      poly vs ⊆ cover pieces ∧ IsArcBetween (poly vs) a b := by
  classical
  
  
  obtain ⟨pts₀, hEnds₀, hMeets₀⟩ := exists_cut_points pieces
  set pts : List Plane := a :: b :: pts₀ with hpts
  have hEnds : EndsAreCut pieces pts := fun P hP z hz => by
    simp [hpts, hEnds₀ P hP z hz]
  have hMeets : MeetsAreCut pieces pts := by
    intro P hP Q hQ hPQ hne
    obtain ⟨u, v, huv, hu, hv⟩ := hMeets₀ P hP Q hQ hPQ hne
    exact ⟨u, v, huv, by simp [hpts, hu], by simp [hpts, hv]⟩
  have hdraw : Graph.IsDrawing (overlayGraph pieces pts) segmentDrawing :=
    overlayGraph_isDrawing pieces pts hnd hEnds hMeets
  
  have hreach : (overlayGraph pieces pts).Reaches a b :=
    overlayGraph_reaches hnd hconn hEnds hMeets (by simp [hpts]) (by simp [hpts]) ha hb
  obtain ⟨W, hpath⟩ := hreach.exists_isPath
  have hWne : W ≠ [] := by
    rintro rfl
    exact hab hpath.isWalk.eq_of_nil
  
  have harc : IsArcBetween (Graph.edgesCover segmentDrawing W) a b :=
    hdraw.path_isArcBetween hpath hWne
  obtain ⟨vs, hvs, hhead, hlast, hpoly⟩ := exists_poly_eq_edgesCover hpath.isWalk hWne
  refine ⟨vs, hvs, hhead, hlast, ?_, ?_⟩
  · rw [hpoly, ← overlayGraph_pointSet pieces pts]
    exact Graph.edgesCover_subset_pointSet fun e he => hpath.edge_mem he
  · rw [hpoly]; exact harc

 
theorem exists_simple_poly_of_poly {vs : List Plane} (hconn : IsPreconnected (poly vs))
    (hab : a ≠ b) (ha : a ∈ poly vs) (hb : b ∈ poly vs) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ poly vs ∧ IsArcBetween (poly ws) a b := by
  have hcov : cover (segsOf vs) = poly vs := cover_segsOf_eq ha hb hab
  have := exists_simple_poly_of_cover (segsOf_nondeg vs) (hcov ▸ hconn) hab
    (hcov ▸ ha) (hcov ▸ hb)
  rwa [hcov] at this

 
theorem exists_simple_poly_of_isPolygonal {A : Set Plane} (hA : IsPolygonal A)
    (hconn : IsPreconnected A) (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ A) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ A ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨vs, rfl⟩ := hA
  exact exists_simple_poly_of_poly hconn hab ha hb

 







 
theorem biUnion_list_cons {α : Type*} (f : α → Set Plane) (x : α) (l : List α) :
    (⋃ y ∈ x :: l, f y) = f x ∪ ⋃ y ∈ l, f y := by
  ext z
  simp only [mem_iUnion, exists_prop, List.mem_cons, mem_union]
  constructor
  · rintro ⟨y, rfl | hy, hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨y, hy, hz⟩
  · rintro (hz | ⟨y, hy, hz⟩)
    · exact ⟨x, Or.inl rfl, hz⟩
    · exact ⟨y, Or.inr hy, hz⟩

 


theorem cover_flatMap_list {α : Type*} (f : α → List Piece) (l : List α) :
    cover (l.flatMap f) = ⋃ x ∈ l, cover (f x) := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.flatMap_cons, cover_append, ih, biUnion_list_cons]

 


theorem subset_of_finite_diff {U C : Set Plane} (hU : IsPreconnected U) (hC : IsClosed C)
    (hfin : (U \ C).Finite) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) : U ⊆ C := by
  intro z hz
  by_contra hzC
  
  set D : Set Plane := C ∪ ((U \ C) \ {z}) with hD
  have hDclosed : IsClosed D := hC.union ((hfin.subset Set.sdiff_subset).isClosed)
  have hzD : z ∉ D := fun h => h.elim hzC fun h' => h'.2 rfl
  have hmemD : ∀ w ∈ U, w ≠ z → w ∈ D := fun w hw hwz =>
    (em (w ∈ C)).elim Or.inl fun h => Or.inr ⟨⟨hw, h⟩, hwz⟩
  
  obtain ⟨w, hwU, hwD, hwz⟩ := hU Dᶜ ({z} : Set Plane)ᶜ hDclosed.isOpen_compl
    isClosed_singleton.isOpen_compl
    (fun w hw => (em (w = z)).elim (fun h => Or.inl (h ▸ hzD)) fun h => Or.inr h)
    ⟨z, hz, hzD⟩
    ((em (a = z)).elim (fun h => ⟨b, hb, fun hbz => hab (h.trans (mem_singleton_iff.1 hbz).symm)⟩)
      fun h => ⟨a, ha, h⟩)
  exact hwD (hmemD w hwU hwz)

 

theorem exists_simple_poly_of_biUnion {L : List (List Plane)}
    (hconn : IsPreconnected (⋃ vs ∈ L, poly vs)) (hab : a ≠ b)
    (ha : a ∈ ⋃ vs ∈ L, poly vs) (hb : b ∈ ⋃ vs ∈ L, poly vs) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ vs ∈ L, poly vs) ∧ IsArcBetween (poly ws) a b := by
  classical
  have hnd : ∀ P ∈ L.flatMap segsOf, P.Nondeg := by
    intro P hP
    obtain ⟨vs, -, hPvs⟩ := List.mem_flatMap.1 hP
    exact segsOf_nondeg vs P hPvs
  have hcovsub : ∀ vs : List Plane, cover (segsOf vs) ⊆ poly vs := by
    intro vs
    rcases cover_segsOf vs with h | ⟨h, -⟩
    · exact h.subset
    · rw [h, cover_nil]; exact empty_subset _
  have hflat : cover (L.flatMap segsOf) = ⋃ vs ∈ L, cover (segsOf vs) :=
    cover_flatMap_list segsOf L
  have hsub : cover (L.flatMap segsOf) ⊆ ⋃ vs ∈ L, poly vs := by
    rw [hflat]
    exact iUnion₂_mono fun vs _ => hcovsub vs
  
  have hdiff : ((⋃ vs ∈ L, poly vs) \ cover (L.flatMap segsOf)).Finite := by
    have hsmall : ∀ vs : List Plane, (poly vs \ cover (segsOf vs)).Subsingleton := by
      intro vs
      rcases cover_segsOf vs with h | ⟨-, h⟩
      · rw [h]; simp
      · exact h.anti Set.sdiff_subset
    refine (Set.Finite.biUnion L.finite_toSet
      fun vs _ => (hsmall vs).finite).subset ?_
    rintro z ⟨hzU, hzC⟩
    simp only [mem_iUnion, exists_prop] at hzU
    obtain ⟨vs, hvs, hz⟩ := hzU
    refine mem_biUnion hvs ⟨hz, fun hmem => hzC ?_⟩
    rw [hflat]
    exact mem_biUnion hvs hmem
  have hclosed : IsClosed (cover (L.flatMap segsOf)) :=
    Set.Finite.isClosed_biUnion (L.flatMap segsOf).finite_toSet fun P _ =>
      (isCompact_segment P.1 P.2).isClosed
  have heq : cover (L.flatMap segsOf) = ⋃ vs ∈ L, poly vs :=
    subset_antisymm hsub (subset_of_finite_diff hconn hclosed hdiff ha hb hab)
  have := exists_simple_poly_of_cover hnd (heq ▸ hconn) hab (heq ▸ ha) (heq ▸ hb)
  rwa [heq] at this

 
theorem exists_lists_of_isPolygonal : ∀ {L : List (Set Plane)}, (∀ A ∈ L, IsPolygonal A) →
    ∃ M : List (List Plane), (⋃ vs ∈ M, poly vs) = ⋃ A ∈ L, A
  | [], _ => ⟨[], by simp⟩
  | A :: L, h => by
    obtain ⟨vs, rfl⟩ := h A (List.mem_cons_self ..)
    obtain ⟨M, hM⟩ := exists_lists_of_isPolygonal fun B hB => h B (List.mem_cons_of_mem _ hB)
    refine ⟨vs :: M, ?_⟩
    rw [biUnion_list_cons (fun ws : List Plane => poly ws),
      biUnion_list_cons (fun B : Set Plane => B), hM]

 


theorem exists_simple_poly_of_union {L : List (Set Plane)} (hL : ∀ A ∈ L, IsPolygonal A)
    (hconn : IsPreconnected (⋃ A ∈ L, A)) (hab : a ≠ b)
    (ha : a ∈ ⋃ A ∈ L, A) (hb : b ∈ ⋃ A ∈ L, A) :
    ∃ ws : List Plane, ∃ h : ws ≠ [], ws.head h = a ∧ ws.getLast h = b ∧
      poly ws ⊆ (⋃ A ∈ L, A) ∧ IsArcBetween (poly ws) a b := by
  obtain ⟨M, hM⟩ := exists_lists_of_isPolygonal hL
  have := exists_simple_poly_of_biUnion (L := M) (hM ▸ hconn) hab (hM ▸ ha) (hM ▸ hb)
  rwa [hM] at this

 




theorem exists_simple_poly_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = x ∧ vs.getLast h = y ∧
      poly vs ⊆ Ω ∧ IsArcBetween (poly vs) x y := by
  obtain ⟨us, hus, hsub, hhead, hlast⟩ := exists_poly_of_isPreconnected hΩ hconn hx hy
  have hxu : x ∈ poly us := hhead ▸ head_mem_poly hus
  have hyu : y ∈ poly us := hlast ▸ getLast_mem_poly hus
  obtain ⟨vs, hvs, h1, h2, h3, h4⟩ :=
    exists_simple_poly_of_poly (isConnected_poly hus).2 hxy hxu hyu
  exact ⟨vs, hvs, h1, h2, h3.trans hsub, h4⟩

 

theorem exists_simple_arc_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ A ⊆ Ω, IsPolygonal A ∧ IsArcBetween A x y := by
  obtain ⟨vs, -, -, -, hsub, harc⟩ := exists_simple_poly_of_isPreconnected hΩ hconn hx hy hxy
  exact ⟨poly vs, hsub, ⟨vs, rfl⟩, harc⟩

end Schoenflies
