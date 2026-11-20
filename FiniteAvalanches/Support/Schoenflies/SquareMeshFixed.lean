/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/SquareMeshFixed.lean.
-/
import FiniteAvalanches.Support.Schoenflies.SquareMeshConnected
import FiniteAvalanches.Support.Schoenflies.Graph.Ear

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 









































































































open Metric Set
open scoped Graph

namespace Schoenflies

 





theorem pieceListGraph_inc_iff {l : List Piece} {P : Piece} {v : Plane} :
    (pieceListGraph l).Inc P v ↔ P ∈ l ∧ (v = P.1 ∨ v = P.2) := by
  constructor
  · rintro ⟨y, hP, h⟩
    exact ⟨hP, by tauto⟩
  · rintro ⟨hP, h⟩
    exact pieceListGraph_inc hP h

theorem endSet_pair (a q b : Plane) : endSet [((a, q) : Piece), (q, b)] = {a, q, b} := by
  ext x
  simp only [endSet, mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro ⟨P, hP, hx⟩
    rcases hP with rfl | rfl <;> simp only [] at hx <;> tauto
  · intro hx
    rcases hx with hx | hx | hx
    exacts [⟨(a, q), Or.inl rfl, Or.inl hx⟩, ⟨(a, q), Or.inl rfl, Or.inr hx⟩,
      ⟨(q, b), Or.inr rfl, Or.inr hx⟩]

theorem coveredVertices_pair (a q b : Plane) :
    (pieceListGraph [((a, q) : Piece), (q, b)]).coveredVertices [((a, q) : Piece), (q, b)]
      = {a, q, b} := by
  ext x
  simp only [Graph.mem_coveredVertices_iff, List.mem_cons, List.not_mem_nil, or_false,
    mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨e, he, hinc⟩
    obtain ⟨-, hx⟩ := pieceListGraph_inc_iff.1 hinc
    rcases he with rfl | rfl <;> simp only [] at hx <;> tauto
  · intro hx
    have h₁ : ((a, q) : Piece) ∈ [((a, q) : Piece), (q, b)] := by simp
    have h₂ : ((q, b) : Piece) ∈ [((a, q) : Piece), (q, b)] := by simp
    rcases hx with hx | hx | hx
    exacts [⟨(a, q), Or.inl rfl, pieceListGraph_inc h₁ (Or.inl hx)⟩,
      ⟨(a, q), Or.inl rfl, pieceListGraph_inc h₁ (Or.inr hx)⟩,
      ⟨(q, b), Or.inr rfl, pieceListGraph_inc h₂ (Or.inr hx)⟩]

 
theorem isPathGraph_pair {a q b : Plane} (haq : a ≠ q) (hqb : q ≠ b) (hab : a ≠ b) :
    (pieceListGraph [(a, q), (q, b)]).IsPathGraph a [(a, q), (q, b)] b := by
  have h₁ : ((a, q) : Piece) ∈ [((a, q) : Piece), (q, b)] := by simp
  have h₂ : ((q, b) : Piece) ∈ [((a, q) : Piece), (q, b)] := by simp
  have hlink₁ := pieceListGraph_isLink_self h₁
  have hlink₂ := pieceListGraph_isLink_self h₂
  
  have hcov : (pieceListGraph [((a, q) : Piece), (q, b)]).coveredVertices [((q, b) : Piece)]
      = {q, b} := by
    ext x
    simp only [Graph.mem_coveredVertices_iff, List.mem_singleton, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨e, rfl, hinc⟩
      obtain ⟨-, hx⟩ := pieceListGraph_inc_iff.1 hinc
      simpa only [] using hx
    · intro hx
      rcases hx with hx | hx
      exacts [⟨(q, b), rfl, pieceListGraph_inc h₂ (Or.inl hx)⟩,
        ⟨(q, b), rfl, pieceListGraph_inc h₂ (Or.inr hx)⟩]
  have hpath : (pieceListGraph [((a, q) : Piece), (q, b)]).IsPath a [(a, q), (q, b)] b := by
    refine Graph.IsPath.cons hlink₁ (Graph.IsPath.single hlink₂ hqb) ?_
    rw [Graph.walkVertices, hcov]
    simp only [mem_insert_iff, mem_singleton_iff]
    push Not
    exact ⟨haq, haq, hab⟩
  refine ⟨hpath, rfl, ?_⟩
  rw [pieceListGraph_vertexSet, endSet_pair, Graph.walkVertices, coveredVertices_pair]
  simp

 







 




def CleanCut (l : List Piece) (q : Plane) : Prop :=
  (∀ R ∈ l, ∀ S ∈ l, q ∈ R.interior → q ∈ S.interior → R = S) ∧
    ((∀ R ∈ l, q ∉ R.interior) ∨ q ∉ endSet l)

theorem CleanCut.of_no_interior {l : List Piece} {q : Plane} (h : ∀ R ∈ l, q ∉ R.interior) :
    CleanCut l q :=
  ⟨fun R hR _ _ hq _ => absurd hq (h R hR), Or.inl h⟩

 


theorem openSegment_halves_disjoint {a b p x : Plane} (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) (h₁ : x ∈ openSegment ℝ a p) (h₂ : x ∈ openSegment ℝ p b) :
    False := by
  have hpseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ _ _ hp
  have hap : a ≠ p := by
    rintro rfl
    exact hab (left_mem_openSegment_iff.1 hp)
  have hpb : p ≠ b := by
    rintro rfl
    exact hab (right_mem_openSegment_iff.1 hp)
  have hle : dist a p ≤ dist a b :=
    (dist_le_of_mem_segment hab (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
      (by simp) hpseg).2
  have hlt₁ := dist_lt_of_mem_openSegment hab (left_mem_segment ℝ a b) hpseg hap (by simp) h₁
  have hlt₂ :=
    dist_lt_of_mem_openSegment hab hpseg (right_mem_segment ℝ a b) hpb hle h₂
  linarith [hlt₁.2, hlt₂.1]

 
theorem splitAllAt_eq_self {l : List Piece} {q : Plane} (h : ∀ R ∈ l, q ∉ R.interior) :
    splitAllAt q l = l := by
  induction l with
  | nil => rfl
  | cons R l ih =>
    rw [splitAllAt, List.flatMap_cons, splitAt, if_neg (h R (List.mem_cons_self ..))]
    rw [show l.flatMap (splitAt q) = splitAllAt q l from rfl,
      ih fun S hS => h S (List.mem_cons_of_mem _ hS)]
    rfl

 

theorem mem_splitAllAt_iff {l : List Piece} {P R : Piece} {q : Plane} (hP : P ∈ l)
    (hq : q ∈ P.interior) (huniq : ∀ S ∈ l, q ∈ S.interior → S = P) :
    R ∈ splitAllAt q l ↔ (R ∈ l ∧ R ≠ P) ∨ R ∈ [((P.1, q) : Piece), (q, P.2)] := by
  classical
  constructor
  · intro hR
    obtain ⟨S, hS, hRS⟩ := List.mem_flatMap.1 hR
    by_cases hqS : q ∈ S.interior
    · obtain rfl := huniq S hS hqS
      rw [splitAt, if_pos hqS] at hRS
      exact Or.inr hRS
    · rw [splitAt, if_neg hqS] at hRS
      obtain rfl : R = S := List.mem_singleton.1 hRS
      exact Or.inl ⟨hS, fun h => hqS (h ▸ hq)⟩
  · rintro (⟨hR, hRP⟩ | hR)
    · have hqR : q ∉ R.interior := fun h => hRP (huniq R hR h)
      exact List.mem_flatMap.2 ⟨R, hR, by rw [splitAt, if_neg hqR]; simp⟩
    · exact List.mem_flatMap.2 ⟨P, hP, by rw [splitAt, if_pos hq]; exact hR⟩

 
theorem endSet_splitAllAt {l : List Piece} {P : Piece} {q : Plane} (hP : P ∈ l)
    (hq : q ∈ P.interior) (huniq : ∀ S ∈ l, q ∈ S.interior → S = P) :
    endSet (splitAllAt q l) = endSet l ∪ {q} := by
  ext v
  simp only [endSet, mem_setOf_eq, mem_union, mem_singleton_iff]
  constructor
  · rintro ⟨R, hR, hv⟩
    rcases (mem_splitAllAt_iff hP hq huniq).1 hR with ⟨hRl, -⟩ | hR2
    · exact Or.inl ⟨R, hRl, hv⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR2
      rcases hR2 with rfl | rfl <;> rcases hv with rfl | rfl
      exacts [Or.inl ⟨P, hP, Or.inl rfl⟩, Or.inr rfl, Or.inr rfl, Or.inl ⟨P, hP, Or.inr rfl⟩]
  · have hleft : ((P.1, q) : Piece) ∈ splitAllAt q l :=
      (mem_splitAllAt_iff hP hq huniq).2 (Or.inr (by simp))
    have hright : ((q, P.2) : Piece) ∈ splitAllAt q l :=
      (mem_splitAllAt_iff hP hq huniq).2 (Or.inr (by simp))
    rintro (⟨R, hR, hv⟩ | hvq)
    · by_cases hRP : R = P
      · subst hRP
        rcases hv with rfl | rfl
        exacts [⟨(R.1, q), hleft, Or.inl rfl⟩, ⟨(q, R.2), hright, Or.inr rfl⟩]
      · exact ⟨R, (mem_splitAllAt_iff hP hq huniq).2 (Or.inl ⟨hR, hRP⟩), hv⟩
    · exact ⟨(P.1, q), hleft, Or.inr hvq⟩

 
theorem pieceListGraph_splitAllAt_eq {l : List Piece} {P : Piece} {q : Plane} (hP : P ∈ l)
    (hq : q ∈ P.interior) (huniq : ∀ S ∈ l, q ∈ S.interior → S = P) :
    pieceListGraph (splitAllAt q l)
      = ((pieceListGraph l).deleteEdges {P}).union (pieceListGraph [(P.1, q), (q, P.2)]) := by
  have hVsplit : endSet (splitAllAt q l) = endSet l ∪ {q} := endSet_splitAllAt hP hq huniq
  have hqmem : q ∈ endSet (splitAllAt q l) := by rw [hVsplit]; exact Or.inr rfl
  refine (Graph.eq_of_le_of_subset_subset (Graph.union_le ?_ ?_) ?_ ?_).symm
  · 
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [Graph.vertexSet_deleteEdges, pieceListGraph_vertexSet] at hv
      rw [pieceListGraph_vertexSet, hVsplit]
      exact mem_union_left _ hv
    · intro R x y hlink
      obtain ⟨⟨hRl, hends⟩, hRP⟩ :
          ((R ∈ l ∧ ((x = R.1 ∧ y = R.2) ∨ (x = R.2 ∧ y = R.1))) ∧ R ∉ ({P} : Set Piece)) := hlink
      exact ⟨(mem_splitAllAt_iff hP hq huniq).2
        (Or.inl ⟨hRl, by simpa using hRP⟩), hends⟩
  · exact pieceListGraph_mono fun R hR => (mem_splitAllAt_iff hP hq huniq).2 (Or.inr hR)
  · intro v hv
    rw [pieceListGraph_vertexSet, hVsplit] at hv
    rw [Graph.vertexSet_union, Graph.vertexSet_deleteEdges, pieceListGraph_vertexSet,
      pieceListGraph_vertexSet]
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr ⟨(P.1, q), by simp, Or.inr hv⟩
  · intro R hR
    rw [pieceListGraph_mem_edgeSet] at hR
    rcases (mem_splitAllAt_iff hP hq huniq).1 hR with ⟨hRl, hRP⟩ | hR2
    · exact Or.inl (Graph.mem_edgeSet_deleteEdges_iff.2 ⟨hRl, by simpa using hRP⟩)
    · exact Or.inr hR2

 


theorem pieceListGraph_splitAllAt_isTwoConnected {l : List Piece} {P : Piece} {q : Plane}
    (hP : P ∈ l) (hnd : P.Nondeg) (hq : q ∈ P.interior)
    (huniq : ∀ S ∈ l, q ∈ S.interior → S = P) (hnew : q ∉ endSet l)
    (h2 : (pieceListGraph l).IsTwoConnected) :
    (pieceListGraph (splitAllAt q l)).IsTwoConnected := by
  have h1q : P.1 ≠ q := by
    intro h
    rw [← h] at hq
    exact hnd (left_mem_openSegment_iff.1 hq)
  have hq2 : q ≠ P.2 := by
    intro h
    rw [h] at hq
    exact hnd (right_mem_openSegment_iff.1 hq)
  rw [pieceListGraph_splitAllAt_eq hP hq huniq]
  refine h2.replace_edge_by_path (pieceListGraph_isLink_self hP) hnd ?_
    (isPathGraph_pair h1q hq2 hnd) ?_
  · 
    intro R hR hR' x y
    exfalso
    simp only [pieceListGraph_mem_edgeSet, List.mem_cons, List.not_mem_nil, or_false] at hR'
    rw [Graph.mem_edgeSet_deleteEdges_iff, pieceListGraph_mem_edgeSet] at hR
    rcases hR' with rfl | rfl
    exacts [hnew ⟨_, hR.1, Or.inr rfl⟩, hnew ⟨_, hR.1, Or.inl rfl⟩]
  · rintro x ⟨R, hR, hx⟩ hx1 hx2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl <;> rcases hx with rfl | rfl
    exacts [absurd rfl hx1, hnew, hnew, absurd rfl hx2]

 

theorem CleanCut.splitAllAt {l : List Piece} {q q' : Plane} (hnd : ∀ R ∈ l, R.Nondeg)
    (hq : CleanCut l q) (hq' : CleanCut l q') : CleanCut (splitAllAt q' l) q := by
  classical
  by_cases hsame : q = q'
  · subst hsame
    exact CleanCut.of_no_interior (Schoenflies.splitAllAt_avoids q hnd)
  refine ⟨?_, ?_⟩
  · 
    intro R hR S hS hqR hqS
    obtain ⟨R₀, hR₀, hRR₀⟩ := List.mem_flatMap.1 hR
    obtain ⟨S₀, hS₀, hSS₀⟩ := List.mem_flatMap.1 hS
    obtain rfl : R₀ = S₀ :=
      hq.1 R₀ hR₀ S₀ hS₀ (splitAt_interior_subset q' R₀ R hRR₀ hqR)
        (splitAt_interior_subset q' S₀ S hSS₀ hqS)
    
    by_cases hq'R : q' ∈ R₀.interior
    · rw [splitAt, if_pos hq'R] at hRR₀ hSS₀
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRR₀ hSS₀
      have hnd₀ : R₀.Nondeg := hnd R₀ hR₀
      rcases hRR₀ with rfl | rfl <;> rcases hSS₀ with rfl | rfl
      · rfl
      · exact absurd (openSegment_halves_disjoint hnd₀ hq'R hqR hqS) not_false
      · exact absurd (openSegment_halves_disjoint hnd₀ hq'R hqS hqR) not_false
      · rfl
    · rw [splitAt, if_neg hq'R] at hRR₀ hSS₀
      rw [List.mem_singleton.1 hRR₀, List.mem_singleton.1 hSS₀]
  · rcases hq.2 with hnone | hend
    · exact Or.inl fun R hR => by
        obtain ⟨R₀, hR₀, hRR₀⟩ := List.mem_flatMap.1 hR
        exact fun hmem => hnone R₀ hR₀ (splitAt_interior_subset q' R₀ R hRR₀ hmem)
    · refine Or.inr fun hmem => ?_
      obtain ⟨R, hR, hv⟩ := hmem
      obtain ⟨R₀, hR₀, hRR₀⟩ := List.mem_flatMap.1 hR
      rcases splitAt_ends q' R₀ R hRR₀ q hv with h | h
      exacts [hsame h, hend ⟨R₀, hR₀, h⟩]

 





theorem pieceListGraph_subdivide_isTwoConnected : ∀ (points : List Plane) (l : List Piece),
    (∀ P ∈ l, P.Nondeg) → (∀ q ∈ points, CleanCut l q) →
      (pieceListGraph l).IsTwoConnected →
      (pieceListGraph (subdivide l points)).IsTwoConnected := by
  classical
  intro points
  induction points with
  | nil => exact fun l _ _ h2 => h2
  | cons q qs ih =>
    intro l hnd hclean h2
    rw [subdivide_cons]
    refine ih (splitAllAt q l) (splitAllAt_ne q hnd) ?_ ?_
    · exact fun q' hq' => (hclean q' (List.mem_cons_of_mem _ hq')).splitAllAt hnd
        (hclean q (List.mem_cons_self ..))
    · obtain ⟨huniq, hor⟩ := hclean q (List.mem_cons_self ..)
      rcases hor with hnone | hend
      · rw [splitAllAt_eq_self hnone]; exact h2
      · by_cases hex : ∃ P ∈ l, q ∈ P.interior
        · obtain ⟨P, hP, hqP⟩ := hex
          exact pieceListGraph_splitAllAt_isTwoConnected hP (hnd P hP) hqP
            (fun S hS hqS => huniq S hS P hP hqS hqP) hend h2
        · push Not at hex
          rw [splitAllAt_eq_self hex]; exact h2

 







 
theorem notMem_interior_of_end {R : Piece} (hnd : R.Nondeg) {q : Plane} (h : q = R.1 ∨ q = R.2) :
    q ∉ R.interior := by
  rcases h with rfl | rfl
  · exact fun hmem => hnd (left_mem_openSegment_iff.1 hmem)
  · exact fun hmem => hnd (right_mem_openSegment_iff.1 hmem)

variable {xc yc : ℕ → ℝ} {m n : ℕ}

 
theorem cleanCut_gridEdges (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) (q : Plane) :
    CleanCut (gridEdges xc yc m n) q := by
  have hnd : ∀ P ∈ gridEdges xc yc m n, P.Nondeg :=
    fun P hP => gridEdges_nondeg hxs hys hm hn hP
  
  have hgrid : ∀ R ∈ gridEdges xc yc m n, q ∈ R.interior →
      ∀ a ≤ m, ∀ b ≤ n, q ≠ gridPt xc yc a b := by
    intro R hR hqR a ha b hb hab
    refine notMem_interior_of_end (hnd R hR) ?_ hqR
    rw [hab]
    exact end_of_gridPt_mem_seg hxs hys hm hn hR ha hb
      (hab ▸ openSegment_subset_segment ℝ _ _ hqR)
  refine ⟨fun R hR S hS hqR hqS => ?_, ?_⟩
  · by_contra hRS
    obtain ⟨a, ha, b, hb, hq⟩ := gridPt_of_mem_two_edges hxs hys hm hn hR hS hRS
      (openSegment_subset_segment ℝ _ _ hqR) (openSegment_subset_segment ℝ _ _ hqS)
    exact hgrid R hR hqR a ha b hb hq
  · by_cases hq : q ∈ endSet (gridEdges xc yc m n)
    · refine Or.inl fun R hR hqR => ?_
      obtain ⟨a, ha, b, hb, hab⟩ := (mem_vertexSet_gridGraph_iff hm hn).1 hq
      exact hgrid R hR hqR a ha b hb hab
    · exact Or.inr hq

 



theorem gridGraph_subdivide_isTwoConnected (hxs : StrictMonoOn xc (Set.Iic m))
    (hys : StrictMonoOn yc (Set.Iic n)) (hm : 1 ≤ m) (hn : 1 ≤ n) (points : List Plane) :
    (pieceListGraph (subdivide (gridEdges xc yc m n) points)).IsTwoConnected := by
  refine pieceListGraph_subdivide_isTwoConnected points _
    (fun P hP => gridEdges_nondeg hxs hys hm hn hP)
    (fun q _ => cleanCut_gridEdges hxs hys hm hn q) ?_
  exact gridGraph_isTwoConnected hm hn
    (fun i hi => ne_of_lt (hxs (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)))
    (fun j hj => ne_of_lt (hys (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)))

 





 


theorem edgesCover_gridBoundary_ringSet {r : ℝ} (hr : 0 ≤ r) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hxmono : ∀ i, i < m → xc i ≤ xc (i + 1)) (hymono : ∀ j, j < n → yc j ≤ yc (j + 1))
    (hx0 : xc 0 = -r) (hxm : xc m = r) (hy0 : yc 0 = -r) (hyn : yc n = r) :
    Graph.edgesCover segmentDrawing
        (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n) = ringSet r := by
  rw [edgesCover_gridBoundary hm hn hxmono hymono, ← cover_ringPieces hr]
  simp only [ringPieces, cover_cons, cover_nil, Set.union_empty, Piece.seg, gridPt, hx0, hxm,
    hy0, hyn]
  rw [segment_symm ℝ (Plane.mk r r) (Plane.mk (-r) r),
    segment_symm ℝ (Plane.mk (-r) r) (Plane.mk (-r) (-r))]
  ext z
  simp only [Set.mem_union]
  tauto

 



theorem gridGraph_inner_cycle {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≠ 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hxs : StrictMonoOn xc (Set.Iic m)) (hys : StrictMonoOn yc (Set.Iic n))
    (hx0 : xc 0 = -r) (hxm : xc m = r) (hy0 : yc 0 = -r) (hyn : yc n = r) :
    (gridGraph xc yc m n).IsCycleThrough (gridBoundaryLast xc yc m n)
        (gridBoundaryPt xc yc m n 0) (gridBoundaryPt xc yc m n (2 * m + 2 * n - 1))
        (gridBoundaryDetour xc yc m n) ∧
      Graph.edgesCover segmentDrawing
          (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n) = ringSet r ∧
      Graph.edgesCover segmentDrawing
          (gridBoundaryLast xc yc m n :: gridBoundaryDetour xc yc m n) ∩ modelCurve = ∅ := by
  have hcov := edgesCover_gridBoundary_ringSet (xc := xc) (yc := yc) hr hm hn
    (fun i hi => (coord_le_of_idx_le hxs (by omega) (by omega) (by omega)))
    (fun j hj => (coord_le_of_idx_le hys (by omega) (by omega) (by omega))) hx0 hxm hy0 hyn
  exact ⟨gridGraph_isCycleThrough_boundary hm hn hxs.injOn hys.injOn, hcov,
    by rw [hcov]; exact ringSet_disjoint_modelCurve hr1⟩

 



theorem mem_modelCurve_of_supNorm {z : Plane} (h : Plane.supNorm z = 1) : z ∈ modelCurve := h

theorem supNorm_mk (a b : ℝ) : Plane.supNorm (Plane.mk a b) = max |a| |b| := rfl

 

theorem gridVEdge_not_subset_modelCurve {i j : ℕ} (hxi : |xc i| < 1) (h1 : -1 ≤ yc j)
    (h2 : yc (j + 1) ≤ 1) (hlt : yc j < yc (j + 1)) :
    ¬ (gridVEdge xc yc i j).seg ⊆ modelCurve := by
  intro hsub
  set t : ℝ := (yc j + yc (j + 1)) / 2 with ht
  have hmem : Plane.mk (xc i) t ∈ (gridVEdge xc yc i j).seg := by
    refine mem_gridVEdge_seg_iff.2 ⟨Plane.mk_zero _ _, ?_⟩
    rw [Plane.mk_one, segment_eq_Icc hlt.le]
    constructor <;> (rw [ht]; linarith)
  have hone : Plane.supNorm (Plane.mk (xc i) t) = 1 := hsub hmem
  rw [supNorm_mk] at hone
  have habs : |t| < 1 := by
    rw [abs_lt]
    constructor <;> (rw [ht]; linarith)
  rcases max_cases |xc i| |t| with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hone <;> linarith

 














theorem gridGraph_full_square_aligned_ends (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hxs : StrictMonoOn xc (Set.Iic m)) (hys : StrictMonoOn yc (Set.Iic n))
    (hx0 : xc 0 = -1) (hxm : xc m = 1) (hy0 : yc 0 = -1) (hyn : yc n = 1)
    {i : ℕ} (hi0 : 0 < i) (him : i < m) :
    gridPt xc yc i 0 ∈ modelCurve ∧ gridPt xc yc i n ∈ modelCurve ∧
      gridPt xc yc i 0 0 = gridPt xc yc i n 0 ∧
      (∃ P ∈ E(gridGraph xc yc m n),
        (gridPt xc yc i 0 = P.1 ∨ gridPt xc yc i 0 = P.2) ∧ ¬ P.seg ⊆ modelCurve) ∧
      (∃ P ∈ E(gridGraph xc yc m n),
        (gridPt xc yc i n = P.1 ∨ gridPt xc yc i n = P.2) ∧ ¬ P.seg ⊆ modelCurve) := by
  have hxi_lo : -1 < xc i := by
    rw [← hx0]; exact hxs (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)
  have hxi_hi : xc i < 1 := by
    rw [← hxm]; exact hxs (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)
  have hxi : |xc i| < 1 := abs_lt.2 ⟨hxi_lo, hxi_hi⟩
  have hymono : ∀ a b : ℕ, a ≤ b → b ≤ n → yc a ≤ yc b := fun a b hab hb =>
    coord_le_of_idx_le hys (by omega) (Set.mem_Iic.2 hb) hab
  
  have hbot : gridPt xc yc i 0 ∈ modelCurve := by
    refine mem_modelCurve_of_supNorm ?_
    rw [gridPt, supNorm_mk, hy0]
    simp only [abs_neg, abs_one]
    exact max_eq_right hxi.le
  have htop : gridPt xc yc i n ∈ modelCurve := by
    refine mem_modelCurve_of_supNorm ?_
    rw [gridPt, supNorm_mk, hyn, abs_one]
    exact max_eq_right hxi.le
  refine ⟨hbot, htop, by simp only [gridPt, Plane.mk_zero], ?_, ?_⟩
  · 
    refine ⟨gridVEdge xc yc i 0, gridVEdge_mem_gridEdges (by omega) (by omega) hm,
      Or.inl rfl, ?_⟩
    refine gridVEdge_not_subset_modelCurve hxi (by rw [hy0]) ?_ ?_
    · rw [← hyn]; exact hymono 1 n (by omega) le_rfl
    · exact hys (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)
  · 
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine ⟨gridVEdge xc yc i k, gridVEdge_mem_gridEdges (by omega) (by omega) hm,
      Or.inr rfl, ?_⟩
    refine gridVEdge_not_subset_modelCurve hxi ?_ (by rw [hyn]) ?_
    · rw [← hy0]; exact hymono 0 k (by omega) (by omega)
    · exact hys (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 (by omega)) (by omega)

 


















 
theorem end_mem_vertexSet_meshGraph {N : ℕ} {fresh anchors : List Plane} {R : Piece}
    (hR : R ∈ meshSegments N fresh) {z : Plane} (hz : z = R.1 ∨ z = R.2) :
    z ∈ V(meshGraph N fresh anchors) := by
  obtain ⟨Q, hQ, -, hend⟩ :=
    subdivide_preserves_end (meshPoints N fresh anchors) ⟨R, hR, subset_rfl, hz⟩
  exact ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, (orientPiece_ends Q z).2 hend⟩

 

theorem supNorm_eq_of_isLink_of_fresh_nil {N : ℕ} (hN : 2 ≤ N) {anchors : List Plane}
    {P : Piece} {x y : Plane} (h : (meshGraph N [] anchors).IsLink P x y) :
    Plane.supNorm x = Plane.supNorm y := by
  obtain ⟨R, hR, hsub⟩ := meshGraph_edge_source h.1
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨z, hz, -⟩
  · have hring : P.seg ⊆ ringSet r :=
      hsub.trans (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr)
    have h1 : Plane.supNorm P.1 = r := hring (left_mem_segment ℝ _ _)
    have h2 : Plane.supNorm P.2 = r := hring (right_mem_segment ℝ _ _)
    rcases h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [h1.trans h2.symm, h2.trans h1.symm]
  · exact absurd hz (by simp)

 
theorem not_connected_meshGraph_of_fresh_nil {N : ℕ} (hN : 2 ≤ N) (anchors : List Plane) :
    ¬ (meshGraph N [] anchors).Connected := by
  intro hconn
  have hinv : ∀ {u v : Plane}, (meshGraph N [] anchors).Reaches u v →
      Plane.supNorm u = Plane.supNorm v := by
    rintro u v ⟨W, hW⟩
    induction hW with
    | nil => rfl
    | cons hl _ ih => exact (supNorm_eq_of_isLink_of_fresh_nil hN hl).trans ih
  
  have houter : (Plane.mk 1 1 : Plane) ∈ V(meshGraph N [] anchors) :=
    end_mem_vertexSet_meshGraph (R := (Plane.mk 1 1, Plane.mk (-1) 1))
      (outer_ringPieces_mem hN (by simp [ringPieces])) (Or.inl rfl)
  have hinner : (Plane.mk ((N : ℝ)⁻¹) ((N : ℝ)⁻¹) : Plane) ∈ V(meshGraph N [] anchors) :=
    end_mem_vertexSet_meshGraph
      (R := (Plane.mk ((N : ℝ)⁻¹) ((N : ℝ)⁻¹), Plane.mk (-(N : ℝ)⁻¹) ((N : ℝ)⁻¹)))
      (mem_meshSegments.2 (Or.inl ⟨(N : ℝ)⁻¹, inv_mem_meshRadii hN, by simp [ringPieces]⟩))
      (Or.inl rfl)
  have heq := hinv (hconn.reaches houter hinner)
  rw [supNorm_mk, supNorm_mk, abs_one, max_self, abs_of_nonneg (inv_cast_pos hN).le,
    max_self] at heq
  exact absurd heq.symm (ne_of_lt (inv_cast_lt_one hN))

 


theorem not_isTwoConnected_squareMesh_of_fresh_nil (δ : ℝ) (anchors : List Plane) :
    ¬ (squareMesh δ [] anchors).IsTwoConnected := fun h =>
  not_connected_meshGraph_of_fresh_nil (two_le_meshCount δ) anchors h.connected

end Schoenflies

 




namespace Graph

variable {α β : Type*} {G : Graph α β}

 
theorem IsPath.append_of_disjoint : ∀ {u v : α} {W₁ : List β}, G.IsPath u W₁ v →
    ∀ {w : α} {W₂ : List β}, G.IsPath v W₂ w →
      (∀ x ∈ G.walkVertices u W₁, x ∈ G.walkVertices v W₂ → x = v) →
      G.IsPath u (W₁ ++ W₂) w := by
  intro u v W₁ h₁
  induction h₁ with
  | nil hx => intro w W₂ h₂ _; simpa using h₂
  | @cons u₀ w₀ v₀ e W hl hW hfresh ih =>
    intro w W₂ h₂ hdisj
    refine IsPath.cons hl (ih h₂ fun x hx hx2 =>
      hdisj x (mem_walkVertices_cons_of_mem hl hx) hx2) ?_
    intro hmem
    rw [walkVertices] at hmem
    simp only [List.append_eq, coveredVertices_append, Set.mem_insert_iff,
      Set.mem_union] at hmem
    rcases hmem with hu | hcov
    · exact hfresh (hu ▸ mem_walkVertices_self)
    rcases hcov with hcov | hcov
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · 
      have : u₀ = v₀ :=
        hdisj u₀ mem_walkVertices_self (mem_walkVertices_of_mem_covered hcov)
      exact absurd (IsPath.eq_nil_of_eq (this ▸ IsPath.cons hl hW hfresh)) (by simp)

 

theorem IsPath.cons_cases {u v : α} {e : β} {W : List β} (h : G.IsPath u (e :: W) v) :
    ∃ w, G.IsLink e u w ∧ G.IsPath w W v ∧ u ∉ G.walkVertices w W := by
  cases h with
  | cons hl hW hfresh => exact ⟨_, hl, hW, hfresh⟩

end Graph

namespace Schoenflies

 







 


def SubdividesToPath (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, P.Nondeg → ∃ W : List Piece,
    (overlayGraph pieces points).IsPath P.1 W P.2 ∧
      ∀ Q, Q ∈ W ↔ (Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ P.seg)

 
theorem walkVertices_subset_of_edges {pieces : List Piece} {points : List Plane}
    {A : Set Plane} {u : Plane} {W : List Piece} (hu : u ∈ A) (hW : ∀ Q ∈ W, Q.seg ⊆ A)
    {x : Plane} (hx : x ∈ (overlayGraph pieces points).walkVertices u W) : x ∈ A := by
  rcases Graph.mem_walkVertices_iff.1 hx with rfl | ⟨Q, hQ, hinc⟩
  · exact hu
  · obtain ⟨y, -, hends⟩ := hinc
    rcases hends with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [hW Q hQ (left_mem_segment ℝ _ _), hW Q hQ (right_mem_segment ℝ _ _)]

 
theorem edgesCover_eq_seg {pieces : List Piece} {points : List Plane} {P : Piece}
    (hP : P ∈ pieces) {W : List Piece}
    (hW : ∀ Q, Q ∈ W ↔ (Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ P.seg)) :
    Graph.edgesCover segmentDrawing W = P.seg := by
  refine subset_antisymm ?_ ?_
  · intro z hz
    obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
    rw [edgeArc_segmentDrawing] at hzQ
    exact ((hW Q).1 hQ).2 hzQ
  · intro z hz
    obtain ⟨Q, hQ, hzQ, hsub⟩ := subdivide_covers_source points pieces P hP z hz
    refine Graph.mem_edgesCover ((hW (orientPiece Q)).2
      ⟨mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, by rwa [orientPiece_seg]⟩) ?_
    rw [edgeArc_segmentDrawing, orientPiece_seg]
    exact hzQ

 





 
def sideT : Piece := (Plane.mk 1 1, Plane.mk (-1) 1)

 
def sideL : Piece := (Plane.mk (-1) 1, Plane.mk (-1) (-1))

 
def sideB : Piece := (Plane.mk (-1) (-1), Plane.mk 1 (-1))

 
def sideR : Piece := (Plane.mk 1 (-1), Plane.mk 1 1)

theorem sideT_mem_ringPieces : sideT ∈ ringPieces 1 := by simp [ringPieces, sideT]
theorem sideL_mem_ringPieces : sideL ∈ ringPieces 1 := by simp [ringPieces, sideL]
theorem sideB_mem_ringPieces : sideB ∈ ringPieces 1 := by simp [ringPieces, sideB]
theorem sideR_mem_ringPieces : sideR ∈ ringPieces 1 := by simp [ringPieces, sideR]

theorem mem_sideT {x : Plane} (h : x ∈ sideT.seg) : x 1 = 1 := (mem_segment_horiz.1 h).1
theorem mem_sideB {x : Plane} (h : x ∈ sideB.seg) : x 1 = -1 := (mem_segment_horiz.1 h).1
theorem mem_sideL {x : Plane} (h : x ∈ sideL.seg) : x 0 = -1 := (mem_segment_vert.1 h).1
theorem mem_sideR {x : Plane} (h : x ∈ sideR.seg) : x 0 = 1 := (mem_segment_vert.1 h).1

theorem sideT_inter_sideL {x : Plane} (h : x ∈ sideT.seg) (h' : x ∈ sideL.seg) :
    x = Plane.mk (-1) 1 :=
  plane_eq_of_coords (by rw [mem_sideL h', Plane.mk_zero]) (by rw [mem_sideT h, Plane.mk_one])

theorem sideL_inter_sideB {x : Plane} (h : x ∈ sideL.seg) (h' : x ∈ sideB.seg) :
    x = Plane.mk (-1) (-1) :=
  plane_eq_of_coords (by rw [mem_sideL h, Plane.mk_zero]) (by rw [mem_sideB h', Plane.mk_one])

theorem sideB_inter_sideR {x : Plane} (h : x ∈ sideB.seg) (h' : x ∈ sideR.seg) :
    x = Plane.mk 1 (-1) :=
  plane_eq_of_coords (by rw [mem_sideR h', Plane.mk_zero]) (by rw [mem_sideB h, Plane.mk_one])

theorem sideT_inter_sideR {x : Plane} (h : x ∈ sideT.seg) (h' : x ∈ sideR.seg) :
    x = Plane.mk 1 1 :=
  plane_eq_of_coords (by rw [mem_sideR h', Plane.mk_zero]) (by rw [mem_sideT h, Plane.mk_one])

theorem sideT_disjoint_sideB {x : Plane} (h : x ∈ sideT.seg) (h' : x ∈ sideB.seg) : False := by
  have := (mem_sideT h).symm.trans (mem_sideB h'); norm_num at this

theorem sideL_disjoint_sideR {x : Plane} (h : x ∈ sideL.seg) (h' : x ∈ sideR.seg) : False := by
  have := (mem_sideL h).symm.trans (mem_sideR h'); norm_num at this

 
theorem sides_cover : sideT.seg ∪ sideL.seg ∪ sideB.seg ∪ sideR.seg = modelCurve := by
  rw [← ringSet_one, ← cover_ringPieces zero_le_one]
  simp only [ringPieces, cover_cons, cover_nil, Set.union_empty, sideT, sideL, sideB, sideR]
  ext z
  simp only [Set.mem_union]
  tauto

theorem side_seg_subset_modelCurve {P : Piece}
    (h : P = sideT ∨ P = sideL ∨ P = sideB ∨ P = sideR) : P.seg ⊆ modelCurve := by
  rw [← sides_cover]
  rcases h with rfl | rfl | rfl | rfl
  exacts [fun x hx => Or.inl (Or.inl (Or.inl hx)), fun x hx => Or.inl (Or.inl (Or.inr hx)),
    fun x hx => Or.inl (Or.inr hx), fun x hx => Or.inr hx]

 







 









theorem meshGraph_outer_cycle {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane)
    (hsub : SubdividesToPath (meshSegments N fresh) (meshPoints N fresh anchors)) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (meshGraph N fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve := by
  have hmemT := outer_ringPieces_mem (fresh := fresh) hN sideT_mem_ringPieces
  have hmemL := outer_ringPieces_mem (fresh := fresh) hN sideL_mem_ringPieces
  have hmemB := outer_ringPieces_mem (fresh := fresh) hN sideB_mem_ringPieces
  have hmemR := outer_ringPieces_mem (fresh := fresh) hN sideR_mem_ringPieces
  obtain ⟨WT, hpT, hcT⟩ := hsub _ hmemT (ringPieces_nondeg one_pos _ sideT_mem_ringPieces)
  obtain ⟨WL, hpL, hcL⟩ := hsub _ hmemL (ringPieces_nondeg one_pos _ sideL_mem_ringPieces)
  obtain ⟨WB, hpB, hcB⟩ := hsub _ hmemB (ringPieces_nondeg one_pos _ sideB_mem_ringPieces)
  obtain ⟨WR, hpR, hcR⟩ := hsub _ hmemR (ringPieces_nondeg one_pos _ sideR_mem_ringPieces)
  have hsegT : ∀ Q ∈ WT, Q.seg ⊆ sideT.seg := fun Q hQ => ((hcT Q).1 hQ).2
  have hsegL : ∀ Q ∈ WL, Q.seg ⊆ sideL.seg := fun Q hQ => ((hcL Q).1 hQ).2
  have hsegB : ∀ Q ∈ WB, Q.seg ⊆ sideB.seg := fun Q hQ => ((hcB Q).1 hQ).2
  have hsegR : ∀ Q ∈ WR, Q.seg ⊆ sideR.seg := fun Q hQ => ((hcR Q).1 hQ).2
  
  have hVT : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices sideT.1 WT, x ∈ sideT.seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegT hx
  have hVL : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices sideL.1 WL, x ∈ sideL.seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegL hx
  have hVB : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices sideB.1 WB, x ∈ sideB.seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegB hx
  
  have hp1 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      sideT.1 (WT ++ WL) sideL.2 :=
    hpT.append_of_disjoint hpL fun x hx hx2 => sideT_inter_sideL (hVT x hx) (hVL x hx2)
  have hV1 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      sideT.1 (WT ++ WL), x ∈ sideT.seg ∪ sideL.seg := by
    refine fun x hx => walkVertices_subset_of_edges (Or.inl (left_mem_segment ℝ _ _))
      (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    exacts [(hsegT Q h).trans Set.subset_union_left, (hsegL Q h).trans Set.subset_union_right]
  
  have hp2 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      sideT.1 ((WT ++ WL) ++ WB) sideB.2 := by
    refine hp1.append_of_disjoint hpB fun x hx hx2 => ?_
    rcases hV1 x hx with h | h
    · exact absurd (sideT_disjoint_sideB h (hVB x hx2)) not_false
    · exact sideL_inter_sideB h (hVB x hx2)
  have hV2 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      sideT.1 ((WT ++ WL) ++ WB), x ∈ sideT.seg ∪ sideL.seg ∪ sideB.seg := by
    refine fun x hx => walkVertices_subset_of_edges
      (Or.inl (Or.inl (left_mem_segment ℝ _ _))) (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    · rcases List.mem_append.1 h with h' | h'
      exacts [(hsegT Q h').trans (Set.subset_union_left.trans Set.subset_union_left),
        (hsegL Q h').trans (Set.subset_union_right.trans Set.subset_union_left)]
    · exact (hsegB Q h).trans Set.subset_union_right
  
  have hRne : sideR.1 ≠ sideR.2 := ringPieces_nondeg one_pos _ sideR_mem_ringPieces
  have hWRne : WR ≠ [] := by
    rintro rfl
    exact hRne hpR.isWalk.eq_of_nil
  obtain ⟨eR, L, hL⟩ := List.exists_cons_of_ne_nil
    (show WR.reverse ≠ [] by simpa using hWRne)
  have hpRrev := hpR.reverse
  rw [hL] at hpRrev
  obtain ⟨w, hlink, htail, hfr⟩ := hpRrev.cons_cases
  have heRmem : eR ∈ WR := by
    rw [← List.mem_reverse, hL]; exact List.mem_cons_self ..
  have hLmem : ∀ Q ∈ L, Q ∈ WR := fun Q hQ => by
    rw [← List.mem_reverse, hL]; exact List.mem_cons_of_mem _ hQ
  have hwR : w ∈ sideR.seg := by
    rcases hlink.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [hsegR eR heRmem (right_mem_segment ℝ _ _),
      hsegR eR heRmem (left_mem_segment ℝ _ _)]
  have hVRtail : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices w L, x ∈ sideR.seg := fun x hx =>
    walkVertices_subset_of_edges hwR (fun Q hQ => hsegR Q (hLmem Q hQ)) hx
  have hrevV : (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices sideB.2 L.reverse
      = (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices w L :=
    htail.isWalk.reverse_walkVertices
  
  have hp3 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      sideT.1 (((WT ++ WL) ++ WB) ++ L.reverse) w := by
    refine hp2.append_of_disjoint htail.reverse fun x hx hx2 => ?_
    rw [hrevV] at hx2
    have hxR : x ∈ sideR.seg := hVRtail x hx2
    rcases hV2 x hx with (h | h) | h
    · refine absurd (show sideR.2 ∈ (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices w L from ?_) hfr
      rwa [show sideR.2 = x from (sideT_inter_sideR h hxR).symm]
    · exact absurd (sideL_disjoint_sideR h hxR) not_false
    · exact sideB_inter_sideR h hxR
  
  have hnondegR : eR.Nondeg :=
    meshGraph_edge_nondeg (anchors := anchors) hN hfresh ((hcR eR).1 heRmem).1
  have hnotT : eR ∉ WT := fun hmem => hnondegR (by
    have h1 := sideT_inter_sideR (hsegT eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := sideT_inter_sideR (hsegT eR hmem (right_mem_segment ℝ _ _))
      (hsegR eR heRmem (right_mem_segment ℝ _ _))
    exact h1.trans h2.symm)
  have hnotL : eR ∉ WL := fun hmem =>
    sideL_disjoint_sideR (hsegL eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
  have hnotB : eR ∉ WB := fun hmem => hnondegR (by
    have h1 := sideB_inter_sideR (hsegB eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := sideB_inter_sideR (hsegB eR hmem (right_mem_segment ℝ _ _))
      (hsegR eR heRmem (right_mem_segment ℝ _ _))
    exact h1.trans h2.symm)
  have hnotLrev : eR ∉ L.reverse := by
    have hnodup : (eR :: L).Nodup := hL ▸ hpR.reverse.nodup
    rw [List.mem_reverse]
    exact (List.nodup_cons.1 hnodup).1
  have hnotD : eR ∉ ((WT ++ WL) ++ WB) ++ L.reverse := by
    intro hmem
    rcases List.mem_append.1 hmem with h | h
    · rcases List.mem_append.1 h with h' | h'
      · rcases List.mem_append.1 h' with h'' | h''
        exacts [hnotT h'', hnotL h'']
      · exact hnotB h'
    · exact hnotLrev h
  
  have hmT : sideT.seg ⊆ modelCurve := side_seg_subset_modelCurve (Or.inl rfl)
  have hmL : sideL.seg ⊆ modelCurve := side_seg_subset_modelCurve (Or.inr (Or.inl rfl))
  have hmB : sideB.seg ⊆ modelCurve := side_seg_subset_modelCurve (Or.inr (Or.inr (Or.inl rfl)))
  have hmR : sideR.seg ⊆ modelCurve := side_seg_subset_modelCurve (Or.inr (Or.inr (Or.inr rfl)))
  have hsegsAll : ∀ Q ∈ eR :: (((WT ++ WL) ++ WB) ++ L.reverse), Q.seg ⊆ modelCurve := by
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | h
    · exact (hsegR Q heRmem).trans hmR
    rcases List.mem_append.1 h with h' | h'
    · rcases List.mem_append.1 h' with h'' | h''
      · rcases List.mem_append.1 h'' with h3 | h3
        exacts [(hsegT Q h3).trans hmT, (hsegL Q h3).trans hmL]
      · exact (hsegB Q h'').trans hmB
    · exact (hsegR Q (hLmem Q (List.mem_reverse.1 h'))).trans hmR
  
  have hthird : sideT.2 ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices sideT.1 (((WT ++ WL) ++ WB) ++ L.reverse) :=
    Graph.walkVertices_mono
      (List.Subset.trans (List.subset_append_left _ _)
        (List.Subset.trans (List.subset_append_left _ _) (List.subset_append_left _ _)))
      hpT.isWalk.target_mem_walkVertices
  have hne₁ : sideT.2 ≠ sideT.1 := mk_ne_mk_of_fst (by norm_num)
  have hne₂ : sideT.2 ≠ w := by
    intro h
    have := mem_sideR (h ▸ hwR)
    rw [sideT, Plane.mk_zero] at this
    norm_num at this
  refine ⟨eR, sideT.1, w, sideT.2, ((WT ++ WL) ++ WB) ++ L.reverse,
    ⟨⟨hlink, hp3, hnotD⟩, hthird, hne₁, hne₂⟩, hsegsAll, ?_⟩
  have hcovT : Graph.edgesCover segmentDrawing WT = sideT.seg := edgesCover_eq_seg hmemT hcT
  have hcovL : Graph.edgesCover segmentDrawing WL = sideL.seg := edgesCover_eq_seg hmemL hcL
  have hcovB : Graph.edgesCover segmentDrawing WB = sideB.seg := edgesCover_eq_seg hmemB hcB
  have hcovR : Graph.edgesCover segmentDrawing WR = sideR.seg := edgesCover_eq_seg hmemR hcR
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
    rw [edgeArc_segmentDrawing] at hzQ
    exact hsegsAll Q hQ hzQ
  · rw [← sides_cover] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · rw [← hcovT] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      exact Graph.mem_edgesCover (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hQ)))) hzQ
    · rw [← hcovL] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      exact Graph.mem_edgesCover (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hQ)))) hzQ
    · rw [← hcovB] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      exact Graph.mem_edgesCover (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_right _ hQ))) hzQ
    · rw [← hcovR] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      rw [← List.mem_reverse, hL] at hQ
      rcases List.mem_cons.1 hQ with rfl | hQ'
      · exact Graph.mem_edgesCover List.mem_cons_self hzQ
      · exact Graph.mem_edgesCover (List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_reverse.2 hQ'))) hzQ

 
theorem squareMesh_outer_cycle_of_subdividesToPath {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane)
    (hsub : SubdividesToPath (meshSegments (meshCount δ) fresh)
      (meshPoints (meshCount δ) fresh anchors)) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (squareMesh δ fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  meshGraph_outer_cycle (two_le_meshCount δ) hfresh anchors hsub


 




theorem squareMesh_outer_cycleGraph_isTwoConnected_of_subdividesToPath {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane)
    (hsub : SubdividesToPath (meshSegments (meshCount δ) fresh)
      (meshPoints (meshCount δ) fresh anchors)) :
    ∃ (e : Piece) (u : Plane) (D : List Piece),
      ((squareMesh δ fresh anchors).cycleGraph u e D).IsTwoConnected ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve := by
  obtain ⟨e, u, v, x, D, hlc, -, hcov⟩ :=
    squareMesh_outer_cycle_of_subdividesToPath hfresh δ anchors hsub
  exact ⟨e, u, D, Graph.IsLongCycle.isTwoConnected hlc, hcov⟩

end Schoenflies
