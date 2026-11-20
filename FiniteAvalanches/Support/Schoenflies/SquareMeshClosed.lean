/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/SquareMeshClosed.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.GridAttach
import FiniteAvalanches.Support.Schoenflies.SquareCycle

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 































































































open Metric Set
open scoped Graph

namespace Schoenflies

 






 


theorem subdividesToPath_of_overlay {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) : SubdividesToPath pieces points := by
  intro P hP hPnd
  obtain ⟨W, hW, hinc⟩ := exists_incWalk_insideEdges hnd hEnds hMeets hP hPnd
  exact ⟨W, hinc.isPath, hW⟩

 
theorem meshSubdividesToPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    SubdividesToPath (meshSegments N fresh) (meshPoints N fresh anchors) :=
  subdividesToPath_of_overlay (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)

 

 
theorem meshGraph_outer_cycle_of_mem_modelCurve {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (meshGraph N fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  meshGraph_outer_cycle hN hfresh anchors (meshSubdividesToPath hN hfresh anchors)

 
theorem squareMesh_outer_cycle {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (squareMesh δ fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  squareMesh_outer_cycle_of_subdividesToPath hfresh δ anchors
    (meshSubdividesToPath (two_le_meshCount δ) hfresh anchors)

 
theorem exists_squareMesh_outerCycleGraph_isTwoConnected {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ∃ (e : Piece) (u : Plane) (D : List Piece),
      ((squareMesh δ fresh anchors).cycleGraph u e D).IsTwoConnected ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  squareMesh_outer_cycleGraph_isTwoConnected_of_subdividesToPath hfresh δ anchors
    (meshSubdividesToPath (two_le_meshCount δ) hfresh anchors)

 





open scoped Classical in
 

noncomputable def outerCycleData (δ : ℝ) (fresh anchors : List Plane) :
    Piece × Plane × Plane × Plane × List Piece :=
  if h : ∃ t : Piece × Plane × Plane × Plane × List Piece,
      (squareMesh δ fresh anchors).IsLongCycle t.1 t.2.1 t.2.2.1 t.2.2.2.2 t.2.2.2.1 ∧
        (∀ Q ∈ t.1 :: t.2.2.2.2, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (t.1 :: t.2.2.2.2) = modelCurve
    then h.choose else ((0, 0), 0, 0, 0, [])

 
noncomputable def outerCycleEdge (δ : ℝ) (fresh anchors : List Plane) : Piece :=
  (outerCycleData δ fresh anchors).1

 
noncomputable def outerCycleStart (δ : ℝ) (fresh anchors : List Plane) : Plane :=
  (outerCycleData δ fresh anchors).2.1

 
noncomputable def outerCycleEnd (δ : ℝ) (fresh anchors : List Plane) : Plane :=
  (outerCycleData δ fresh anchors).2.2.1

 

noncomputable def outerCycleThird (δ : ℝ) (fresh anchors : List Plane) : Plane :=
  (outerCycleData δ fresh anchors).2.2.2.1

 

noncomputable def outerCycleDetour (δ : ℝ) (fresh anchors : List Plane) : List Piece :=
  (outerCycleData δ fresh anchors).2.2.2.2

theorem outerCycleData_spec {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane) :
    (squareMesh δ fresh anchors).IsLongCycle (outerCycleEdge δ fresh anchors)
        (outerCycleStart δ fresh anchors) (outerCycleEnd δ fresh anchors)
        (outerCycleDetour δ fresh anchors) (outerCycleThird δ fresh anchors) ∧
      (∀ Q ∈ outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors,
        Q.seg ⊆ modelCurve) ∧
      Graph.edgesCover segmentDrawing
        (outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors) = modelCurve := by
  classical
  have h : ∃ t : Piece × Plane × Plane × Plane × List Piece,
      (squareMesh δ fresh anchors).IsLongCycle t.1 t.2.1 t.2.2.1 t.2.2.2.2 t.2.2.2.1 ∧
        (∀ Q ∈ t.1 :: t.2.2.2.2, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (t.1 :: t.2.2.2.2) = modelCurve := by
    obtain ⟨e, u, v, x, D, h₁, h₂, h₃⟩ := squareMesh_outer_cycle hfresh δ anchors
    exact ⟨(e, u, v, x, D), h₁, h₂, h₃⟩
  have hd : outerCycleData δ fresh anchors = h.choose := dif_pos h
  simpa [outerCycleEdge, outerCycleStart, outerCycleEnd, outerCycleThird, outerCycleDetour, hd]
    using h.choose_spec

 

theorem squareMesh_isLongCycle_outerCycle {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    (squareMesh δ fresh anchors).IsLongCycle (outerCycleEdge δ fresh anchors)
      (outerCycleStart δ fresh anchors) (outerCycleEnd δ fresh anchors)
      (outerCycleDetour δ fresh anchors) (outerCycleThird δ fresh anchors) :=
  (outerCycleData_spec hfresh δ anchors).1

 
theorem squareMesh_outerCycle_subset_modelCurve {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ∀ Q ∈ outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors,
      Q.seg ⊆ modelCurve :=
  (outerCycleData_spec hfresh δ anchors).2.1

 
theorem squareMesh_outerCycle_edgesCover {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    Graph.edgesCover segmentDrawing
      (outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors) = modelCurve :=
  (outerCycleData_spec hfresh δ anchors).2.2

 
theorem squareMesh_outerCycleGraph_isTwoConnected {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ((squareMesh δ fresh anchors).cycleGraph (outerCycleStart δ fresh anchors)
      (outerCycleEdge δ fresh anchors) (outerCycleDetour δ fresh anchors)).IsTwoConnected :=
  (squareMesh_isLongCycle_outerCycle hfresh δ anchors).isTwoConnected

 






 
def rsideT (r : ℝ) : Piece := (Plane.mk r r, Plane.mk (-r) r)

 
def rsideL (r : ℝ) : Piece := (Plane.mk (-r) r, Plane.mk (-r) (-r))

 
def rsideB (r : ℝ) : Piece := (Plane.mk (-r) (-r), Plane.mk r (-r))

 
def rsideR (r : ℝ) : Piece := (Plane.mk r (-r), Plane.mk r r)

theorem rsideT_one : rsideT 1 = sideT := rfl
theorem rsideL_one : rsideL 1 = sideL := rfl
theorem rsideB_one : rsideB 1 = sideB := rfl
theorem rsideR_one : rsideR 1 = sideR := rfl

theorem rsideT_mem_ringPieces (r : ℝ) : rsideT r ∈ ringPieces r := by
  simp [ringPieces, rsideT]

theorem rsideL_mem_ringPieces (r : ℝ) : rsideL r ∈ ringPieces r := by
  simp [ringPieces, rsideL]

theorem rsideB_mem_ringPieces (r : ℝ) : rsideB r ∈ ringPieces r := by
  simp [ringPieces, rsideB]

theorem rsideR_mem_ringPieces (r : ℝ) : rsideR r ∈ ringPieces r := by
  simp [ringPieces, rsideR]

theorem mem_rsideT {r : ℝ} {x : Plane} (h : x ∈ (rsideT r).seg) : x 1 = r :=
  (mem_segment_horiz.1 h).1

theorem mem_rsideB {r : ℝ} {x : Plane} (h : x ∈ (rsideB r).seg) : x 1 = -r :=
  (mem_segment_horiz.1 h).1

theorem mem_rsideL {r : ℝ} {x : Plane} (h : x ∈ (rsideL r).seg) : x 0 = -r :=
  (mem_segment_vert.1 h).1

theorem mem_rsideR {r : ℝ} {x : Plane} (h : x ∈ (rsideR r).seg) : x 0 = r :=
  (mem_segment_vert.1 h).1

theorem rsideT_inter_rsideL {r : ℝ} {x : Plane} (h : x ∈ (rsideT r).seg)
    (h' : x ∈ (rsideL r).seg) : x = Plane.mk (-r) r :=
  plane_eq_of_coords (by rw [mem_rsideL h', Plane.mk_zero]) (by rw [mem_rsideT h, Plane.mk_one])

theorem rsideL_inter_rsideB {r : ℝ} {x : Plane} (h : x ∈ (rsideL r).seg)
    (h' : x ∈ (rsideB r).seg) : x = Plane.mk (-r) (-r) :=
  plane_eq_of_coords (by rw [mem_rsideL h, Plane.mk_zero]) (by rw [mem_rsideB h', Plane.mk_one])

theorem rsideB_inter_rsideR {r : ℝ} {x : Plane} (h : x ∈ (rsideB r).seg)
    (h' : x ∈ (rsideR r).seg) : x = Plane.mk r (-r) :=
  plane_eq_of_coords (by rw [mem_rsideR h', Plane.mk_zero]) (by rw [mem_rsideB h, Plane.mk_one])

theorem rsideT_inter_rsideR {r : ℝ} {x : Plane} (h : x ∈ (rsideT r).seg)
    (h' : x ∈ (rsideR r).seg) : x = Plane.mk r r :=
  plane_eq_of_coords (by rw [mem_rsideR h', Plane.mk_zero]) (by rw [mem_rsideT h, Plane.mk_one])

theorem rsideT_disjoint_rsideB {r : ℝ} (hr : 0 < r) {x : Plane} (h : x ∈ (rsideT r).seg)
    (h' : x ∈ (rsideB r).seg) : False := by
  have := (mem_rsideT h).symm.trans (mem_rsideB h'); linarith

theorem rsideL_disjoint_rsideR {r : ℝ} (hr : 0 < r) {x : Plane} (h : x ∈ (rsideL r).seg)
    (h' : x ∈ (rsideR r).seg) : False := by
  have := (mem_rsideL h).symm.trans (mem_rsideR h'); linarith

 
theorem rsides_cover {r : ℝ} (hr : 0 ≤ r) :
    (rsideT r).seg ∪ (rsideL r).seg ∪ (rsideB r).seg ∪ (rsideR r).seg = ringSet r := by
  rw [← cover_ringPieces hr]
  simp only [ringPieces, cover_cons, cover_nil, Set.union_empty, rsideT, rsideL, rsideB, rsideR]
  ext z
  simp only [Set.mem_union]
  tauto

theorem rside_seg_subset_ringSet {r : ℝ} (hr : 0 ≤ r) {P : Piece}
    (h : P = rsideT r ∨ P = rsideL r ∨ P = rsideB r ∨ P = rsideR r) : P.seg ⊆ ringSet r := by
  rw [← rsides_cover hr]
  rcases h with rfl | rfl | rfl | rfl
  exacts [fun x hx => Or.inl (Or.inl (Or.inl hx)), fun x hx => Or.inl (Or.inl (Or.inr hx)),
    fun x hx => Or.inl (Or.inr hx), fun x hx => Or.inr hx]

 
theorem ring_ringPieces_mem {N : ℕ} {fresh : List Plane} {r : ℝ} (hr : r ∈ meshRadii N)
    {R : Piece} (hR : R ∈ ringPieces r) : R ∈ meshSegments N fresh :=
  mem_meshSegments.2 (Or.inl ⟨r, hr, hR⟩)

 










 





theorem meshGraph_ring_cycle {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) {r : ℝ}
    (hr : r ∈ meshRadii N) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (meshGraph N fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ ringSet r) ∧
        Graph.edgesCover segmentDrawing (e :: D) = ringSet r := by
  have hrpos : 0 < r := meshRadii_pos hN hr
  have hsub : SubdividesToPath (meshSegments N fresh) (meshPoints N fresh anchors) :=
    meshSubdividesToPath hN hfresh anchors
  have hmemT := ring_ringPieces_mem (fresh := fresh) hr (rsideT_mem_ringPieces r)
  have hmemL := ring_ringPieces_mem (fresh := fresh) hr (rsideL_mem_ringPieces r)
  have hmemB := ring_ringPieces_mem (fresh := fresh) hr (rsideB_mem_ringPieces r)
  have hmemR := ring_ringPieces_mem (fresh := fresh) hr (rsideR_mem_ringPieces r)
  obtain ⟨WT, hpT, hcT⟩ := hsub _ hmemT (ringPieces_nondeg hrpos _ (rsideT_mem_ringPieces r))
  obtain ⟨WL, hpL, hcL⟩ := hsub _ hmemL (ringPieces_nondeg hrpos _ (rsideL_mem_ringPieces r))
  obtain ⟨WB, hpB, hcB⟩ := hsub _ hmemB (ringPieces_nondeg hrpos _ (rsideB_mem_ringPieces r))
  obtain ⟨WR, hpR, hcR⟩ := hsub _ hmemR (ringPieces_nondeg hrpos _ (rsideR_mem_ringPieces r))
  have hsegT : ∀ Q ∈ WT, Q.seg ⊆ (rsideT r).seg := fun Q hQ => ((hcT Q).1 hQ).2
  have hsegL : ∀ Q ∈ WL, Q.seg ⊆ (rsideL r).seg := fun Q hQ => ((hcL Q).1 hQ).2
  have hsegB : ∀ Q ∈ WB, Q.seg ⊆ (rsideB r).seg := fun Q hQ => ((hcB Q).1 hQ).2
  have hsegR : ∀ Q ∈ WR, Q.seg ⊆ (rsideR r).seg := fun Q hQ => ((hcR Q).1 hQ).2
  
  have hVT : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideT r).1 WT,
      x ∈ (rsideT r).seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegT hx
  have hVL : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideL r).1 WL,
      x ∈ (rsideL r).seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegL hx
  have hVB : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideB r).1 WB,
      x ∈ (rsideB r).seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegB hx
  
  have hp1 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      (rsideT r).1 (WT ++ WL) (rsideL r).2 :=
    hpT.append_of_disjoint hpL fun x hx hx2 => rsideT_inter_rsideL (hVT x hx) (hVL x hx2)
  have hV1 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      (rsideT r).1 (WT ++ WL), x ∈ (rsideT r).seg ∪ (rsideL r).seg := by
    refine fun x hx => walkVertices_subset_of_edges (Or.inl (left_mem_segment ℝ _ _))
      (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    exacts [(hsegT Q h).trans Set.subset_union_left, (hsegL Q h).trans Set.subset_union_right]
  
  have hp2 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      (rsideT r).1 ((WT ++ WL) ++ WB) (rsideB r).2 := by
    refine hp1.append_of_disjoint hpB fun x hx hx2 => ?_
    rcases hV1 x hx with h | h
    · exact absurd (rsideT_disjoint_rsideB hrpos h (hVB x hx2)) not_false
    · exact rsideL_inter_rsideB h (hVB x hx2)
  have hV2 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      (rsideT r).1 ((WT ++ WL) ++ WB),
      x ∈ (rsideT r).seg ∪ (rsideL r).seg ∪ (rsideB r).seg := by
    refine fun x hx => walkVertices_subset_of_edges
      (Or.inl (Or.inl (left_mem_segment ℝ _ _))) (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    · rcases List.mem_append.1 h with h' | h'
      exacts [(hsegT Q h').trans (Set.subset_union_left.trans Set.subset_union_left),
        (hsegL Q h').trans (Set.subset_union_right.trans Set.subset_union_left)]
    · exact (hsegB Q h).trans Set.subset_union_right
  
  have hRne : (rsideR r).1 ≠ (rsideR r).2 := ringPieces_nondeg hrpos _ (rsideR_mem_ringPieces r)
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
  have hwR : w ∈ (rsideR r).seg := by
    rcases hlink.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [hsegR eR heRmem (right_mem_segment ℝ _ _),
      hsegR eR heRmem (left_mem_segment ℝ _ _)]
  have hVRtail : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices w L, x ∈ (rsideR r).seg := fun x hx =>
    walkVertices_subset_of_edges hwR (fun Q hQ => hsegR Q (hLmem Q hQ)) hx
  have hrevV : (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices (rsideB r).2 L.reverse
      = (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices w L :=
    htail.isWalk.reverse_walkVertices
  
  have hp3 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      (rsideT r).1 (((WT ++ WL) ++ WB) ++ L.reverse) w := by
    refine hp2.append_of_disjoint htail.reverse fun x hx hx2 => ?_
    rw [hrevV] at hx2
    have hxR : x ∈ (rsideR r).seg := hVRtail x hx2
    rcases hV2 x hx with (h | h) | h
    · refine absurd (show (rsideR r).2 ∈ (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices w L from ?_) hfr
      rwa [show (rsideR r).2 = x from (rsideT_inter_rsideR h hxR).symm]
    · exact absurd (rsideL_disjoint_rsideR hrpos h hxR) not_false
    · exact rsideB_inter_rsideR h hxR
  
  have hnondegR : eR.Nondeg :=
    meshGraph_edge_nondeg (anchors := anchors) hN hfresh ((hcR eR).1 heRmem).1
  have hnotT : eR ∉ WT := fun hmem => hnondegR (by
    have h1 := rsideT_inter_rsideR (hsegT eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := rsideT_inter_rsideR (hsegT eR hmem (right_mem_segment ℝ _ _))
      (hsegR eR heRmem (right_mem_segment ℝ _ _))
    exact h1.trans h2.symm)
  have hnotL : eR ∉ WL := fun hmem =>
    rsideL_disjoint_rsideR hrpos (hsegL eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
  have hnotB : eR ∉ WB := fun hmem => hnondegR (by
    have h1 := rsideB_inter_rsideR (hsegB eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := rsideB_inter_rsideR (hsegB eR hmem (right_mem_segment ℝ _ _))
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
  
  have hmT : (rsideT r).seg ⊆ ringSet r := rside_seg_subset_ringSet hrpos.le (Or.inl rfl)
  have hmL : (rsideL r).seg ⊆ ringSet r :=
    rside_seg_subset_ringSet hrpos.le (Or.inr (Or.inl rfl))
  have hmB : (rsideB r).seg ⊆ ringSet r :=
    rside_seg_subset_ringSet hrpos.le (Or.inr (Or.inr (Or.inl rfl)))
  have hmR : (rsideR r).seg ⊆ ringSet r :=
    rside_seg_subset_ringSet hrpos.le (Or.inr (Or.inr (Or.inr rfl)))
  have hsegsAll : ∀ Q ∈ eR :: (((WT ++ WL) ++ WB) ++ L.reverse), Q.seg ⊆ ringSet r := by
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | h
    · exact (hsegR Q heRmem).trans hmR
    rcases List.mem_append.1 h with h' | h'
    · rcases List.mem_append.1 h' with h'' | h''
      · rcases List.mem_append.1 h'' with h3 | h3
        exacts [(hsegT Q h3).trans hmT, (hsegL Q h3).trans hmL]
      · exact (hsegB Q h'').trans hmB
    · exact (hsegR Q (hLmem Q (List.mem_reverse.1 h'))).trans hmR
  
  have hthird : (rsideT r).2 ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideT r).1
        (((WT ++ WL) ++ WB) ++ L.reverse) :=
    Graph.walkVertices_mono
      (List.Subset.trans (List.subset_append_left _ _)
        (List.Subset.trans (List.subset_append_left _ _) (List.subset_append_left _ _)))
      hpT.isWalk.target_mem_walkVertices
  have hne₁ : (rsideT r).2 ≠ (rsideT r).1 :=
    mk_ne_mk_of_fst (by intro h; linarith)
  have hne₂ : (rsideT r).2 ≠ w := by
    intro h
    have hw := mem_rsideR (h ▸ hwR)
    rw [rsideT, Plane.mk_zero] at hw
    linarith
  refine ⟨eR, (rsideT r).1, w, (rsideT r).2, ((WT ++ WL) ++ WB) ++ L.reverse,
    ⟨⟨hlink, hp3, hnotD⟩, hthird, hne₁, hne₂⟩, hsegsAll, ?_⟩
  have hcovT : Graph.edgesCover segmentDrawing WT = (rsideT r).seg := edgesCover_eq_seg hmemT hcT
  have hcovL : Graph.edgesCover segmentDrawing WL = (rsideL r).seg := edgesCover_eq_seg hmemL hcL
  have hcovB : Graph.edgesCover segmentDrawing WB = (rsideB r).seg := edgesCover_eq_seg hmemB hcB
  have hcovR : Graph.edgesCover segmentDrawing WR = (rsideR r).seg := edgesCover_eq_seg hmemR hcR
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
    rw [edgeArc_segmentDrawing] at hzQ
    exact hsegsAll Q hQ hzQ
  · rw [← rsides_cover hrpos.le] at hz
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


 








 

theorem squarePieces_zero (r : ℝ) : squarePieces 0 r = ringPieces r := by
  simp [squarePieces, ringPieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE]

 

theorem frontier_closedSquare_zero {r : ℝ} (hr : 0 ≤ r) :
    frontier (Plane.closedSquare 0 r) = ringSet r := by
  rw [← cover_squarePieces 0 hr, squarePieces_zero, cover_ringPieces hr]

 
noncomputable def ringGraph (N : ℕ) (fresh anchors : List Plane) (r : ℝ) : Graph Plane Piece :=
  squareGraph (meshSegments N fresh) (meshPoints N fresh anchors) 0 r

theorem ringGraph_le (N : ℕ) (fresh anchors : List Plane) (r : ℝ) :
    ringGraph N fresh anchors r ≤ meshGraph N fresh anchors :=
  squareGraph_le

 
theorem squarePieces_zero_subset_meshSegments {N : ℕ} {fresh : List Plane} {r : ℝ}
    (hr : r ∈ meshRadii N) : ∀ P ∈ squarePieces 0 r, P ∈ meshSegments N fresh := by
  rw [squarePieces_zero]
  exact fun P hP => ring_ringPieces_mem hr hP

 
theorem ringGraph_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) {r : ℝ}
    (hr : r ∈ meshRadii N) : (ringGraph N fresh anchors r).IsTwoConnected :=
  squareGraph_isTwoConnected (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)
    (meshRadii_pos hN hr) (squarePieces_zero_subset_meshSegments hr)

 


theorem mem_vertexSet_ringGraph {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) {anchors : List Plane} {r : ℝ}
    (hr : r ∈ meshRadii N) {y : Plane} (hy : y ∈ meshPoints N fresh anchors)
    (hyr : y ∈ ringSet r) : y ∈ V(ringGraph N fresh anchors r) :=
  mem_vertexSet_squareGraph (meshSegments_nondeg hN hfresh) (meshRadii_pos hN hr).le
    (squarePieces_zero_subset_meshSegments hr) hy
    (by rw [frontier_closedSquare_zero (meshRadii_pos hN hr).le]; exact hyr)


 









theorem inv_le_of_mem_meshRadii {N : ℕ} (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ meshRadii N) :
    ((N : ℝ)⁻¹) ≤ r := by
  obtain ⟨j, -, rfl⟩ := mem_meshRadii.1 hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hN
  rw [inv_eq_one_div, div_le_div_iff_of_pos_right hN0]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

 
theorem spokePiece_inter_ringSet {N : ℕ} (hN : 2 ≤ N) {z : Plane} (hz : z ∈ modelCurve)
    {r : ℝ} (hr : r ∈ meshRadii N) : (spokePiece N z).seg ∩ ringSet r = {r • z} := by
  have hrpos : 0 < r := meshRadii_pos hN hr
  ext x
  rw [spokePiece_seg hN]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hx⟩
    have : t = r := by
      rw [← supNorm_smul_of_mem_modelCurve (le_trans (inv_cast_pos hN).le ht.1) hz]
      exact hx
    simp [this]
  · rintro rfl
    exact ⟨⟨r, ⟨inv_le_of_mem_meshRadii hN hr, meshRadii_le_one hN hr⟩, rfl⟩,
      supNorm_smul_of_mem_modelCurve hrpos.le hz⟩

theorem smul_mem_ringSet {r : ℝ} (hr : 0 ≤ r) {z : Plane} (hz : z ∈ modelCurve) :
    r • z ∈ ringSet r := supNorm_smul_of_mem_modelCurve hr hz

 



theorem smul_mem_meshPoints {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) : r • z ∈ meshPoints N fresh anchors := by
  have hzm : z ∈ modelCurve := hfresh z hz
  have hrpos : 0 < r := meshRadii_pos hN hr
  
  have hmemring : r • z ∈ cover (ringPieces r) := by
    rw [cover_ringPieces hrpos.le]; exact smul_mem_ringSet hrpos.le hzm
  obtain ⟨Q, hQ, hxQ⟩ := mem_cover_iff.1 hmemring
  set P : Piece := spokePiece N z with hP
  have hPmem : P ∈ meshSegments N fresh := spokePiece_mem_meshSegments hz
  have hQmem : Q ∈ meshSegments N fresh := ring_ringPieces_mem hr hQ
  have hQring : Q.seg ⊆ ringSet r := ringPieces_seg_subset hrpos.le hQ
  
  have hPQ : P ≠ Q := by
    intro h
    have h1 : Plane.supNorm z = r := hQring (h ▸ left_mem_segment ℝ P.1 P.2)
    have h2 : Plane.supNorm (((N : ℝ)⁻¹) • z) = r := hQring (h ▸ right_mem_segment ℝ P.1 P.2)
    rw [supNorm_smul_of_mem_modelCurve (inv_cast_pos hN).le hzm] at h2
    rw [show Plane.supNorm z = 1 from hzm] at h1
    exact absurd (h2.trans h1.symm) (ne_of_lt (inv_cast_lt_one hN))
  
  have hmeetsub : meetOf P Q ⊆ {r • z} := by
    rw [← spokePiece_inter_ringSet hN hzm hr]
    exact fun x hx => ⟨hx.1, hQring hx.2⟩
  have hmeetmem : r • z ∈ meetOf P Q :=
    ⟨((spokePiece_inter_ringSet hN hzm hr).symm ▸ rfl : r • z ∈ (spokePiece N z).seg ∩ ringSet r).1,
      hxQ⟩
  obtain ⟨u, v, huv, hu, -⟩ :=
    meshPoints_meetsAreCut N fresh anchors P hPmem Q hQmem hPQ ⟨_, hmeetmem⟩
  have : u = r • z := hmeetsub (huv ▸ left_mem_segment ℝ u v)
  exact this ▸ hu

 
theorem smul_mem_vertexSet_ringGraph {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) : r • z ∈ V(ringGraph N fresh anchors r) :=
  mem_vertexSet_ringGraph hN hfresh hr (smul_mem_meshPoints hN hfresh anchors hz hr)
    (smul_mem_ringSet (meshRadii_pos hN hr).le (hfresh z hz))

 
theorem smul_ne_smul {r : ℝ} (hr : r ≠ 0) {z w : Plane} (hzw : z ≠ w) : r • z ≠ r • w := by
  intro h
  exact hzw (smul_right_injective Plane hr h)


 






 


theorem mem_walkVertices_of_mem_points {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) {P : Piece} (hP : P ∈ pieces) {W : List Piece}
    (hW : ∀ Q, Q ∈ W ↔ (Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ P.seg))
    {q : Plane} (hq : q ∈ points) (hqP : q ∈ P.seg) :
    q ∈ (overlayGraph pieces points).walkVertices P.1 W := by
  have hcov : Graph.edgesCover segmentDrawing W = P.seg := edgesCover_eq_seg hP hW
  rw [← hcov] at hqP
  obtain ⟨Q, hQ, hqQ⟩ := Graph.mem_edgesCover_iff.1 hqP
  rw [edgeArc_segmentDrawing] at hqQ
  have hQmem : Q ∈ overlayPieces pieces points := ((hW Q).1 hQ).1
  have hint : q ∉ Q.interior := overlayPieces_avoids hnd q hq Q hQmem
  have hend : q = Q.1 ∨ q = Q.2 := by
    by_contra hcon
    push Not at hcon
    exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hqQ)
  exact Graph.mem_walkVertices_of_mem_covered
    (Graph.mem_coveredVertices hQ (overlayGraph_inc hQmem hend))

open scoped Classical in
 


noncomputable def spokeWalk (N : ℕ) (fresh anchors : List Plane) (z : Plane) : List Piece :=
  if h : ∃ W : List Piece,
      (meshGraph N fresh anchors).IsPath z W (((N : ℝ)⁻¹) • z) ∧
        ∀ Q, Q ∈ W ↔ (Q ∈ E(meshGraph N fresh anchors) ∧ Q.seg ⊆ (spokePiece N z).seg)
    then h.choose else []

theorem spokeWalk_spec {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    (meshGraph N fresh anchors).IsPath z (spokeWalk N fresh anchors z) (((N : ℝ)⁻¹) • z) ∧
      ∀ Q, Q ∈ spokeWalk N fresh anchors z ↔
        (Q ∈ E(meshGraph N fresh anchors) ∧ Q.seg ⊆ (spokePiece N z).seg) := by
  classical
  have h : ∃ W : List Piece,
      (meshGraph N fresh anchors).IsPath z W (((N : ℝ)⁻¹) • z) ∧
        ∀ Q, Q ∈ W ↔ (Q ∈ E(meshGraph N fresh anchors) ∧ Q.seg ⊆ (spokePiece N z).seg) :=
    meshSubdividesToPath hN hfresh anchors _ (spokePiece_mem_meshSegments hz)
      (spokePiece_nondeg hN (hfresh z hz))
  rw [spokeWalk, dif_pos h]
  exact h.choose_spec

theorem spokeWalk_isPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh) :
    (meshGraph N fresh anchors).IsPath z (spokeWalk N fresh anchors z) (((N : ℝ)⁻¹) • z) :=
  (spokeWalk_spec hN hfresh anchors hz).1

theorem spokeWalk_seg_subset {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {Q : Piece} (hQ : Q ∈ spokeWalk N fresh anchors z) : Q.seg ⊆ (spokePiece N z).seg :=
  (((spokeWalk_spec hN hfresh anchors hz).2 Q).1 hQ).2

 
theorem smul_mem_walkVertices_spokeWalk {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) :
    r • z ∈ (meshGraph N fresh anchors).walkVertices z (spokeWalk N fresh anchors z) := by
  have hmem : r • z ∈ (spokePiece N z).seg :=
    ((spokePiece_inter_ringSet hN (hfresh z hz) hr).symm.subset rfl).1
  exact mem_walkVertices_of_mem_points (meshSegments_nondeg hN hfresh)
    (spokePiece_mem_meshSegments hz) (spokeWalk_spec hN hfresh anchors hz).2
    (smul_mem_meshPoints hN hfresh anchors hz hr) hmem

 
theorem walkVertices_spokeWalk_subset {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z : Plane} (hz : z ∈ fresh)
    {x : Plane}
    (hx : x ∈ (meshGraph N fresh anchors).walkVertices z (spokeWalk N fresh anchors z)) :
    x ∈ (spokePiece N z).seg :=
  walkVertices_subset_of_edges (left_mem_segment ℝ _ _)
    (fun _ hQ => spokeWalk_seg_subset hN hfresh anchors hz hQ) hx


 














 

theorem spokePiece_disjoint {N : ℕ} (hN : 2 ≤ N) {z w : Plane} (hz : z ∈ modelCurve)
    (hw : w ∈ modelCurve) (hzw : z ≠ w) {x : Plane} (hxz : x ∈ (spokePiece N z).seg)
    (hxw : x ∈ (spokePiece N w).seg) : False := by
  rw [spokePiece_seg hN] at hxz hxw
  obtain ⟨t, ht, hxt⟩ := hxz
  obtain ⟨s, hs, hxs⟩ := hxw
  have hxt' : t • z = x := hxt
  have hxs' : s • w = x := hxs
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (inv_cast_pos hN) ht.1
  have hspos : (0 : ℝ) ≤ s := le_trans (inv_cast_pos hN).le hs.1
  have h1 : Plane.supNorm x = t := by
    rw [← hxt']; exact supNorm_smul_of_mem_modelCurve htpos.le hz
  have h2 : Plane.supNorm x = s := by
    rw [← hxs']; exact supNorm_smul_of_mem_modelCurve hspos hw
  rw [show s = t from by rw [← h2, h1]] at hxs'
  exact hzw (smul_right_injective Plane (ne_of_gt htpos) (hxt'.trans hxs'.symm))

theorem ringGraph_edge_seg_subset {N : ℕ} {fresh anchors : List Plane} {r : ℝ} (hr : 0 ≤ r)
    {Q : Piece} (hQ : Q ∈ E(ringGraph N fresh anchors r)) : Q.seg ⊆ ringSet r := by
  rw [← frontier_closedSquare_zero hr]
  exact (mem_edgeSet_squareGraph_iff.1 hQ).2

open scoped Classical in
 


noncomputable def ringArc (N : ℕ) (fresh anchors : List Plane) (r : ℝ) (a b : Plane) :
    List Piece :=
  if h : ∃ P : List Piece, (ringGraph N fresh anchors r).IsPath a P b then h.choose else []

theorem ringArc_isPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {r : ℝ}
    (hr : r ∈ meshRadii N) {a b : Plane} (ha : a ∈ V(ringGraph N fresh anchors r))
    (hb : b ∈ V(ringGraph N fresh anchors r)) :
    (ringGraph N fresh anchors r).IsPath a (ringArc N fresh anchors r a b) b := by
  classical
  have h : ∃ P : List Piece, (ringGraph N fresh anchors r).IsPath a P b :=
    (ringGraph_isTwoConnected hN hfresh anchors hr).connected.exists_isPath ha hb
  rw [ringArc, dif_pos h]
  exact h.choose_spec

 
noncomputable def meshEar (N : ℕ) (fresh anchors : List Plane) (z w : Plane) : List Piece :=
  spokeWalk N fresh anchors z ++
    ringArc N fresh anchors ((N : ℝ)⁻¹) (((N : ℝ)⁻¹) • z) (((N : ℝ)⁻¹) • w) ++
    (spokeWalk N fresh anchors w).reverse

theorem meshEar_isPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshGraph N fresh anchors).IsPath z (meshEar N fresh anchors z w) w := by
  set G := meshGraph N fresh anchors with hG
  set rmin : ℝ := ((N : ℝ)⁻¹) with hrmin
  have hrm : rmin ∈ meshRadii N := inv_mem_meshRadii hN
  have hrmpos : 0 < rmin := inv_cast_pos hN
  have hzm : z ∈ modelCurve := hfresh z hz
  have hwm : w ∈ modelCurve := hfresh w hw
  
  have hP1 : G.IsPath z (spokeWalk N fresh anchors z) (rmin • z) :=
    spokeWalk_isPath hN hfresh anchors hz
  have hP3 : G.IsPath (rmin • w) (spokeWalk N fresh anchors w).reverse w :=
    (spokeWalk_isPath hN hfresh anchors hw).reverse
  have harc := ringArc_isPath hN hfresh anchors hrm
    (smul_mem_vertexSet_ringGraph hN hfresh anchors hz hrm)
    (smul_mem_vertexSet_ringGraph hN hfresh anchors hw hrm)
  have hP2 : G.IsPath (rmin • z) (ringArc N fresh anchors rmin (rmin • z) (rmin • w))
      (rmin • w) := harc.mono (ringGraph_le N fresh anchors rmin)
  
  have harcseg : ∀ Q ∈ ringArc N fresh anchors rmin (rmin • z) (rmin • w), Q.seg ⊆ ringSet rmin :=
    fun Q hQ => ringGraph_edge_seg_subset hrmpos.le (harc.isWalk.edgeSet_subset Q hQ)
  have hV2 : ∀ x ∈ G.walkVertices (rmin • z)
      (ringArc N fresh anchors rmin (rmin • z) (rmin • w)), x ∈ ringSet rmin :=
    fun x hx => walkVertices_subset_of_edges (smul_mem_ringSet hrmpos.le hzm) harcseg hx
  have hV3 : ∀ x ∈ G.walkVertices (rmin • w) (spokeWalk N fresh anchors w).reverse,
      x ∈ (spokePiece N w).seg := by
    refine fun x hx => walkVertices_subset_of_edges ?_ (fun Q hQ =>
      spokeWalk_seg_subset hN hfresh anchors hw (List.mem_reverse.1 hQ)) hx
    exact ((spokePiece_inter_ringSet hN hwm hrm).symm.subset rfl).1
  
  have hp1 : G.IsPath z (spokeWalk N fresh anchors z ++
      ringArc N fresh anchors rmin (rmin • z) (rmin • w)) (rmin • w) := by
    refine hP1.append_of_disjoint hP2 fun x hx hx2 => ?_
    have hxs : x ∈ (spokePiece N z).seg :=
      walkVertices_spokeWalk_subset hN hfresh anchors hz hx
    have := (spokePiece_inter_ringSet hN hzm hrm).subset ⟨hxs, hV2 x hx2⟩
    exact this
  have hV1 : ∀ x ∈ G.walkVertices z (spokeWalk N fresh anchors z ++
      ringArc N fresh anchors rmin (rmin • z) (rmin • w)),
      x ∈ (spokePiece N z).seg ∪ ringSet rmin := by
    refine fun x hx => walkVertices_subset_of_edges (Or.inl (left_mem_segment ℝ _ _))
      (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    · exact (spokeWalk_seg_subset hN hfresh anchors hz h).trans Set.subset_union_left
    · exact (harcseg Q h).trans Set.subset_union_right
  
  refine hp1.append_of_disjoint hP3 fun x hx hx2 => ?_
  have hxw : x ∈ (spokePiece N w).seg := hV3 x hx2
  rcases hV1 x hx with h | h
  · exact absurd (spokePiece_disjoint hN hzm hwm hzw h hxw) not_false
  · exact (spokePiece_inter_ringSet hN hwm hrm).subset ⟨hxw, h⟩


 








 
noncomputable def spokeGraph (N : ℕ) (fresh anchors : List Plane) (u : Plane) :
    Graph Plane Piece :=
  (meshGraph N fresh anchors).pathGraphOf u (spokeWalk N fresh anchors u)

theorem spokeGraph_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {u : Plane} (hu : u ∈ fresh) :
    spokeGraph N fresh anchors u ≤ meshGraph N fresh anchors :=
  Graph.pathGraphOf_le (spokeWalk_isPath hN hfresh anchors hu).isWalk

 
theorem smul_ne_self {N : ℕ} (hN : 2 ≤ N) {u : Plane} (hu : u ∈ modelCurve) {r : ℝ}
    (hr : r ∈ meshRadii N) (hr1 : r ≠ 1) : r • u ≠ u := by
  intro h
  have h1 : Plane.supNorm (r • u) = r :=
    supNorm_smul_of_mem_modelCurve (meshRadii_pos hN hr).le hu
  rw [h, show Plane.supNorm u = 1 from hu] at h1
  exact hr1 h1.symm

 

theorem smul_mem_coveredVertices_spokeWalk {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {u : Plane} (hu : u ∈ fresh)
    {r : ℝ} (hr : r ∈ meshRadii N) (hr1 : r ≠ 1) :
    r • u ∈ (meshGraph N fresh anchors).coveredVertices (spokeWalk N fresh anchors u) := by
  rcases Graph.mem_walkVertices_iff.1
    (smul_mem_walkVertices_spokeWalk hN hfresh anchors hu hr) with h | h
  · exact absurd h (smul_ne_self hN (hfresh u hu) hr hr1)
  · exact h

 
noncomputable def meshCore (N : ℕ) (fresh anchors : List Plane) (z w : Plane) :
    Graph Plane Piece :=
  ((ringGraph N fresh anchors 1).union
      ((meshGraph N fresh anchors).pathGraphOf z (meshEar N fresh anchors z w))).union
    (ringGraph N fresh anchors ((N : ℝ)⁻¹))

theorem meshCore_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    meshCore N fresh anchors z w ≤ meshGraph N fresh anchors :=
  Graph.union_le
    (Graph.union_le (ringGraph_le N fresh anchors 1)
      (Graph.pathGraphOf_le (meshEar_isPath hN hfresh anchors hz hw hzw).isWalk))
    (ringGraph_le N fresh anchors _)

 
theorem mem_vertexSet_ringGraph_one {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {u : Plane} (hu : u ∈ fresh) :
    u ∈ V(ringGraph N fresh anchors 1) := by
  have := smul_mem_vertexSet_ringGraph hN hfresh anchors hu (one_mem_meshRadii hN)
  rwa [one_smul] at this

 
theorem meshCore_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshCore N fresh anchors z w).IsTwoConnected := by
  set G := meshGraph N fresh anchors with hG
  set rmin : ℝ := ((N : ℝ)⁻¹) with hrmin
  have hrm : rmin ∈ meshRadii N := inv_mem_meshRadii hN
  have hear := meshEar_isPath hN hfresh anchors hz hw hzw
  have hearle : G.pathGraphOf z (meshEar N fresh anchors z w) ≤ G :=
    Graph.pathGraphOf_le hear.isWalk
  
  have h1 : ((ringGraph N fresh anchors 1).union
      (G.pathGraphOf z (meshEar N fresh anchors z w))).IsTwoConnected :=
    (ringGraph_isTwoConnected hN hfresh anchors (one_mem_meshRadii hN)).ear
      (Graph.Compatible.of_le_le (ringGraph_le N fresh anchors 1) hearle)
      hear.isPathGraph_pathGraphOf hzw
      (mem_vertexSet_ringGraph_one hN hfresh anchors hz)
      (mem_vertexSet_ringGraph_one hN hfresh anchors hw)
  
  have hrne : rmin ≠ 1 := (inv_cast_lt_one hN).ne
  have hmemz : rmin • z ∈ V(G.pathGraphOf z (meshEar N fresh anchors z w)) :=
    Graph.mem_walkVertices_of_mem_covered (Graph.coveredVertices_mono
      (fun _ hQ => List.mem_append_left _ (List.mem_append_left _ hQ))
      (smul_mem_coveredVertices_spokeWalk hN hfresh anchors hz hrm hrne))
  have hmemw : rmin • w ∈ V(G.pathGraphOf z (meshEar N fresh anchors z w)) :=
    Graph.mem_walkVertices_of_mem_covered (Graph.coveredVertices_mono
      (fun _ hQ => List.mem_append_right _ (List.mem_reverse.2 hQ))
      (smul_mem_coveredVertices_spokeWalk hN hfresh anchors hw hrm hrne))
  exact h1.union (Graph.Compatible.of_le_le
      (Graph.union_le (ringGraph_le N fresh anchors 1) hearle) (ringGraph_le N fresh anchors rmin))
    (ringGraph_isTwoConnected hN hfresh anchors hrm)
    (smul_ne_smul (ne_of_gt (inv_cast_pos hN)) hzw)
    (Or.inr hmemz) (smul_mem_vertexSet_ringGraph hN hfresh anchors hz hrm)
    (Or.inr hmemw) (smul_mem_vertexSet_ringGraph hN hfresh anchors hw hrm)


 

 
theorem smul_mem_walkVertices_meshEar {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) {r : ℝ} (hr : r ∈ meshRadii N) :
    r • z ∈ (meshGraph N fresh anchors).walkVertices z (meshEar N fresh anchors z w) ∧
      r • w ∈ (meshGraph N fresh anchors).walkVertices z (meshEar N fresh anchors z w) := by
  have hear := meshEar_isPath hN hfresh anchors hz hw hzw
  constructor
  · exact Graph.walkVertices_mono
      (fun _ hQ => List.mem_append_left _ (List.mem_append_left _ hQ))
      (smul_mem_walkVertices_spokeWalk hN hfresh anchors hz hr)
  · by_cases h1 : r = 1
    · rw [h1, one_smul]; exact hear.isWalk.target_mem_walkVertices
    · exact Graph.mem_walkVertices_of_mem_covered (Graph.coveredVertices_mono
        (fun _ hQ => List.mem_append_right _ (List.mem_reverse.2 hQ))
        (smul_mem_coveredVertices_spokeWalk hN hfresh anchors hw hr h1))

 
noncomputable def attachRings (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece) :
    List ℝ → Graph Plane Piece
  | [] => K
  | r :: rs => (attachRings N fresh anchors K rs).union (ringGraph N fresh anchors r)

 

noncomputable def attachSpokes (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece) :
    List Plane → Graph Plane Piece
  | [] => K
  | u :: us => (attachSpokes N fresh anchors K us).union (spokeGraph N fresh anchors u)

theorem le_attachRings (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece)
    (l : List ℝ) : K ≤ attachRings N fresh anchors K l := by
  induction l with
  | nil => exact le_refl K
  | cons r rs ih => exact ih.trans (Graph.left_le_union _ _)

theorem le_attachSpokes (N : ℕ) (fresh anchors : List Plane) (K : Graph Plane Piece)
    (l : List Plane) : K ≤ attachSpokes N fresh anchors K l := by
  induction l with
  | nil => exact le_refl K
  | cons u us ih => exact ih.trans (Graph.left_le_union _ _)

theorem attachRings_le {N : ℕ} {fresh anchors : List Plane} {K : Graph Plane Piece}
    (hK : K ≤ meshGraph N fresh anchors) (l : List ℝ) :
    attachRings N fresh anchors K l ≤ meshGraph N fresh anchors := by
  induction l with
  | nil => exact hK
  | cons r rs ih => exact Graph.union_le ih (ringGraph_le _ _ _ _)

theorem attachSpokes_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) {anchors : List Plane} {K : Graph Plane Piece}
    (hK : K ≤ meshGraph N fresh anchors) {l : List Plane} (hl : ∀ u ∈ l, u ∈ fresh) :
    attachSpokes N fresh anchors K l ≤ meshGraph N fresh anchors := by
  induction l with
  | nil => exact hK
  | cons u us ih =>
    exact Graph.union_le (ih fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (spokeGraph_le hN hfresh anchors (hl u List.mem_cons_self))

theorem ringGraph_le_attachRings {N : ℕ} {fresh anchors : List Plane} {K : Graph Plane Piece}
    (hK : K ≤ meshGraph N fresh anchors) {l : List ℝ} {r : ℝ} (hr : r ∈ l) :
    ringGraph N fresh anchors r ≤ attachRings N fresh anchors K l := by
  induction l with
  | nil => exact absurd hr (List.not_mem_nil)
  | cons r' rs ih =>
    rcases List.mem_cons.1 hr with rfl | h
    · exact (Graph.Compatible.of_le_le (attachRings_le hK rs)
        (ringGraph_le N fresh anchors r)).right_le_union
    · exact (ih h).trans (Graph.left_le_union _ _)

theorem spokeGraph_le_attachSpokes {N : ℕ} {fresh anchors : List Plane}
    {K : Graph Plane Piece} (hK : K ≤ meshGraph N fresh anchors) {l : List Plane} {u : Plane}
    (hN : 2 ≤ N) (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (hl : ∀ x ∈ l, x ∈ fresh)
    (hu : u ∈ l) : spokeGraph N fresh anchors u ≤ attachSpokes N fresh anchors K l := by
  induction l with
  | nil => exact absurd hu (List.not_mem_nil)
  | cons u' us ih =>
    rcases List.mem_cons.1 hu with rfl | h
    · exact (Graph.Compatible.of_le_le
        (attachSpokes_le hN hfresh hK fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (spokeGraph_le hN hfresh anchors (hl u List.mem_cons_self))).right_le_union
    · exact (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h).trans (Graph.left_le_union _ _)

theorem attachRings_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) {anchors : List Plane} {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) {K : Graph Plane Piece}
    (hK : K.IsTwoConnected) (hKle : K ≤ meshGraph N fresh anchors)
    (hzK : ∀ r ∈ meshRadii N, r • z ∈ V(K)) (hwK : ∀ r ∈ meshRadii N, r • w ∈ V(K))
    {l : List ℝ} (hl : ∀ r ∈ l, r ∈ meshRadii N) :
    (attachRings N fresh anchors K l).IsTwoConnected := by
  induction l with
  | nil => exact hK
  | cons r rs ih =>
    have hrm : r ∈ meshRadii N := hl r List.mem_cons_self
    have hacc := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hmono := (le_attachRings N fresh anchors K rs).vertexSet_mono
    exact hacc.union (Graph.Compatible.of_le_le
        (attachRings_le hKle rs) (ringGraph_le N fresh anchors r))
      (ringGraph_isTwoConnected hN hfresh anchors hrm)
      (smul_ne_smul (ne_of_gt (meshRadii_pos hN hrm)) hzw)
      (hmono (hzK r hrm)) (smul_mem_vertexSet_ringGraph hN hfresh anchors hz hrm)
      (hmono (hwK r hrm)) (smul_mem_vertexSet_ringGraph hN hfresh anchors hw hrm)

theorem attachSpokes_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) {anchors : List Plane} {K : Graph Plane Piece}
    (hK : K.IsTwoConnected) (hKle : K ≤ meshGraph N fresh anchors)
    (houter : ∀ u ∈ fresh, u ∈ V(K)) (hinner : ∀ u ∈ fresh, ((N : ℝ)⁻¹) • u ∈ V(K))
    {l : List Plane} (hl : ∀ u ∈ l, u ∈ fresh) :
    (attachSpokes N fresh anchors K l).IsTwoConnected := by
  induction l with
  | nil => exact hK
  | cons u us ih =>
    have hu : u ∈ fresh := hl u List.mem_cons_self
    have hacc := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hmono := (le_attachSpokes N fresh anchors K us).vertexSet_mono
    refine hacc.ear (Graph.Compatible.of_le_le
        (attachSpokes_le hN hfresh hKle fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (spokeGraph_le hN hfresh anchors hu))
      (spokeWalk_isPath hN hfresh anchors hu).isPathGraph_pathGraphOf ?_
      (hmono (houter u hu)) (hmono (hinner u hu))
    exact fun h => smul_ne_self hN (hfresh u hu) (inv_mem_meshRadii hN)
      (inv_cast_lt_one hN).ne h.symm


 

 
noncomputable def meshAssembly (N : ℕ) (fresh anchors : List Plane) (z w : Plane) :
    Graph Plane Piece :=
  attachSpokes N fresh anchors
    (attachRings N fresh anchors (meshCore N fresh anchors z w) (meshRadii N)) fresh

theorem meshAssembly_le {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    meshAssembly N fresh anchors z w ≤ meshGraph N fresh anchors :=
  attachSpokes_le hN hfresh
    (attachRings_le (meshCore_le hN hfresh anchors hz hw hzw) (meshRadii N)) fun _ hx => hx

theorem meshAssembly_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshAssembly N fresh anchors z w).IsTwoConnected := by
  have hcore := meshCore_isTwoConnected hN hfresh anchors hz hw hzw
  have hcorele := meshCore_le hN hfresh anchors hz hw hzw
  
  have hzK : ∀ r ∈ meshRadii N, r • z ∈ V(meshCore N fresh anchors z w) := fun r hr =>
    Or.inl (Or.inr (smul_mem_walkVertices_meshEar hN hfresh anchors hz hw hzw hr).1)
  have hwK : ∀ r ∈ meshRadii N, r • w ∈ V(meshCore N fresh anchors z w) := fun r hr =>
    Or.inl (Or.inr (smul_mem_walkVertices_meshEar hN hfresh anchors hz hw hzw hr).2)
  have hrings := attachRings_isTwoConnected hN hfresh hz hw hzw hcore hcorele hzK hwK
    (l := meshRadii N) fun _ hx => hx
  refine attachSpokes_isTwoConnected hN hfresh hrings
    (attachRings_le hcorele (meshRadii N)) ?_ ?_ fun _ hx => hx
  · exact fun u hu => (le_attachRings N fresh anchors _ (meshRadii N)).vertexSet_mono
      (Or.inl (Or.inl (mem_vertexSet_ringGraph_one hN hfresh anchors hu)))
  · exact fun u hu => (le_attachRings N fresh anchors _ (meshRadii N)).vertexSet_mono
      (Or.inr (smul_mem_vertexSet_ringGraph hN hfresh anchors hu (inv_mem_meshRadii hN)))

 


theorem vertexSet_meshGraph_subset_meshAssembly {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    V(meshGraph N fresh anchors) ⊆ V(meshAssembly N fresh anchors z w) := by
  have hcorele := meshCore_le hN hfresh anchors hz hw hzw
  intro v hv
  obtain ⟨Q, hQ, hvQ⟩ := meshGraph_mem_vertexSet.1 hv
  obtain ⟨R, hR, hsub⟩ := meshGraph_edge_source hQ
  have hvseg : v ∈ Q.seg := by
    rcases hvQ with rfl | rfl
    exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
  have hvR : v ∈ R.seg := hsub hvseg
  have hvp : v ∈ meshPoints N fresh anchors :=
    overlayPieces_ends_cut (meshPoints_endsAreCut N fresh anchors) Q hQ v hvQ
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨u, hu, rfl⟩
  · 
    have hvring : v ∈ V(ringGraph N fresh anchors r) :=
      mem_vertexSet_ringGraph hN hfresh hr hvp
        (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr hvR)
    exact (le_attachSpokes N fresh anchors _ fresh).vertexSet_mono
      ((ringGraph_le_attachRings hcorele hr).vertexSet_mono hvring)
  · 
    have hvwalk : v ∈ (meshGraph N fresh anchors).walkVertices u (spokeWalk N fresh anchors u) :=
      mem_walkVertices_of_mem_points (meshSegments_nondeg hN hfresh)
        (spokePiece_mem_meshSegments hu) (spokeWalk_spec hN hfresh anchors hu).2 hvp hvR
    exact (spokeGraph_le_attachSpokes (l := fresh)
      (attachRings_le hcorele (meshRadii N)) hN hfresh (fun _ hx => hx) hu).vertexSet_mono hvwalk

 




theorem meshGraph_isTwoConnected {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ x ∈ fresh, x ∈ modelCurve) (anchors : List Plane) {z w : Plane}
    (hz : z ∈ fresh) (hw : w ∈ fresh) (hzw : z ≠ w) :
    (meshGraph N fresh anchors).IsTwoConnected :=
  (meshAssembly_isTwoConnected hN hfresh anchors hz hw hzw).of_le_of_vertexSet_subset
    (meshAssembly_le hN hfresh anchors hz hw hzw)
    (vertexSet_meshGraph_subset_meshAssembly hN hfresh anchors hz hw hzw)

 





theorem squareMesh_isTwoConnected {fresh : List Plane} (hfresh : ∀ x ∈ fresh, x ∈ modelCurve)
    {δ : ℝ} (hdense : FreshDense fresh δ) (hδ : δ < 4) (anchors : List Plane) :
    (squareMesh δ fresh anchors).IsTwoConnected := by
  obtain ⟨z, hz, w, hw, hzw⟩ := exists_two_distinct_fresh_of_freshDense hdense hδ
  exact meshGraph_isTwoConnected (two_le_meshCount δ) hfresh anchors hz hw hzw

end Schoenflies
