/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/GridAttach.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.LocalGrid
import FiniteAvalanches.Support.Schoenflies.Graph.Ear
import FiniteAvalanches.Support.Schoenflies.Line
import FiniteAvalanches.Support.Schoenflies.PolygonalCarrier

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





































































open Metric Set
open scoped Graph

 









namespace Graph

variable {α β : Type*} {G H : Graph α β} {u v x y : α} {e : β} {X : Set α}

 

def SameLinks (G H : Graph α β) : Prop :=
  V(G) = V(H) ∧ ∀ x y, (∃ e, G.IsLink e x y) ↔ (∃ e, H.IsLink e x y)

namespace SameLinks

@[refl] theorem refl (G : Graph α β) : SameLinks G G := ⟨rfl, fun _ _ => Iff.rfl⟩

theorem symm (h : SameLinks G H) : SameLinks H G := ⟨h.1.symm, fun x y => (h.2 x y).symm⟩

theorem vertexSet (h : SameLinks G H) : V(G) = V(H) := h.1

 

theorem deleteVerts (h : SameLinks G H) (X : Set α) :
    SameLinks (G.deleteVerts X) (H.deleteVerts X) := by
  refine ⟨by rw [vertexSet_deleteVerts, vertexSet_deleteVerts, h.1], fun x y => ?_⟩
  constructor
  · rintro ⟨e, he⟩
    rw [deleteVerts_isLink _ _] at he
    obtain ⟨f, hf⟩ := (h.2 x y).1 ⟨e, he.1⟩
    exact ⟨f, (deleteVerts_isLink _ _).2 ⟨hf, he.2.1, he.2.2⟩⟩
  · rintro ⟨e, he⟩
    rw [deleteVerts_isLink _ _] at he
    obtain ⟨f, hf⟩ := (h.2 x y).2 ⟨e, he.1⟩
    exact ⟨f, (deleteVerts_isLink _ _).2 ⟨hf, he.2.1, he.2.2⟩⟩

end SameLinks

 
theorem Reaches.sameLinks (h : SameLinks G H) (hr : G.Reaches u v) : H.Reaches u v := by
  obtain ⟨W, hW⟩ := hr
  induction hW with
  | nil hz => exact Reaches.refl (h.1 ▸ hz)
  | @cons p w q g R hl _ ih =>
    obtain ⟨f, hf⟩ := (h.2 p w).1 ⟨g, hl⟩
    exact (Reaches.of_isLink hf).trans ih

theorem Connected.sameLinks (h : SameLinks G H) (hG : G.Connected) : H.Connected := by
  obtain ⟨z, hz⟩ := hG.nonempty
  exact Connected.of_hub (h.1 ▸ hz) fun w hw =>
    (hG.reaches hz (h.1 ▸ hw : w ∈ V(G))).sameLinks h

theorem HasThreeVertices.sameLinks (h : SameLinks G H) (hG : G.HasThreeVertices) :
    H.HasThreeVertices := hG.mono (le_of_eq h.1)

 
theorem IsTwoConnected.sameLinks (h : SameLinks G H) (hG : G.IsTwoConnected) :
    H.IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.sameLinks h
  connected := hG.connected.sameLinks h
  deleteVerts_connected := fun z _ =>
    (hG.deleteVerts_connected' z).sameLinks (h.deleteVerts {z})

end Graph

namespace Schoenflies

 







 
theorem overlayGraph_eq_pieceListGraph (pieces : List Piece) (points : List Plane) :
    overlayGraph pieces points = pieceListGraph (overlayPieces pieces points) := rfl

 

 
theorem orientPiece_link_iff (P : Piece) (x y : Plane) :
    ((x = (orientPiece P).1 ∧ y = (orientPiece P).2) ∨
        (x = (orientPiece P).2 ∧ y = (orientPiece P).1)) ↔
      ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact or_comm

 


theorem sameLinks_overlayGraph (pieces : List Piece) (points : List Plane) :
    Graph.SameLinks (pieceListGraph (subdivide pieces points)) (overlayGraph pieces points) := by
  constructor
  · ext v
    simp only [pieceListGraph_vertexSet, overlayGraph_vertexSet, endSet, mem_setOf_eq]
    constructor
    · rintro ⟨P, hP, hv⟩
      exact ⟨orientPiece P, mem_overlayPieces.2 ⟨P, hP, rfl⟩, (orientPiece_ends P v).2 hv⟩
    · rintro ⟨P, hP, hv⟩
      obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
      exact ⟨Q, hQ, (orientPiece_ends Q v).1 hv⟩
  · intro x y
    simp only [pieceListGraph_isLink, overlayGraph_isLink]
    constructor
    · rintro ⟨P, hP, hxy⟩
      exact ⟨orientPiece P, mem_overlayPieces.2 ⟨P, hP, rfl⟩,
        (orientPiece_link_iff P x y).2 hxy⟩
    · rintro ⟨P, hP, hxy⟩
      obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
      exact ⟨Q, hQ, (orientPiece_link_iff Q x y).1 hxy⟩

 





theorem overlayGraph_isTwoConnected {pieces : List Piece} {points : List Plane}
    (h : (pieceListGraph (subdivide pieces points)).IsTwoConnected) :
    (overlayGraph pieces points).IsTwoConnected :=
  h.sameLinks (sameLinks_overlayGraph pieces points)

 
theorem overlayGraph_isTwoConnected_of_cleanCut {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hclean : ∀ q ∈ points, CleanCut pieces q)
    (h : (pieceListGraph pieces).IsTwoConnected) :
    (overlayGraph pieces points).IsTwoConnected :=
  overlayGraph_isTwoConnected (pieceListGraph_subdivide_isTwoConnected points pieces hnd hclean h)

 





theorem splitAllAt_append (q : Plane) (l l' : List Piece) :
    splitAllAt q (l ++ l') = splitAllAt q l ++ splitAllAt q l' := by
  simp [splitAllAt, List.flatMap_append]

theorem subdivide_append (points : List Plane) : ∀ l l' : List Piece,
    subdivide (l ++ l') points = subdivide l points ++ subdivide l' points := by
  induction points with
  | nil => intro l l'; rfl
  | cons q qs ih => intro l l'; rw [subdivide_cons, splitAllAt_append, ih, subdivide_cons,
      subdivide_cons]

theorem endSet_subset_append_left {l l' : List Piece} : endSet l ⊆ endSet (l ++ l') := by
  rintro v ⟨P, hP, hv⟩
  exact ⟨P, List.mem_append_left _ hP, hv⟩

 




 
theorem mem_endSet_subdivide_of_mem_cover {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) {x : Plane} (hxp : x ∈ points) (hx : x ∈ cover pieces) :
    x ∈ endSet (subdivide pieces points) := by
  rw [← subdivide_cover pieces points] at hx
  obtain ⟨P, hP, hxP⟩ := mem_cover_iff.1 hx
  refine ⟨P, hP, ?_⟩
  by_contra hcon
  push Not at hcon
  exact subdivide_avoids points hnd x hxp P hP
    (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

 





 






theorem overlayGraph_append_isTwoConnected {l l' : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ l, P.Nondeg) (hnd' : ∀ P ∈ l', P.Nondeg)
    (hl : (pieceListGraph (subdivide l points)).IsTwoConnected)
    (hl' : (pieceListGraph (subdivide l' points)).IsTwoConnected)
    {a b : Plane} (hab : a ≠ b) (ha : a ∈ points) (hb : b ∈ points)
    (hal : a ∈ cover l) (hbl : b ∈ cover l) (hal' : a ∈ cover l') (hbl' : b ∈ cover l') :
    (overlayGraph (l ++ l') points).IsTwoConnected := by
  refine overlayGraph_isTwoConnected ?_
  rw [subdivide_append, ← pieceListGraph_union]
  exact hl.union (pieceListGraph_compatible _ _) hl' hab
    (mem_endSet_subdivide_of_mem_cover hnd ha hal)
    (mem_endSet_subdivide_of_mem_cover hnd' ha hal')
    (mem_endSet_subdivide_of_mem_cover hnd hb hbl)
    (mem_endSet_subdivide_of_mem_cover hnd' hb hbl')

 












variable {F : Set Plane} {a b y : Plane}

 



theorem exists_crosscut (hab : a ≠ b) (hFopen : IsOpen F) (hFbdd : Bornology.IsBounded F)
    (hy : y ∈ Plane.line a b ∩ F) :
    ∃ q₀ q₁ : Plane, q₀ ≠ q₁ ∧ q₀ ∈ frontier F ∧ q₁ ∈ frontier F ∧
      openSegment ℝ q₀ q₁ ⊆ F ∧ y ∈ openSegment ℝ q₀ q₁ ∧
      ∀ S : Set Plane, IsPreconnected S → S ⊆ Plane.line a b ∩ F → y ∈ S →
        S ⊆ openSegment ℝ q₀ q₁ := by
  obtain ⟨q₀, q₁, hne, -, -, hcomp, -, h0, h1⟩ :=
    Plane.exists_openSegment_eq_connectedComponentIn hab hFopen hFbdd hy
  refine ⟨q₀, q₁, hne, h0, h1, ?_, ?_, ?_⟩
  · rw [← hcomp]
    exact fun z hz => (connectedComponentIn_subset _ _ hz).2
  · rw [← hcomp]
    exact mem_connectedComponentIn hy
  · intro S hS hSsub hyS
    rw [← hcomp]
    exact hS.subset_connectedComponentIn hyS hSsub

 

theorem frontier_face_subset_pointSet {β : Type*} {G : Graph Plane β} [G.Finite]
    {drawing : β → ℝ → Plane} (h : Graph.IsDrawing G drawing) (base : Plane) :
    frontier (Graph.face G drawing base) ⊆ Graph.pointSet G drawing :=
  Plane.frontier_connectedComponentIn_compl_subset h.isClosed_pointSet base

 





 
theorem isPathGraph_single {q₀ q₁ : Plane} (hne : q₀ ≠ q₁) :
    (pieceListGraph [(q₀, q₁)]).IsPathGraph q₀ [(q₀, q₁)] q₁ where
  isPath := .single (pieceListGraph_isLink_self (by simp)) hne
  edgeSet_eq := rfl
  vertexSet_eq := by
    have hmem : ((q₀, q₁) : Piece) ∈ [((q₀, q₁) : Piece)] := List.mem_singleton_self _
    ext x
    constructor
    · rintro ⟨P, hP, hx⟩
      rw [List.mem_singleton] at hP
      subst hP
      simp only [Graph.walkVertices, mem_insert_iff, Graph.coveredVertices, mem_setOf_eq]
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨(q₀, q₁), hmem, pieceListGraph_inc hmem (Or.inr h)⟩
    · intro hx
      simp only [Graph.walkVertices, mem_insert_iff, Graph.coveredVertices, mem_setOf_eq] at hx
      rcases hx with h | ⟨e, he, hinc⟩
      · exact ⟨(q₀, q₁), hmem, Or.inl h⟩
      · rw [List.mem_singleton] at he
        subst he
        obtain ⟨-, hx'⟩ := pieceListGraph_inc_iff.1 hinc
        exact ⟨(q₀, q₁), hmem, hx'⟩

 

theorem pieceListGraph_append_crosscut {l : List Piece} {q₀ q₁ : Plane}
    (hl : (pieceListGraph l).IsTwoConnected) (hne : q₀ ≠ q₁)
    (h0 : q₀ ∈ endSet l) (h1 : q₁ ∈ endSet l) :
    (pieceListGraph (l ++ [(q₀, q₁)])).IsTwoConnected := by
  rw [← pieceListGraph_union]
  exact hl.ear (pieceListGraph_compatible _ _) (isPathGraph_single hne) hne h0 h1

 











 






theorem isConnected_union_joins {A : Set Plane} {r₀ : Plane} (hr₀ : r₀ ∈ A)
    {reps : List Plane} {T : Plane → Set Plane}
    (hTconn : ∀ r ∈ reps, IsPreconnected (T r))
    (hThub : ∀ r ∈ reps, r₀ ∈ T r) (hTrep : ∀ r ∈ reps, r ∈ T r)
    (hcover : ∀ z ∈ A, ∃ r ∈ reps, ∃ S : Set Plane,
      S ⊆ A ∧ IsPreconnected S ∧ z ∈ S ∧ r ∈ S) :
    IsConnected (A ∪ ⋃ r ∈ reps, T r) := by
  have hmem : r₀ ∈ A ∪ ⋃ r ∈ reps, T r := Or.inl hr₀
  refine ⟨⟨r₀, hmem⟩, isPreconnected_of_forall r₀ ?_⟩
  rintro z (hz | hz)
  · 
    obtain ⟨r, hr, S, hSA, hSconn, hzS, hrS⟩ := hcover z hz
    refine ⟨S ∪ T r, ?_, Or.inr (hThub r hr), Or.inl hzS,
      hSconn.union' ⟨r, hrS, hTrep r hr⟩ (hTconn r hr)⟩
    exact union_subset (hSA.trans subset_union_left)
      (fun w hw => Or.inr (mem_biUnion hr hw))
  · 
    simp only [mem_iUnion, exists_prop] at hz
    obtain ⟨r, hr, hzT⟩ := hz
    exact ⟨T r, fun w hw => Or.inr (mem_biUnion hr hw), hThub r hr, hzT, hTconn r hr⟩

 





 



noncomputable def attachPoints (pieces : List Piece) (extra : List Plane) : List Plane :=
  extra ++ (exists_cut_points pieces).choose

theorem mem_attachPoints_of_mem {pieces : List Piece} {extra : List Plane} {x : Plane}
    (hx : x ∈ extra) : x ∈ attachPoints pieces extra := List.mem_append_left _ hx

theorem attachPoints_endsAreCut (pieces : List Piece) (extra : List Plane) :
    EndsAreCut pieces (attachPoints pieces extra) :=
  (exists_cut_points pieces).choose_spec.1.mono (List.subset_append_right _ _)

theorem attachPoints_meetsAreCut (pieces : List Piece) (extra : List Plane) :
    MeetsAreCut pieces (attachPoints pieces extra) :=
  (exists_cut_points pieces).choose_spec.2.mono (List.subset_append_right _ _)

 


noncomputable def attachGraph (pieces : List Piece) (extra : List Plane) : Graph Plane Piece :=
  overlayGraph pieces (attachPoints pieces extra)

instance attachGraph_finite (pieces : List Piece) (extra : List Plane) :
    Graph.Finite (attachGraph pieces extra) := overlayGraph_finite _ _

theorem attachGraph_isDrawing {pieces : List Piece} (hnd : ∀ P ∈ pieces, P.Nondeg)
    (extra : List Plane) : Graph.IsDrawing (attachGraph pieces extra) segmentDrawing :=
  overlayGraph_isDrawing _ _ hnd (attachPoints_endsAreCut _ _) (attachPoints_meetsAreCut _ _)

@[simp] theorem attachGraph_pointSet (pieces : List Piece) (extra : List Plane) :
    Graph.pointSet (attachGraph pieces extra) segmentDrawing = cover pieces :=
  overlayGraph_pointSet _ _

 



theorem attachGraph_isTwoConnected {l l' : List Piece} {extra : List Plane}
    (hnd : ∀ P ∈ l, P.Nondeg) (hnd' : ∀ P ∈ l', P.Nondeg)
    (hl : (pieceListGraph (subdivide l (attachPoints (l ++ l') extra))).IsTwoConnected)
    (hl' : (pieceListGraph (subdivide l' (attachPoints (l ++ l') extra))).IsTwoConnected)
    {a b : Plane} (hab : a ≠ b) (ha : a ∈ extra) (hb : b ∈ extra)
    (hal : a ∈ cover l) (hbl : b ∈ cover l) (hal' : a ∈ cover l') (hbl' : b ∈ cover l') :
    (attachGraph (l ++ l') extra).IsTwoConnected :=
  overlayGraph_append_isTwoConnected hnd hnd' hl hl' hab
    (mem_attachPoints_of_mem ha) (mem_attachPoints_of_mem hb) hal hbl hal' hbl'

 




 


theorem isConnected_cover_diff_of_joins {l : List Piece} {C : Set Plane} {r₀ : Plane}
    {reps : List Plane} {J : Plane → List Piece} (hr₀ : r₀ ∈ cover l \ C)
    (hJconn : ∀ r ∈ reps, IsPreconnected (cover (J r)))
    (hJhub : ∀ r ∈ reps, r₀ ∈ cover (J r)) (hJrep : ∀ r ∈ reps, r ∈ cover (J r))
    (hJC : ∀ r ∈ reps, ∀ z ∈ cover (J r), z ∉ C)
    (hcov : ∀ z ∈ cover l \ C, ∃ r ∈ reps, ∃ S : Set Plane,
      S ⊆ cover l \ C ∧ IsPreconnected S ∧ z ∈ S ∧ r ∈ S) :
    IsConnected (cover (l ++ reps.flatMap J) \ C) := by
  have hEq : cover (l ++ reps.flatMap J) \ C = (cover l \ C) ∪ ⋃ r ∈ reps, cover (J r) := by
    rw [cover_append, cover_flatMap']
    ext z
    simp only [Set.mem_sdiff, mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz | ⟨r, hr, hz⟩, hzC⟩
      · exact Or.inl ⟨hz, hzC⟩
      · exact Or.inr ⟨r, hr, hz⟩
    · rintro (⟨hz, hzC⟩ | ⟨r, hr, hz⟩)
      · exact ⟨Or.inl hz, hzC⟩
      · exact ⟨Or.inr ⟨r, hr, hz⟩, hJC r hr z hz⟩
  rw [hEq]
  exact isConnected_union_joins hr₀ hJconn hJhub hJrep hcov

 

theorem localGridEdges_nondeg {p : Plane} {s : ℝ} {k : ℕ} (hs : 0 < s) (hk : 1 ≤ k) :
    ∀ P ∈ localGridEdges p s k, P.Nondeg := fun _ hP =>
  gridEdges_nondeg ((localGridX_strictMono hs hk).strictMonoOn _)
    ((localGridY_strictMono hs hk).strictMonoOn _) hk hk hP

 

theorem localGrid_subset_attachGraph_pointSet {p : Plane} {s : ℝ} {k : ℕ} (l : List Piece)
    (extra : List Plane) :
    cover (localGridEdges p s k) ⊆
      Graph.pointSet (attachGraph (l ++ localGridEdges p s k) extra) segmentDrawing := by
  rw [attachGraph_pointSet, cover_append]
  exact subset_union_right

 

theorem attachGraph_localGridCell_diam {p : Plane} {s ε : ℝ} (hε : 0 < ε) (i j : ℕ)
    {x y : Plane} (hx : x ∈ localGridCell p s (localGridCount s ε) i j)
    (hy : y ∈ localGridCell p s (localGridCount s ε) i j) : dist x y < ε :=
  lt_of_le_of_lt (dist_le_of_mem_localGridCell hx hy) (localGridCount_spec hε)

 







 
theorem seg_subset_crosscut {q₀ q₁ : Plane} {J : Piece}
    (hswallow : ∀ S : Set Plane, IsPreconnected S → S ⊆ Plane.line a b ∩ F → y ∈ S →
      S ⊆ openSegment ℝ q₀ q₁)
    (hJline : J.interior ⊆ Plane.line a b ∩ F) (hy : y ∈ J.interior) :
    J.seg ⊆ segment ℝ q₀ q₁ := by
  have h1 : J.interior ⊆ openSegment ℝ q₀ q₁ :=
    hswallow _ (convex_openSegment _ _).isPreconnected hJline hy
  calc J.seg = closure J.interior := (closure_openSegment _ _).symm
    _ ⊆ closure (openSegment ℝ q₀ q₁) := closure_mono h1
    _ = segment ℝ q₀ q₁ := closure_openSegment _ _

 

theorem mem_cover_append_crosscut {l : List Piece} {q₀ q₁ z : Plane}
    (hz : z ∈ segment ℝ q₀ q₁) : z ∈ cover (l ++ [(q₀, q₁)]) := by
  rw [cover_append]
  exact Or.inr (mem_cover_iff.2 ⟨(q₀, q₁), List.mem_singleton_self _, hz⟩)

 
theorem left_mem_cover {l : List Piece} {P : Piece} (hP : P ∈ l) : P.1 ∈ cover l :=
  mem_cover_iff.2 ⟨P, hP, left_mem_segment ℝ _ _⟩

theorem right_mem_cover {l : List Piece} {P : Piece} (hP : P ∈ l) : P.2 ∈ cover l :=
  mem_cover_iff.2 ⟨P, hP, right_mem_segment ℝ _ _⟩

 






theorem two_common_of_crosscut {l l' : List Piece} {q₀ q₁ : Plane} {J : Piece}
    (hJ : J ∈ l') (hJnd : J.Nondeg)
    (hswallow : ∀ S : Set Plane, IsPreconnected S → S ⊆ Plane.line a b ∩ F → y ∈ S →
      S ⊆ openSegment ℝ q₀ q₁)
    (hJline : J.interior ⊆ Plane.line a b ∩ F) (hy : y ∈ J.interior) :
    J.1 ≠ J.2 ∧ J.1 ∈ cover (l ++ [(q₀, q₁)]) ∧ J.2 ∈ cover (l ++ [(q₀, q₁)]) ∧
      J.1 ∈ cover l' ∧ J.2 ∈ cover l' := by
  have hsub := seg_subset_crosscut hswallow hJline hy
  exact ⟨hJnd, mem_cover_append_crosscut (hsub (left_mem_segment ℝ _ _)),
    mem_cover_append_crosscut (hsub (right_mem_segment ℝ _ _)),
    left_mem_cover hJ, right_mem_cover hJ⟩

 





theorem cover_swap (l₁ l₂ l₃ : List Piece) :
    cover ((l₁ ++ l₂) ++ l₃) = cover ((l₁ ++ l₃) ++ l₂) := by
  simp only [cover_append]
  ac_rfl

 


noncomputable def gridAttachPieces (gsegs : List Piece) (reps : List Plane)
    (Jarc : Plane → List Piece) (p : Plane) (s ε : ℝ) : List Piece :=
  (gsegs ++ reps.flatMap Jarc) ++ localGridEdges p s (localGridCount s ε)

 
noncomputable def gridAttachGraph (gsegs : List Piece) (reps : List Plane)
    (Jarc : Plane → List Piece) (p : Plane) (s ε : ℝ) (extra : List Plane) : Graph Plane Piece :=
  attachGraph (gridAttachPieces gsegs reps Jarc p s ε) extra

variable {gsegs : List Piece} {reps : List Plane} {Jarc : Plane → List Piece} {p : Plane}
  {s ε : ℝ} {extra : List Plane} {C : Set Plane} {r₀ : Plane}

instance gridAttachGraph_finite (gsegs : List Piece) (reps : List Plane)
    (Jarc : Plane → List Piece) (p : Plane) (s ε : ℝ) (extra : List Plane) :
    Graph.Finite (gridAttachGraph gsegs reps Jarc p s ε extra) := attachGraph_finite _ _

 
theorem gridAttachPieces_nondeg (hs : 0 < s)
    (hg : ∀ P ∈ gsegs, P.Nondeg) (hj : ∀ P ∈ reps.flatMap Jarc, P.Nondeg) :
    ∀ P ∈ gridAttachPieces gsegs reps Jarc p s ε, P.Nondeg := by
  intro P hP
  rcases List.mem_append.1 hP with hP' | hP'
  · rcases List.mem_append.1 hP' with hP'' | hP''
    exacts [hg P hP'', hj P hP'']
  · exact localGridEdges_nondeg hs (one_le_localGridCount s ε) P hP'

 
theorem gridAttachGraph_isDrawing (hs : 0 < s)
    (hg : ∀ P ∈ gsegs, P.Nondeg) (hj : ∀ P ∈ reps.flatMap Jarc, P.Nondeg) :
    Graph.IsDrawing (gridAttachGraph gsegs reps Jarc p s ε extra) segmentDrawing :=
  attachGraph_isDrawing (gridAttachPieces_nondeg hs hg hj) extra

@[simp] theorem gridAttachGraph_pointSet :
    Graph.pointSet (gridAttachGraph gsegs reps Jarc p s ε extra) segmentDrawing =
      cover (gridAttachPieces gsegs reps Jarc p s ε) := attachGraph_pointSet _ _

 
theorem localGrid_subset_gridAttachGraph :
    cover (localGridEdges p s (localGridCount s ε)) ⊆
      Graph.pointSet (gridAttachGraph gsegs reps Jarc p s ε extra) segmentDrawing := by
  rw [gridAttachGraph_pointSet, gridAttachPieces, cover_append]
  exact subset_union_right

 








theorem gridAttachGraph_isTwoConnected (hs : 0 < s)
    (hg : ∀ P ∈ gsegs, P.Nondeg) (hj : ∀ P ∈ reps.flatMap Jarc, P.Nondeg)
    (hΓ : (pieceListGraph (subdivide (gsegs ++ reps.flatMap Jarc)
      (attachPoints (gridAttachPieces gsegs reps Jarc p s ε) extra))).IsTwoConnected)
    (hK : (pieceListGraph (subdivide (localGridEdges p s (localGridCount s ε))
      (attachPoints (gridAttachPieces gsegs reps Jarc p s ε) extra))).IsTwoConnected)
    {a b : Plane} (hab : a ≠ b) (ha : a ∈ extra) (hb : b ∈ extra)
    (haΓ : a ∈ cover (gsegs ++ reps.flatMap Jarc))
    (hbΓ : b ∈ cover (gsegs ++ reps.flatMap Jarc))
    (haK : a ∈ cover (localGridEdges p s (localGridCount s ε)))
    (hbK : b ∈ cover (localGridEdges p s (localGridCount s ε))) :
    (gridAttachGraph gsegs reps Jarc p s ε extra).IsTwoConnected := by
  refine attachGraph_isTwoConnected (fun P hP => ?_)
    (localGridEdges_nondeg hs (one_le_localGridCount s ε)) hΓ hK hab ha hb haΓ hbΓ haK hbK
  rcases List.mem_append.1 hP with hP' | hP'
  exacts [hg P hP', hj P hP']

 



theorem gridAttachGraph_isConnected_diff
    (hr₀ : r₀ ∈ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C)
    (hJconn : ∀ r ∈ reps, IsPreconnected (cover (Jarc r)))
    (hJhub : ∀ r ∈ reps, r₀ ∈ cover (Jarc r)) (hJrep : ∀ r ∈ reps, r ∈ cover (Jarc r))
    (hJC : ∀ r ∈ reps, ∀ z ∈ cover (Jarc r), z ∉ C)
    (hcov : ∀ z ∈ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C,
      ∃ r ∈ reps, ∃ S : Set Plane, S ⊆ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C
        ∧ IsPreconnected S ∧ z ∈ S ∧ r ∈ S) :
    IsConnected
      (Graph.pointSet (gridAttachGraph gsegs reps Jarc p s ε extra) segmentDrawing \ C) := by
  rw [gridAttachGraph_pointSet, gridAttachPieces, cover_swap]
  exact isConnected_cover_diff_of_joins hr₀ hJconn hJhub hJrep hJC hcov

end Schoenflies
