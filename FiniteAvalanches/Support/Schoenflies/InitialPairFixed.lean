/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/InitialPairFixed.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.InitialPair
import FiniteAvalanches.Support.Schoenflies.JordanClosed
import FiniteAvalanches.Support.Schoenflies.BoundaryCycles

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 






































































open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

 



theorem forall_isSeparating_of_isJordanCurve : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S :=
  fun _ h => jordan_curve_theorem h

 





namespace HexData

variable (H : HexData)




theorem arcOf_false :
    H.arcOf false = H.outer 1 '' I ∪ (H.outer 2 '' I ∪ H.outer 3 '' I) := rfl

theorem arcOf_true :
    H.arcOf true = H.outer 4 '' I ∪ (H.outer 5 '' I ∪ H.outer 0 '' I) := rfl

theorem arcOf_subset_outerArcs (k : Bool) : H.arcOf k ⊆ H.outerArcs := by
  rw [← H.arcOf_union]
  cases k
  exacts [Set.subset_union_left, Set.subset_union_right]

 
theorem pos_mem_outer_of_succ {i j : Fin 6} (h : i + 1 = j) : H.pos j ∈ H.outer i '' I := by
  subst h; exact H.pos_succ_mem_outer i

 

theorem isPolygonal_arcOf (hp : ∀ i, IsPolygonal (H.outer i '' I)) (k : Bool) :
    IsPolygonal (H.arcOf k) := by
  cases k
  · rw [H.arcOf_false]
    refine (hp 1).union ((hp 2).union (hp 3)
      ⟨H.pos 3, H.pos_mem_outer_of_succ (by decide), H.pos_mem_outer 3⟩) ?_
    exact ⟨H.pos 2, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 2)⟩
  · rw [H.arcOf_true]
    refine (hp 4).union ((hp 5).union (hp 0)
      ⟨H.pos 0, H.pos_mem_outer_of_succ (by decide), H.pos_mem_outer 0⟩) ?_
    exact ⟨H.pos 5, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 5)⟩

 
theorem isPolygonal_outerArcs (hp : ∀ i, IsPolygonal (H.outer i '' I)) :
    IsPolygonal H.outerArcs := by
  rw [H.outerArcs_eq]
  have h45 : IsPolygonal (H.outer 4 '' I ∪ H.outer 5 '' I) :=
    (hp 4).union (hp 5) ⟨H.pos 5, H.pos_mem_outer_of_succ (by decide), H.pos_mem_outer 5⟩
  have h345 := (hp 3).union h45
    ⟨H.pos 4, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 4)⟩
  have h2345 := (hp 2).union h345
    ⟨H.pos 3, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 3)⟩
  have h12345 := (hp 1).union h2345
    ⟨H.pos 2, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 2)⟩
  exact (hp 0).union h12345
    ⟨H.pos 1, H.pos_mem_outer_of_succ (by decide), Or.inl (H.pos_mem_outer 1)⟩

end HexData

 

theorem isPolygonal_modelCurve : IsPolygonal modelCurve := by
  have h : |(0 : ℝ)| < 1 := by norm_num
  have hp : ∀ i, IsPolygonal ((targetHex h h).outer i '' I) := by
    intro i
    change IsPolygonal (tgtOuter 0 0 i '' I)
    rw [tgtOuter_image]
    exact isPolygonal_segment _ _
  have hpoly := (targetHex h h).isPolygonal_outerArcs hp
  rwa [targetHex_outerArcs h h] at hpoly

 






 
theorem initSkel_isLink_edge {i j : Fin 6} (h : i + 1 = j) :
    initSkel.IsLink (.edge i) (.vert i) (.vert j) := by
  subst h; exact initSkel_isLink_ends (InitialCell.edge_mem_edges i)

 
theorem initSkel_isLink_chord : initSkel.IsLink .chord (.vert 1) (.vert 4) :=
  initSkel_isLink_ends InitialCell.chord_mem_edges

 
theorem isWalk_initBoundary_false :
    initSkel.IsWalk (.vert 1) (initBoundary (.face false)) (.vert 1) := by
  change initSkel.IsWalk (.vert 1) [.edge 1, .edge 2, .edge 3, .chord] (.vert 1)
  exact .cons (initSkel_isLink_edge (by decide : (1 : Fin 6) + 1 = 2))
    (.cons (initSkel_isLink_edge (by decide : (2 : Fin 6) + 1 = 3))
      (.cons (initSkel_isLink_edge (by decide : (3 : Fin 6) + 1 = 4))
        (.cons initSkel_isLink_chord.symm (.nil (InitialCell.vert_mem_vertices 1)))))

 
theorem isWalk_initBoundary_true :
    initSkel.IsWalk (.vert 4) (initBoundary (.face true)) (.vert 4) := by
  change initSkel.IsWalk (.vert 4) [.edge 4, .edge 5, .edge 0, .chord] (.vert 4)
  exact .cons (initSkel_isLink_edge (by decide : (4 : Fin 6) + 1 = 5))
    (.cons (initSkel_isLink_edge (by decide : (5 : Fin 6) + 1 = 0))
      (.cons (initSkel_isLink_edge (by decide : (0 : Fin 6) + 1 = 1))
        (.cons initSkel_isLink_chord (.nil (InitialCell.vert_mem_vertices 4)))))

 
theorem exists_isWalk_initBoundary (k : Bool) :
    ∃ v, initSkel.IsWalk v (initialStructure.boundary (.face k)) v := by
  cases k
  exacts [⟨_, isWalk_initBoundary_false⟩, ⟨_, isWalk_initBoundary_true⟩]

 
theorem initSkel_inc_iff {e x : InitialCell} :
    initSkel.Inc e x ↔ e ∈ InitialCell.edges ∧ (x = e.ends.1 ∨ x = e.ends.2) := by
  constructor
  · rintro ⟨y, hy⟩
    rw [initSkel_isLink] at hy
    rcases hy.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [⟨hy.1, Or.inl rfl⟩, ⟨hy.1, Or.inr rfl⟩]
  · rintro ⟨he, rfl | rfl⟩
    exacts [⟨_, initSkel_isLink_ends he⟩, ⟨_, (initSkel_isLink_ends he).symm⟩]

 


theorem mem_faceCells_iff {k : Bool} {c : InitialCell} :
    c ∈ faceCells k ↔
      c ∈ initBoundary (.face k) ∨ ∃ e ∈ initBoundary (.face k), initSkel.Inc e c := by
  have hedge : ∀ i j : Fin 6, i + 1 = j → ∀ x : InitialCell,
      initSkel.Inc (.edge i) x ↔ (x = .vert i ∨ x = .vert j) := by
    rintro i j rfl x
    rw [initSkel_inc_iff]
    exact ⟨fun h => h.2, fun h => ⟨InitialCell.edge_mem_edges i, h⟩⟩
  have hchord : ∀ x : InitialCell,
      initSkel.Inc .chord x ↔ (x = .vert 1 ∨ x = .vert 4) := by
    intro x
    rw [initSkel_inc_iff]
    exact ⟨fun h => h.2, fun h => ⟨InitialCell.chord_mem_edges, h⟩⟩
  cases k <;>
    simp only [faceCells, initBoundary, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left,
      hedge 1 2 (by decide), hedge 2 3 (by decide), hedge 3 4 (by decide),
      hedge 4 5 (by decide), hedge 5 0 (by decide), hedge 0 1 (by decide), hchord] <;>
    tauto

 





 
theorem isPath_initBoundary_false_tail :
    initSkel.IsPath (.vert 2) [.edge 2, .edge 3, .chord] (.vert 1) := by
  refine .cons (initSkel_isLink_edge (by decide : (2 : Fin 6) + 1 = 3))
    (.cons (initSkel_isLink_edge (by decide : (3 : Fin 6) + 1 = 4))
      (Graph.IsPath.single initSkel_isLink_chord.symm (by simp)) ?_) ?_
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]

 
theorem isPath_initBoundary_true_tail :
    initSkel.IsPath (.vert 5) [.edge 5, .edge 0, .chord] (.vert 4) := by
  refine .cons (initSkel_isLink_edge (by decide : (5 : Fin 6) + 1 = 0))
    (.cons (initSkel_isLink_edge (by decide : (0 : Fin 6) + 1 = 1))
      (Graph.IsPath.single initSkel_isLink_chord (by simp)) ?_) ?_
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]
  · simp [Graph.walkVertices, Graph.coveredVertices, initSkel_inc_iff, InitialCell.ends,
      InitialCell.edges]

 
theorem isLongCycle_initBoundary_false :
    initSkel.IsLongCycle (.edge 1) (.vert 2) (.vert 1)
      [.edge 2, .edge 3, .chord] (.vert 3) where
  isCycle := ⟨(initSkel_isLink_edge (by decide : (1 : Fin 6) + 1 = 2)).symm,
    isPath_initBoundary_false_tail, by simp⟩
  mem := Graph.mem_walkVertices_cons_of_mem
    (initSkel_isLink_edge (by decide : (2 : Fin 6) + 1 = 3))
    Graph.mem_walkVertices_self
  ne_left := by simp
  ne_right := by simp

 
theorem isLongCycle_initBoundary_true :
    initSkel.IsLongCycle (.edge 4) (.vert 5) (.vert 4)
      [.edge 5, .edge 0, .chord] (.vert 0) where
  isCycle := ⟨(initSkel_isLink_edge (by decide : (4 : Fin 6) + 1 = 5)).symm,
    isPath_initBoundary_true_tail, by simp⟩
  mem := Graph.mem_walkVertices_cons_of_mem
    (initSkel_isLink_edge (by decide : (5 : Fin 6) + 1 = 0))
    Graph.mem_walkVertices_self
  ne_left := by simp
  ne_right := by simp

 

theorem initSub_face_iff {k : Bool} {c : InitialCell} :
    initSub c (.face k) ↔ c = .face k ∨ c ∈ faceCells k := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨l, h, hc⟩)
    · exact Or.inl h
    · exact absurd h (by simp [InitialCell.edges])
    · cases h; exact Or.inr hc
  · rintro (rfl | hc)
    · exact initSub_refl (Or.inr ⟨k, rfl⟩)
    · exact initSub_face hc

 

theorem mem_faceCells_iff_mem_pathCells {k : Bool} {u c : InitialCell}
    (hu : ∃ e ∈ initBoundary (.face k), initSkel.Inc e u) :
    c ∈ faceCells k ↔
      c ∈ initialStructure.pathCells u (initBoundary (.face k)) := by
  rw [mem_faceCells_iff]
  simp only [CellStructure.pathCells, Set.mem_union, Set.mem_setOf_eq,
    Graph.mem_walkVertices_iff, Graph.mem_coveredVertices_iff]
  constructor
  · rintro (hc | hc)
    · exact Or.inl hc
    · exact Or.inr (Or.inr hc)
  · rintro (hc | rfl | hc)
    · exact Or.inl hc
    · exact Or.inr hu
    · exact Or.inr hc

 
theorem boundaryCycles_initialStructure : initialStructure.BoundaryCycles where
  cycle F hF := by
    obtain ⟨k, rfl⟩ := hF
    cases k
    · refine ⟨
        { face_mem := ⟨false, rfl⟩
          edge := .edge 1
          source := .vert 2
          target := .vert 1
          walk := [.edge 2, .edge 3, .chord]
          boundary_eq := rfl
          isCycle := isLongCycle_initBoundary_false.isCycle
          sub_face := fun {c} => ?_ }⟩
      rw [initialStructure_sub, initSub_face_iff]
      refine or_congr Iff.rfl (mem_faceCells_iff_mem_pathCells ?_)
      exact ⟨.edge 1, by simp [initBoundary],
        (initSkel_isLink_edge (by decide : (1 : Fin 6) + 1 = 2)).inc_left⟩
    · refine ⟨
        { face_mem := ⟨true, rfl⟩
          edge := .edge 4
          source := .vert 5
          target := .vert 4
          walk := [.edge 5, .edge 0, .chord]
          boundary_eq := rfl
          isCycle := isLongCycle_initBoundary_true.isCycle
          sub_face := fun {c} => ?_ }⟩
      rw [initialStructure_sub, initSub_face_iff]
      refine or_congr Iff.rfl (mem_faceCells_iff_mem_pathCells ?_)
      exact ⟨.edge 4, by simp [initBoundary],
        (initSkel_isLink_edge (by decide : (4 : Fin 6) + 1 = 5)).inc_left⟩

 






variable {C : Set Plane}

 

structure AnchorSet (C : Set Plane) where
   
  carrier : Set Plane
   
  subset_curve : carrier ⊆ C
   
  countable : carrier.Countable
   
  stronglyAccessible : ∀ p ∈ carrier, StronglyAccessible (inside C) p
   
  dense : C ⊆ closure carrier

namespace AnchorSet

variable (A : AnchorSet C)

 
theorem exists_access_segment {p : Plane} (hp : p ∈ A.carrier) :
    ∃ z ∈ inside C, p ≠ z ∧ openSegment ℝ p z ⊆ inside C :=
  (A.stronglyAccessible p hp).openSegment_subset

 


theorem exists_cone {p : Plane} (hp : p ∈ A.carrier) :
    ∃ v : Plane, ‖v‖ = 1 ∧ ∃ r > 0, ∀ s ≤ r, accessCone p v s ⊆ inside C :=
  (A.stronglyAccessible p hp).exists_cone

 
theorem polyAccessible {p : Plane} (hp : p ∈ A.carrier) : PolyAccessible (inside C) p :=
  (A.stronglyAccessible p hp).polyAccessible

end AnchorSet

 

theorem nonempty_anchorSet (hC : IsJordanCurve C) : Nonempty (AnchorSet C) := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  
  have hDmax : ∀ q ∈ inside C, connectedComponentIn Cᶜ q ⊆ inside C := by
    intro q hq z hz
    refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
    rw [← connectedComponentIn_eq hz]
    exact hq.2
  have hCD : C ⊆ closure (inside C) := by
    intro x hx
    have hxf : x ∈ frontier (inside C) := by rw [hsep.frontier_inside]; exact hx
    exact hxf.1
  obtain ⟨A, hAC, hAcount, hAacc, hCA⟩ := exists_countable_dense_stronglyAccessible hC.isCompact
    hC.nonempty hsep.isOpen_inside inside_subset_compl hDmax hCD
  exact ⟨⟨A, hAC, hAcount, hAacc, hCA⟩⟩

open Classical in
 
noncomputable def anchorSet (hC : IsJordanCurve C) : AnchorSet C := (nonempty_anchorSet hC).some

 






 

structure AnchoredInitialData (C : Set Plane) (A : AnchorSet C) extends InitialData C where
   
  a_mem_anchors : toInitialData.a ∈ A.carrier
   
  b_mem_anchors : toInitialData.b ∈ A.carrier

namespace AnchoredInitialData

variable {A : AnchorSet C} (D : AnchoredInitialData C A)

 

theorem stronglyAccessible_a : StronglyAccessible (inside C) D.toInitialData.a :=
  A.stronglyAccessible _ D.a_mem_anchors

 
theorem stronglyAccessible_b : StronglyAccessible (inside C) D.toInitialData.b :=
  A.stronglyAccessible _ D.b_mem_anchors

 
theorem exists_access_segment_a :
    ∃ z ∈ inside C, D.toInitialData.a ≠ z ∧ openSegment ℝ D.toInitialData.a z ⊆ inside C :=
  A.exists_access_segment D.a_mem_anchors

 
theorem exists_access_segment_b :
    ∃ z ∈ inside C, D.toInitialData.b ≠ z ∧ openSegment ℝ D.toInitialData.b z ⊆ inside C :=
  A.exists_access_segment D.b_mem_anchors

 
theorem exists_cone_a :
    ∃ v : Plane, ‖v‖ = 1 ∧ ∃ r > 0, ∀ s ≤ r, accessCone D.toInitialData.a v s ⊆ inside C :=
  A.exists_cone D.a_mem_anchors

 
theorem exists_cone_b :
    ∃ v : Plane, ‖v‖ = 1 ∧ ∃ r > 0, ∀ s ≤ r, accessCone D.toInitialData.b v s ⊆ inside C :=
  A.exists_cone D.b_mem_anchors

end AnchoredInitialData

 







theorem exists_anchoredInitialData_of_homeo (hC : IsJordanCurve C) (A : AnchorSet C)
    (u w : Plane → Plane) (hhom : IsSetHomeoOn u w C modelCurve) :
    ∃ D : AnchoredInitialData C A,
      D.toInitialData.u = u ∧ D.toInitialData.w = w := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  
  obtain ⟨W₁, hW₁, hW₁eq⟩ := hhom.symm.image_isRelOpen isOpen_topBand (U := openTop) rfl
  obtain ⟨W₂, hW₂, hW₂eq⟩ := hhom.symm.image_isRelOpen isOpen_bottomBand (U := openBottom) rfl
  obtain ⟨a₀, ha₀A, ha₀⟩ := exists_mem_inter_of_dense A.subset_curve A.dense hW₁ hW₁eq
    (openTop_nonempty.image w)
  obtain ⟨b₀, hb₀A, hb₀⟩ := exists_mem_inter_of_dense A.subset_curve A.dense hW₂ hW₂eq
    (openBottom_nonempty.image w)
  obtain ⟨q₁, hq₁, rfl⟩ := ha₀
  obtain ⟨q₂, hq₂, rfl⟩ := hb₀
  have hq₁m : q₁ ∈ modelCurve := hq₁.2
  have hq₂m : q₂ ∈ modelCurve := hq₂.2
  obtain ⟨hq₁1, hq₁0⟩ := mem_openTop.1 hq₁
  obtain ⟨hq₂1, hq₂0⟩ := mem_openBottom.1 hq₂
  set xa : ℝ := q₁ 0 with hxa
  set xb : ℝ := q₂ 0 with hxb
  have hq₁eq : q₁ = tgtPos xa xb 1 := Plane.eq_mk rfl hq₁1
  have hq₂eq : q₂ = tgtPos xa xb 4 := Plane.eq_mk rfl hq₂1
  have haC : w q₁ ∈ C := hhom.mapsTo_inv hq₁m
  have hbC : w q₂ ∈ C := hhom.mapsTo_inv hq₂m
  have hab : w q₁ ≠ w q₂ := by
    intro h
    have hr := hhom.rightInvOn hq₁m
    rw [h, hhom.rightInvOn hq₂m] at hr
    rw [← hr] at hq₁1
    rw [hq₂1] at hq₁1
    norm_num at hq₁1
  
  obtain ⟨ws, -, -, -, hwsin, hwsarc, -⟩ := exists_crosscut_of_polyAccessible
    hsep.isOpen_inside hsep.isConnected_inside.isPreconnected
    (Set.disjoint_left.2 fun x hx => inside_subset_compl hx) hab haC hbC
    (A.polyAccessible ha₀A) (A.polyAccessible hb₀A)
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hwsarc
  refine ⟨{ toInitialData :=
              { u := u, w := w, homeo := hhom, curve := hC, xa := xa, xb := xb
                abs_xa := hq₁0, abs_xb := hq₂0
                cross := f
                continuousOn_cross := hfc, injOn_cross := hfi
                cross_zero := by rw [hf0, hq₁eq]
                cross_one := by rw [hf1, hq₂eq]
                cross_inside := ?_
                polygonal_cross := ?_ }
            a_mem_anchors := ?_
            b_mem_anchors := ?_ }, rfl, rfl⟩
  · rw [hfim, ← hq₁eq, ← hq₂eq]
    intro z hz
    exact hwsin ⟨hz.1, by simpa [hf0, hf1] using hz.2⟩
  · rw [hfim]
    exact ⟨ws, rfl⟩
  · change w (tgtPos xa xb 1) ∈ A.carrier
    rw [← hq₁eq]
    exact ha₀A
  · change w (tgtPos xa xb 4) ∈ A.carrier
    rw [← hq₂eq]
    exact hb₀A

 
theorem exists_anchoredInitialData (hC : IsJordanCurve C) (A : AnchorSet C) :
    Nonempty (AnchoredInitialData C A) := by
  obtain ⟨u, w, hhom⟩ := exists_isSetHomeoOn_modelCurve hC
  obtain ⟨D, -, -⟩ := exists_anchoredInitialData_of_homeo hC A u w hhom
  exact ⟨D⟩

open Classical in
 

noncomputable def anchoredInitialData (hC : IsJordanCurve C) (A : AnchorSet C) :
    AnchoredInitialData C A := (exists_anchoredInitialData hC A).some

 

theorem exists_initialData' (hC : IsJordanCurve C) (A : AnchorSet C) :
    ∃ d : InitialData C, d.a ∈ A.carrier ∧ d.b ∈ A.carrier := by
  obtain ⟨D⟩ := exists_anchoredInitialData hC A
  exact ⟨D.toInitialData, D.a_mem_anchors, D.b_mem_anchors⟩

 






 
noncomputable def initialData (hC : IsJordanCurve C) : InitialData C :=
  (anchoredInitialData hC (anchorSet hC)).toInitialData

theorem initialData_a_mem_anchorSet (hC : IsJordanCurve C) :
    (initialData hC).a ∈ (anchorSet hC).carrier :=
  (anchoredInitialData hC (anchorSet hC)).a_mem_anchors

theorem initialData_b_mem_anchorSet (hC : IsJordanCurve C) :
    (initialData hC).b ∈ (anchorSet hC).carrier :=
  (anchoredInitialData hC (anchorSet hC)).b_mem_anchors

 


theorem stronglyAccessible_initialData_a (hC : IsJordanCurve C) :
    StronglyAccessible (inside C) (initialData hC).a :=
  (anchoredInitialData hC (anchorSet hC)).stronglyAccessible_a

 
theorem stronglyAccessible_initialData_b (hC : IsJordanCurve C) :
    StronglyAccessible (inside C) (initialData hC).b :=
  (anchoredInitialData hC (anchorSet hC)).stronglyAccessible_b

 






namespace InitialData

variable (d : InitialData C)

 
theorem hasArcCollarsSource : HasArcCollars (inside C) d.crossSet :=
  d.isCrosscut.hasArcCollars

 
theorem source_cells_cover' :
    inside C \ d.crossSet =
      d.sourceRealization.cell (.face false) ∪ d.sourceRealization.cell (.face true) :=
  d.source_cells_cover (fun _ hA => arc_complement hA) d.hasArcCollarsSource

 
theorem source_cell_isComponent' (k : Bool) :
    ∀ z ∈ d.sourceRealization.cell (.face k),
      connectedComponentIn (inside C \ d.crossSet) z = d.sourceRealization.cell (.face k) :=
  d.source_cell_isComponent (fun _ hA => arc_complement hA) k

 
theorem source_closure_cell_inter' (k : Bool) :
    closure (d.sourceRealization.cell (.face k)) ∩ C = d.src.arcOf k :=
  d.source_closure_cell_inter (fun _ hA => arc_complement hA) k

 
theorem source_cells_ne' :
    d.sourceRealization.cell (.face false) ≠ d.sourceRealization.cell (.face true) :=
  d.source_cells_ne (fun _ hA => arc_complement hA)

 
theorem target_cells_cover' :
    inside modelCurve \ d.tgt.chordSet =
      d.targetRealization.cell (.face false) ∪ d.targetRealization.cell (.face true) :=
  d.target_cells_cover (fun _ hA => arc_complement hA)

 
theorem target_closure_cell_inter' (k : Bool) :
    closure (d.targetRealization.cell (.face k)) ∩ modelCurve = d.tgt.arcOf k :=
  d.target_closure_cell_inter (fun _ hA => arc_complement hA) k

 

theorem target_cell_isComponent (k : Bool) :
    ∀ z ∈ d.targetRealization.cell (.face k),
      connectedComponentIn (inside modelCurve \ d.tgt.chordSet) z =
        d.targetRealization.cell (.face k) := by
  cases k
  · exact d.isCrosscutTarget.side_isComponent forall_isSeparating_of_isJordanCurve
      d.isCutPairTarget
  · exact d.isCrosscutTarget.side_isComponent forall_isSeparating_of_isJordanCurve
      d.isCutPairTarget.symm

 
theorem target_cells_ne :
    d.targetRealization.cell (.face false) ≠ d.targetRealization.cell (.face true) :=
  d.isCrosscutTarget.side_ne forall_isSeparating_of_isJordanCurve d.isCutPairTarget

 







theorem src_outer (i : Fin 6) : d.src.outer i = fun t => d.w (tgtOuter d.xa d.xb i t) := rfl

theorem tgt_outer (i : Fin 6) : d.tgt.outer i = tgtOuter d.xa d.xb i := rfl

theorem src_pos (i : Fin 6) : d.src.pos i = d.w (d.tgt.pos i) := rfl

 


theorem u_src_pos (i : Fin 6) : d.u (d.src.pos i) = d.tgt.pos i :=
  d.homeo.rightInvOn (tgtPos_mem_modelCurve d.abs_xa d.abs_xb i)

 
theorem tgt_pos_corners :
    d.tgt.pos 0 = Plane.mk 1 1 ∧ d.tgt.pos 2 = Plane.mk (-1) 1 ∧
      d.tgt.pos 3 = Plane.mk (-1) (-1) ∧ d.tgt.pos 5 = Plane.mk 1 (-1) :=
  ⟨rfl, rfl, rfl, rfl⟩

 

theorem u_a_mem_openTop : d.u d.a ∈ openTop := by
  rw [d.u_apply_a]
  exact mem_openTop.2 ⟨by simp, by simpa using d.abs_xa⟩

 
theorem u_b_mem_openBottom : d.u d.b ∈ openBottom := by
  rw [d.u_apply_b]
  exact mem_openBottom.2 ⟨by simp, by simpa using d.abs_xb⟩

 
theorem src_outer_image (i : Fin 6) : d.src.outer i '' I = d.w '' (d.tgt.outer i '' I) := by
  rw [← Set.image_comp]; rfl

theorem tgt_outer_subset_modelCurve (i : Fin 6) : d.tgt.outer i '' I ⊆ modelCurve :=
  tgtOuter_subset_modelCurve d.abs_xa d.abs_xb i

 
theorem u_image_w_image {X : Set Plane} (hX : X ⊆ modelCurve) : d.u '' (d.w '' X) = X := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rwa [d.homeo.rightInvOn (hX hx)]
  · exact fun hy => ⟨d.w y, ⟨y, hy, rfl⟩, d.homeo.rightInvOn (hX hy)⟩

theorem tgt_arcOf_subset_modelCurve (k : Bool) : d.tgt.arcOf k ⊆ modelCurve := by
  intro z hz
  rw [← d.tgt_outerArcs]
  exact d.tgt.arcOf_subset_outerArcs k hz

theorem src_arcOf_subset_curve (k : Bool) : d.src.arcOf k ⊆ C := by
  intro z hz
  rw [← d.src_outerArcs]
  exact d.src.arcOf_subset_outerArcs k hz

 
theorem src_arcOf_eq_image (k : Bool) : d.src.arcOf k = d.w '' d.tgt.arcOf k := by
  cases k <;>
    simp only [HexData.arcOf_false, HexData.arcOf_true, Set.image_union, d.src_outer_image]

 


theorem tgt_arcOf_eq_image (k : Bool) : d.tgt.arcOf k = d.u '' d.src.arcOf k := by
  rw [d.src_arcOf_eq_image k, d.u_image_w_image (d.tgt_arcOf_subset_modelCurve k)]

 

theorem skeletonHomeo_image_arcOf (k : Bool) :
    d.skeletonHomeo.toFun '' d.src.arcOf k = d.tgt.arcOf k := by
  rw [d.tgt_arcOf_eq_image k]
  exact Set.image_congr fun x hx => d.skeletonHomeo_eq_u (d.src_arcOf_subset_curve k hx)

 


theorem closure_cell_face_link (k : Bool) :
    closure (d.targetRealization.cell (.face k)) ∩ modelCurve =
      d.u '' (closure (d.sourceRealization.cell (.face k)) ∩ C) := by
  rw [d.target_closure_cell_inter' k, d.source_closure_cell_inter' k, d.tgt_arcOf_eq_image k]

 
theorem closure_cell_face_link_homeo (k : Bool) :
    d.skeletonHomeo.toFun '' (closure (d.sourceRealization.cell (.face k)) ∩ C) =
      closure (d.targetRealization.cell (.face k)) ∩ modelCurve := by
  rw [d.target_closure_cell_inter' k, d.source_closure_cell_inter' k]
  exact d.skeletonHomeo_image_arcOf k

 

 
theorem isPolygonal_tgt_outer (i : Fin 6) : IsPolygonal (d.tgt.outer i '' I) := by
  rw [d.tgt_outer i, tgtOuter_image]
  exact isPolygonal_segment _ _

 

theorem isPolygonal_tgt_edgeArc {e : InitialCell} (he : e ∈ E(initSkel)) :
    IsPolygonal (Graph.edgeArc d.tgt.draw e) := by
  rcases (he : e ∈ InitialCell.edges) with ⟨i, rfl⟩ | rfl
  · rw [HexData.edgeArc_edge]
    exact d.isPolygonal_tgt_outer i
  · rw [HexData.edgeArc_chord]
    change IsPolygonal d.tgt.chordSet
    rw [d.tgt_chordSet]
    exact isPolygonal_segment _ _

 
theorem isPolygonal_tgt_arcOf (k : Bool) : IsPolygonal (d.tgt.arcOf k) :=
  d.tgt.isPolygonal_arcOf d.isPolygonal_tgt_outer k

 
theorem isPolygonal_targetRealization_skeletonSet :
    IsPolygonal d.targetRealization.skeletonSet := by
  rw [d.targetRealization_skeletonSet]
  refine isPolygonal_modelCurve.union ?_ ?_
  · rw [d.tgt_chordSet]; exact isPolygonal_segment _ _
  · refine ⟨Plane.mk d.xa 1, tgtPos_mem_modelCurve d.abs_xa d.abs_xb 1, ?_⟩
    rw [d.tgt_chordSet]
    exact left_mem_segment ℝ _ _

 

theorem isPolygonal_src_nonboundary_edgeArc :
    IsPolygonal (Graph.edgeArc d.src.draw .chord) ∧
      Graph.edgeArc d.src.draw .chord \ C ⊆ inside C := by
  refine ⟨d.polygonal_cross, ?_⟩
  rintro z ⟨hz, hzC⟩
  refine d.cross_inside ⟨hz, ?_⟩
  rintro (rfl | rfl)
  exacts [hzC d.a_mem, hzC d.b_mem]

end InitialData

 










theorem initial_pair' (hC : IsJordanCurve C) (A : AnchorSet C) :
    ∃ d : InitialData C,
      
      d.a ∈ A.carrier ∧ d.b ∈ A.carrier ∧
      StronglyAccessible (inside C) d.a ∧ StronglyAccessible (inside C) d.b ∧
      
      d.u d.a ∈ openTop ∧ d.u d.b ∈ openBottom ∧
      
      (∀ i : Fin 6, d.u (d.src.pos i) = d.tgt.pos i) ∧
      
      (d.sourceRealization.graph).IsTwoConnected ∧
      (d.targetRealization.graph).IsTwoConnected ∧
      d.sourceRealization.outerSet = C ∧
      d.targetRealization.outerSet = modelCurve ∧
      IsConnected d.sourceRealization.nonboundary ∧
      IsConnected d.targetRealization.nonboundary ∧
      IsPolygonal d.crossSet ∧
      (∀ e ∈ E(initSkel), IsPolygonal (Graph.edgeArc d.tgt.draw e)) ∧
      
      d.tgt.chordSet = segment ℝ (d.u d.a) (d.u d.b) ∧
      (∀ x ∈ C, d.skeletonHomeo.toFun x = d.u x) ∧
      
      (∀ k : Bool, d.tgt.arcOf k = d.u '' d.src.arcOf k) ∧
      (∀ k : Bool, closure (d.sourceRealization.cell (.face k)) ∩ C = d.src.arcOf k) ∧
      (∀ k : Bool, closure (d.targetRealization.cell (.face k)) ∩ modelCurve = d.tgt.arcOf k) := by
  obtain ⟨D⟩ := exists_anchoredInitialData hC A
  refine ⟨D.toInitialData, D.a_mem_anchors, D.b_mem_anchors, D.stronglyAccessible_a,
    D.stronglyAccessible_b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.toInitialData.u_a_mem_openTop
  · exact D.toInitialData.u_b_mem_openBottom
  · exact D.toInitialData.u_src_pos
  · exact D.toInitialData.isTwoConnected_sourceRealization
  · exact D.toInitialData.isTwoConnected_targetRealization
  · exact D.toInitialData.sourceRealization_outerSet
  · exact D.toInitialData.targetRealization_outerSet
  · exact D.toInitialData.isConnected_sourceRealization_nonboundary
  · exact D.toInitialData.isConnected_targetRealization_nonboundary
  · exact D.toInitialData.polygonal_cross
  · exact fun e he => D.toInitialData.isPolygonal_tgt_edgeArc he
  · rw [D.toInitialData.tgt_chordSet, D.toInitialData.u_apply_a, D.toInitialData.u_apply_b]
  · exact fun x hx => D.toInitialData.skeletonHomeo_eq_u hx
  · exact D.toInitialData.tgt_arcOf_eq_image
  · exact D.toInitialData.source_closure_cell_inter'
  · exact D.toInitialData.target_closure_cell_inter'

end Schoenflies
