/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/InitialGenerated.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.FiniteTransfer
import FiniteAvalanches.Support.Schoenflies.InitialPairFixed
import FiniteAvalanches.Support.Schoenflies.BoundaryContinuity2

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 










































































open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

open Graph

 





 


theorem IsArcBetween.closure_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    closure (A \ {p, q}) = A := by
  refine Subset.antisymm (h.isArc.isClosed.closure_subset_iff.2 sdiff_subset) fun z hz => ?_
  by_cases hzp : z = p
  · exact hzp ▸ h.left_mem_closure_diff
  by_cases hzq : z = q
  · exact hzq ▸ h.right_mem_closure_diff
  exact subset_closure ⟨hz, by rintro (rfl | rfl) <;> simp_all⟩

 








 

theorem aux_notMem_cells (n : ℕ) : (InitialCell.aux n) ∉ initialStructure.cells :=
  aux_notMem_cellNames n

theorem mem_cells_initialStructure_of_vert (i : Fin 6) :
    (InitialCell.vert i) ∈ initialStructure.cells := Or.inl (Or.inl ⟨i, rfl⟩)

theorem mem_cells_initialStructure_of_edge (i : Fin 6) :
    (InitialCell.edge i) ∈ initialStructure.cells := Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))

theorem mem_cells_initialStructure_of_chord :
    InitialCell.chord ∈ initialStructure.cells := Or.inl (Or.inr (Or.inr rfl))

theorem mem_cells_initialStructure_of_face (k : Bool) :
    (InitialCell.face k) ∈ initialStructure.cells := Or.inr ⟨k, rfl⟩

 
theorem mem_cellNames_of_vert (i : Fin 6) : (InitialCell.vert i) ∈ cellNames :=
  Or.inl (Or.inl ⟨i, rfl⟩)

theorem mem_cellNames_of_edge (i : Fin 6) : (InitialCell.edge i) ∈ cellNames :=
  Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))

theorem mem_cellNames_chord : InitialCell.chord ∈ cellNames := Or.inl (Or.inr (Or.inr rfl))

theorem mem_cellNames_of_face (k : Bool) : (InitialCell.face k) ∈ cellNames := Or.inr ⟨k, rfl⟩

 
theorem mem_cells_of_mem_faceCells {k : Bool} {c : InitialCell} (h : c ∈ faceCells k) :
    c ∈ initialStructure.cells := by
  cases k <;>
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        first
          | exact mem_cells_initialStructure_of_vert _
          | exact mem_cells_initialStructure_of_edge _
          | exact mem_cells_initialStructure_of_chord

 

def recOnCells {motive : InitialCell → Sort*} {c : InitialCell}
    (hc : c ∈ initialStructure.cells) (hv : ∀ i, motive (.vert i)) (he : ∀ i, motive (.edge i))
    (hch : motive .chord) (hf : ∀ k, motive (.face k)) : motive c := by
  match c with
  | .vert i => exact hv i
  | .edge i => exact he i
  | .chord => exact hch
  | .face k => exact hf k
  | .aux n => exact absurd hc (aux_notMem_cells n)

 
theorem face_notMem_faceCells {k l : Bool} : InitialCell.face k ∉ faceCells l := by
  cases l <;> simp [faceCells]

 
theorem initSub_iff_vert {i : Fin 6} {c : InitialCell} :
    initSub c (.vert i) ↔ c = .vert i := by
  refine ⟨fun h => ?_, fun h => by subst h; exact initSub_refl (mem_cellNames_of_vert i)⟩
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, hk, -⟩
  · exact h
  · exact absurd h (by simp [InitialCell.edges])
  · exact absurd hk (by simp)

 
theorem initSub_iff_edge {i : Fin 6} {c : InitialCell} :
    initSub c (.edge i) ↔ c = .edge i ∨ c = .vert i ∨ c = .vert (i + 1) := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h | h⟩ | ⟨k, hk, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hk (by simp)
  · rintro (rfl | rfl | rfl)
    · exact initSub_refl (mem_cellNames_of_edge i)
    · exact (initSub_ends (InitialCell.edge_mem_edges i)).1
    · exact (initSub_ends (InitialCell.edge_mem_edges i)).2

 
theorem initSub_iff_chord {c : InitialCell} :
    initSub c .chord ↔ c = .chord ∨ c = .vert 1 ∨ c = .vert 4 := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h | h⟩ | ⟨k, hk, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hk (by simp)
  · rintro (rfl | rfl | rfl)
    · exact initSub_refl mem_cellNames_chord
    · exact (initSub_ends InitialCell.chord_mem_edges).1
    · exact (initSub_ends InitialCell.chord_mem_edges).2

 
theorem initSub_iff_face {k : Bool} {c : InitialCell} :
    initSub c (.face k) ↔ c = .face k ∨ c ∈ faceCells k := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨l, hl, hmem⟩)
    · exact Or.inl h
    · exact absurd h (by simp [InitialCell.edges])
    · cases hl; exact Or.inr hmem
  · rintro (rfl | h)
    · exact initSub_refl (mem_cellNames_of_face k)
    · exact initSub_face h

 






 

theorem combInvariants_initialStructure : initialStructure.CombInvariants where
  sub_mem_left := by
    rintro c d (⟨rfl, hc⟩ | ⟨hd, rfl | rfl⟩ | ⟨k, rfl, hmem⟩)
    · exact hc
    · exact Or.inl (Or.inl (InitialCell.ends_mem_vertices hd).1)
    · exact Or.inl (Or.inl (InitialCell.ends_mem_vertices hd).2)
    · exact mem_cells_of_mem_faceCells hmem
  sub_mem_right := by
    rintro c d (⟨-, hd⟩ | ⟨hd, -⟩ | ⟨k, rfl, -⟩)
    · exact hd
    · exact Or.inl (Or.inr hd)
    · exact mem_cells_initialStructure_of_face k
  sub_refl := fun {_} hc => initSub_refl hc
  sub_isLink := by
    rintro f a b ⟨hf, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    exacts [(initSub_ends hf).1, (initSub_ends hf).2]
  face_maximal := by
    rintro F τ ⟨k, rfl⟩ h
    rcases h with ⟨h, -⟩ | ⟨he, hends⟩ | ⟨l, rfl, hmem⟩
    · exact h.symm
    · 
      rcases he with ⟨j, rfl⟩ | rfl <;> simp [InitialCell.ends] at hends
    · exact absurd hmem face_notMem_faceCells
  nonboundary_edge := by
    rintro F ⟨k, rfl⟩
    refine ⟨.chord, InitialCell.chord_mem_edges, by simp [InitialCell.outerEdges], ?_⟩
    exact initSub_face (by cases k <;> simp [faceCells])
  mem_face := by
    rintro c hc
    
    cases c with
    | aux n => exact absurd hc (aux_notMem_cells n)
    | vert i =>
      refine ⟨.face (![true, false, false, false, true, true] i), ⟨_, rfl⟩, initSub_face ?_⟩
      fin_cases i <;> simp [faceCells]
    | edge i =>
      refine ⟨.face (![true, false, false, false, true, true] i), ⟨_, rfl⟩, initSub_face ?_⟩
      fin_cases i <;> simp [faceCells]
    | chord => exact ⟨.face false, ⟨_, rfl⟩, initSub_face (by simp [faceCells])⟩
    | face k => exact ⟨.face k, ⟨k, rfl⟩, initSub_refl (mem_cellNames_of_face k)⟩
  outerEdge_unique := outerEdgeUniqueFace_initialStructure

 





namespace HexData

variable (H : HexData)

@[simp] theorem cellSet_vert (i : Fin 6) : H.cellSet (.vert i) = {H.pos i} := rfl

@[simp] theorem cellSet_edge (i : Fin 6) :
    H.cellSet (.edge i) = H.outer i '' I \ {H.pos i, H.pos (i + 1)} := rfl

@[simp] theorem cellSet_chord : H.cellSet .chord = H.chordSet \ {H.pos 1, H.pos 4} := rfl

@[simp] theorem cellSet_face (k : Bool) :
    H.cellSet (.face k) = inside (H.arcOf k ∪ H.chordSet) := rfl

theorem cellSet_edge_subset (i : Fin 6) : H.cellSet (.edge i) ⊆ H.outer i '' I := sdiff_subset

theorem cellSet_edge_subset_outerArcs (i : Fin 6) : H.cellSet (.edge i) ⊆ H.outerArcs :=
  (H.cellSet_edge_subset i).trans (Set.subset_iUnion (fun i : Fin 6 => H.outer i '' I) i)

theorem cellSet_chord_subset : H.cellSet .chord ⊆ H.chordSet := sdiff_subset

theorem pos_mem_outerArcs (i : Fin 6) : H.pos i ∈ H.outerArcs :=
  Set.mem_iUnion.2 ⟨i, H.pos_mem_outer i⟩

 
theorem nonempty_cellSet_edge (i : Fin 6) : (H.cellSet (.edge i)).Nonempty :=
  (H.isArcBetween_outer i).nonempty_diff

theorem nonempty_cellSet_chord : (H.cellSet .chord).Nonempty :=
  H.isArcBetween_chordSet.nonempty_diff

 
theorem closure_cellSet_edge (i : Fin 6) :
    closure (H.cellSet (.edge i)) = H.outer i '' I :=
  (H.isArcBetween_outer i).closure_diff

theorem closure_cellSet_chord : closure (H.cellSet .chord) = H.chordSet :=
  H.isArcBetween_chordSet.closure_diff

 

theorem pos_notMem_cellSet_edge (k i : Fin 6) : H.pos k ∉ H.cellSet (.edge i) := by
  rintro ⟨hz, hne⟩
  rcases H.mem_outer_iff hz with rfl | rfl
  exacts [hne (Or.inl rfl), hne (Or.inr rfl)]

theorem pos_notMem_cellSet_chord (k : Fin 6) : H.pos k ∉ H.cellSet .chord := by
  rintro ⟨hz, hne⟩
  rcases H.mem_chord_iff hz with rfl | rfl
  exacts [hne (Or.inl rfl), hne (Or.inr rfl)]

 

theorem disjoint_cellSet_edge {i j : Fin 6} (hij : i ≠ j) :
    Disjoint (H.cellSet (.edge i)) (H.cellSet (.edge j)) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzi, hne⟩ ⟨hzj, -⟩
  exact hne (H.outer_meet i j hij ⟨hzi, hzj⟩).1

 
theorem disjoint_cellSet_edge_chord (i : Fin 6) :
    Disjoint (H.cellSet (.edge i)) (H.cellSet .chord) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzi, -⟩ ⟨hzc, hne⟩
  exact hne (H.chord_meet i ⟨hzc, hzi⟩)

 
theorem mem_cellSet_edge_or {i : Fin 6} {z : Plane} (hz : z ∈ H.outer i '' I) :
    z ∈ H.cellSet (.edge i) ∨ z = H.pos i ∨ z = H.pos (i + 1) := by
  by_cases h : z ∈ ({H.pos i, H.pos (i + 1)} : Set Plane)
  · rcases h with h | h
    exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]
  · exact Or.inl ⟨hz, h⟩

 
theorem mem_cellSet_chord_or {z : Plane} (hz : z ∈ H.chordSet) :
    z ∈ H.cellSet .chord ∨ z = H.pos 1 ∨ z = H.pos 4 := by
  by_cases h : z ∈ ({H.pos 1, H.pos 4} : Set Plane)
  · rcases h with h | h
    exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]
  · exact Or.inl ⟨hz, h⟩

 
theorem iUnion_cellSet (H : HexData) :
    (⋃ c : InitialCell, H.cellSet c) =
      (H.outerArcs ∪ H.chordSet) ∪ (H.cellSet (.face false) ∪ H.cellSet (.face true)) := by
  refine Subset.antisymm (Set.iUnion_subset fun c => ?_) fun z hz => ?_
  · cases c with
    | vert i =>
      rintro z rfl
      exact Or.inl (Or.inl (H.pos_mem_outerArcs i))
    | edge i => exact fun z hz => Or.inl (Or.inl (H.cellSet_edge_subset_outerArcs i hz))
    | chord => exact fun z hz => Or.inl (Or.inr (H.cellSet_chord_subset hz))
    | aux n => exact Set.empty_subset _
    | face k =>
      cases k
      exacts [fun z hz => Or.inr (Or.inl hz), fun z hz => Or.inr (Or.inr hz)]
  · rcases hz with (hz | hz) | (hz | hz)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
      rcases H.mem_cellSet_edge_or hi with h | rfl | rfl
      exacts [Set.mem_iUnion.2 ⟨.edge i, h⟩, Set.mem_iUnion.2 ⟨.vert i, rfl⟩,
        Set.mem_iUnion.2 ⟨.vert (i + 1), rfl⟩]
    · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion.2 ⟨.chord, h⟩, Set.mem_iUnion.2 ⟨.vert 1, rfl⟩,
        Set.mem_iUnion.2 ⟨.vert 4, rfl⟩]
    · exact Set.mem_iUnion.2 ⟨.face false, hz⟩
    · exact Set.mem_iUnion.2 ⟨.face true, hz⟩

 



theorem biUnion_of_three_edges (H : HexData) (F : Set InitialCell) {i j l : Fin 6}
    (hij : i + 1 = j) (hjl : j + 1 = l)
    (hmem : ∀ c ∈ F, c = .vert i ∨ c = .vert j ∨ c = .vert l ∨ c = .vert (l + 1) ∨
      c = .edge i ∨ c = .edge j ∨ c = .edge l ∨ c = .chord)
    (hvi : InitialCell.vert i ∈ F) (hvj : InitialCell.vert j ∈ F)
    (hvl : InitialCell.vert l ∈ F) (hvl1 : InitialCell.vert (l + 1) ∈ F)
    (hei : InitialCell.edge i ∈ F) (hej : InitialCell.edge j ∈ F)
    (hel : InitialCell.edge l ∈ F) (hch : InitialCell.chord ∈ F)
    (hv1 : InitialCell.vert 1 ∈ F) (hv4 : InitialCell.vert 4 ∈ F) :
    (⋃ c ∈ F, H.cellSet c)
      = (H.outer i '' I ∪ (H.outer j '' I ∪ H.outer l '' I)) ∪ H.chordSet := by
  refine Subset.antisymm (Set.iUnion₂_subset fun c hc => ?_) fun z hz => ?_
  · rcases hmem c hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rintro z rfl; exact Or.inl (Or.inl (H.pos_mem_outer i))
    · rintro z rfl; exact Or.inl (Or.inl (H.pos_mem_outer_of_succ hij))
    · rintro z rfl; exact Or.inl (Or.inr (Or.inl (H.pos_mem_outer_of_succ hjl)))
    · rintro z rfl; exact Or.inl (Or.inr (Or.inr (H.pos_succ_mem_outer l)))
    · exact fun z hz => Or.inl (Or.inl (H.cellSet_edge_subset i hz))
    · exact fun z hz => Or.inl (Or.inr (Or.inl (H.cellSet_edge_subset j hz)))
    · exact fun z hz => Or.inl (Or.inr (Or.inr (H.cellSet_edge_subset l hz)))
    · exact fun z hz => Or.inr (H.cellSet_chord_subset hz)
  · rcases hz with (hz | hz | hz) | hz
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hei, h⟩, Set.mem_iUnion₂.2 ⟨_, hvi, rfl⟩,
        Set.mem_iUnion₂.2 ⟨InitialCell.vert (i + 1), by rw [hij]; exact hvj, rfl⟩]
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hej, h⟩, Set.mem_iUnion₂.2 ⟨_, hvj, rfl⟩,
        Set.mem_iUnion₂.2 ⟨InitialCell.vert (j + 1), by rw [hjl]; exact hvl, rfl⟩]
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hel, h⟩, Set.mem_iUnion₂.2 ⟨_, hvl, rfl⟩,
        Set.mem_iUnion₂.2 ⟨_, hvl1, rfl⟩]
    · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hch, h⟩, Set.mem_iUnion₂.2 ⟨_, hv1, rfl⟩,
        Set.mem_iUnion₂.2 ⟨_, hv4, rfl⟩]

 


theorem biUnion_faceCells (H : HexData) (k : Bool) :
    (⋃ c ∈ faceCells k, H.cellSet c) = H.arcOf k ∪ H.chordSet := by
  cases k
  · rw [HexData.arcOf_false]
    refine H.biUnion_of_three_edges _ (i := 1) (j := 2) (l := 3) (by decide) (by decide)
      (fun c hc => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    all_goals (simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff]; decide)
  · rw [HexData.arcOf_true]
    refine H.biUnion_of_three_edges _ (i := 4) (j := 5) (l := 0) (by decide) (by decide)
      (fun c hc => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    all_goals (simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff]; decide)

 








 








theorem isCellDecomposition (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4))
    (hcut : IsCutPair H.outerArcs (H.pos 1) (H.pos 4) (H.arcOf false) (H.arcOf true))
    (hcollars : HasArcCollars (inside H.outerArcs) H.chordSet) :
    H.realization.IsCellDecomposition (H.outerArcs ∪ inside H.outerArcs) := by
  obtain ⟨hsplit, hdisj12, hdisj1P, hdisj2P, -, -, hne1, hne2, hcl1, hcl2⟩ :=
    crosscut_cell_partition forall_isSeparating_of_isJordanCurve hcross hcut hcollars
  
  have hface : ∀ k : Bool, H.cellSet (.face k) ⊆ inside H.outerArcs := by
    intro k z hz
    rw [hsplit]
    cases k
    exacts [Or.inl (Or.inl hz), Or.inl (Or.inr hz)]
  have hfaceOuter : ∀ k : Bool, Disjoint (H.cellSet (.face k)) H.outerArcs := by
    intro k
    rw [Set.disjoint_left]
    exact fun z hz hzo => (hface k hz).1 hzo
  have hfaceChord : ∀ k : Bool, Disjoint (H.cellSet (.face k)) (H.cellSet .chord) := by
    intro k; cases k; exacts [hdisj1P, hdisj2P]
  have hfaceNe : ∀ k : Bool, (H.cellSet (.face k)).Nonempty := by
    intro k; cases k; exacts [hne1, hne2]
  have hfaceCl : ∀ k : Bool,
      closure (H.cellSet (.face k)) = H.cellSet (.face k) ∪ (H.arcOf k ∪ H.chordSet) := by
    intro k; cases k; exacts [hcl1, hcl2]
  
  have hvertEdge : ∀ k i : Fin 6, Disjoint (H.cellSet (.vert k)) (H.cellSet (.edge i)) := by
    intro k i
    rw [Set.disjoint_left]
    rintro z rfl h
    exact H.pos_notMem_cellSet_edge k i h
  have hvertChord : ∀ k : Fin 6, Disjoint (H.cellSet (.vert k)) (H.cellSet .chord) := by
    intro k
    rw [Set.disjoint_left]
    rintro z rfl h
    exact H.pos_notMem_cellSet_chord k h
  have hvertFace : ∀ (k : Fin 6) (l : Bool),
      Disjoint (H.cellSet (.vert k)) (H.cellSet (.face l)) := by
    intro k l
    rw [Set.disjoint_left]
    rintro z rfl h
    exact (hface l h).1 (H.pos_mem_outerArcs k)
  have hedgeFace : ∀ (i : Fin 6) (l : Bool),
      Disjoint (H.cellSet (.edge i)) (H.cellSet (.face l)) :=
    fun i l => (hfaceOuter l).symm.mono_left (H.cellSet_edge_subset_outerArcs i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · 
    rintro c hc
    cases c with
    | aux n => exact absurd hc (aux_notMem_cells n)
    | vert i => exact ⟨H.pos i, rfl⟩
    | edge i => exact H.nonempty_cellSet_edge i
    | chord => exact H.nonempty_cellSet_chord
    | face k => exact hfaceNe k
  · 
    rintro c d hc hd hcd
    cases c with
    | aux n => exact absurd hc (aux_notMem_cells n)
    | vert k =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m =>
        rw [Set.disjoint_left]
        rintro z rfl h
        exact hcd (congrArg InitialCell.vert (H.injective_pos h))
      | edge i => exact hvertEdge k i
      | chord => exact hvertChord k
      | face l => exact hvertFace k l
    | edge i =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m => exact (hvertEdge m i).symm
      | edge j => exact H.disjoint_cellSet_edge fun h => hcd (congrArg InitialCell.edge h)
      | chord => exact H.disjoint_cellSet_edge_chord i
      | face l => exact hedgeFace i l
    | chord =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m => exact (hvertChord m).symm
      | edge j => exact (H.disjoint_cellSet_edge_chord j).symm
      | chord => exact absurd rfl hcd
      | face l => exact (hfaceChord l).symm
    | face k =>
      cases d with
      | aux n => exact absurd hd (aux_notMem_cells n)
      | vert m => exact (hvertFace m k).symm
      | edge j => exact (hedgeFace j k).symm
      | chord => exact hfaceChord k
      | face l =>
        cases k <;> cases l
        exacts [absurd rfl hcd, hdisj12, hdisj12.symm, absurd rfl hcd]
  · 
    have hall : (⋃ c ∈ initialStructure.cells, H.realization.cell c)
        = ⋃ c : InitialCell, H.cellSet c := by
      refine Subset.antisymm (Set.iUnion₂_subset fun c _ => Set.subset_iUnion _ c)
        (Set.iUnion_subset fun c => ?_)
      match c with
      | .vert i => exact Set.subset_biUnion_of_mem (mem_cells_initialStructure_of_vert i)
      | .edge i => exact Set.subset_biUnion_of_mem (mem_cells_initialStructure_of_edge i)
      | .chord => exact Set.subset_biUnion_of_mem mem_cells_initialStructure_of_chord
      | .face k => exact Set.subset_biUnion_of_mem (mem_cells_initialStructure_of_face k)
      | .aux n => exact Set.empty_subset _
    rw [hall, H.iUnion_cellSet]
    refine Subset.antisymm (Set.union_subset (Set.union_subset Set.subset_union_left ?_) ?_) ?_
    · intro z hz
      rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      · exact Or.inr (by rw [hsplit]; exact Or.inr h)
      · exact Or.inl (H.pos_mem_outerArcs 1)
      · exact Or.inl (H.pos_mem_outerArcs 4)
    · rintro z (hz | hz)
      exacts [Or.inr (hface false hz), Or.inr (hface true hz)]
    · rintro z (hz | hz)
      · exact Or.inl (Or.inl hz)
      · rw [hsplit] at hz
        rcases hz with (hz | hz) | hz
        exacts [Or.inr (Or.inl hz), Or.inr (Or.inr hz),
          Or.inl (Or.inr (H.cellSet_chord_subset hz))]
  · 
    rintro τ hτ
    have hidx : {c | c ∈ initialStructure.cells ∧ initialStructure.sub c τ}
        = {c | initSub c τ} := by
      ext c
      exact ⟨fun h => h.2, fun h => ⟨combInvariants_initialStructure.sub_mem_left h, h⟩⟩
    rw [hidx]
    cases τ with
    | aux n => exact absurd hτ (aux_notMem_cells n)
    | vert i =>
      have hset : {c | initSub c (.vert i)} = ({InitialCell.vert i} : Set InitialCell) := by
        ext c; exact initSub_iff_vert
      rw [hset, Set.biUnion_singleton]
      exact closure_singleton
    | edge i =>
      have hset : {c | initSub c (.edge i)}
          = ({InitialCell.edge i, .vert i, .vert (i + 1)} : Set InitialCell) := by
        ext c; exact initSub_iff_edge
      rw [hset]
      change closure (H.cellSet (.edge i)) = _
      rw [H.closure_cellSet_edge i]
      refine Subset.antisymm (fun z hz => ?_) ?_
      · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
        exacts [Set.mem_iUnion₂.2 ⟨_, Or.inl rfl, h⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inl rfl), rfl⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inr rfl), rfl⟩]
      · refine Set.iUnion₂_subset fun c hc => ?_
        rcases hc with rfl | rfl | rfl
        · exact H.cellSet_edge_subset i
        · rintro z rfl; exact H.pos_mem_outer i
        · rintro z rfl; exact H.pos_succ_mem_outer i
    | chord =>
      have hset : {c | initSub c .chord}
          = ({InitialCell.chord, .vert 1, .vert 4} : Set InitialCell) := by
        ext c; exact initSub_iff_chord
      rw [hset]
      change closure (H.cellSet .chord) = _
      rw [H.closure_cellSet_chord]
      refine Subset.antisymm (fun z hz => ?_) ?_
      · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
        exacts [Set.mem_iUnion₂.2 ⟨_, Or.inl rfl, h⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inl rfl), rfl⟩,
          Set.mem_iUnion₂.2 ⟨_, Or.inr (Or.inr rfl), rfl⟩]
      · refine Set.iUnion₂_subset fun c hc => ?_
        rcases hc with rfl | rfl | rfl
        · exact H.cellSet_chord_subset
        · rintro z rfl
          exact ⟨0, zero_mem_I, H.chord_zero⟩
        · rintro z rfl
          exact ⟨1, one_mem_I, H.chord_one⟩
    | face k =>
      have hset : {c | initSub c (.face k)} = insert (InitialCell.face k) (faceCells k) := by
        ext c; exact initSub_iff_face
      rw [hset, Set.biUnion_insert]
      change closure (H.cellSet (.face k))
        = H.cellSet (.face k) ∪ ⋃ x ∈ faceCells k, H.cellSet x
      rw [H.biUnion_faceCells k]
      exact hfaceCl k

 



theorem isOpen_cellSet_face (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4))
    (hcut : IsCutPair H.outerArcs (H.pos 1) (H.pos 4) (H.arcOf false) (H.arcOf true))
    (hcollars : HasArcCollars (inside H.outerArcs) H.chordSet) (k : Bool) :
    IsOpen (H.cellSet (.face k)) := by
  obtain ⟨-, -, -, -, hopen1, hopen2, -⟩ :=
    crosscut_cell_partition forall_isSeparating_of_isJordanCurve hcross hcut hcollars
  cases k
  exacts [hopen1, hopen2]

 


theorem isFaceJordan (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4))
    (hcut : IsCutPair H.outerArcs (H.pos 1) (H.pos 4) (H.arcOf false) (H.arcOf true)) :
    H.realization.IsFaceJordan where
  isJordanCurve := by
    intro F hF
    obtain ⟨k, rfl⟩ := hF
    cases k
    · change IsJordanCurve (frontier (H.cellSet (.face false)))
      rw [H.cellSet_face,
        (jordan_curve_theorem (hcross.isJordanCurve_union hcut)).frontier_inside]
      exact hcross.isJordanCurve_union hcut
    · change IsJordanCurve (frontier (H.cellSet (.face true)))
      rw [H.cellSet_face,
        (jordan_curve_theorem (hcross.isJordanCurve_union hcut.symm)).frontier_inside]
      exact hcross.isJordanCurve_union hcut.symm
  cell_eq_inside := by
    intro F hF
    obtain ⟨k, rfl⟩ := hF
    cases k
    · change inside (H.arcOf false ∪ H.chordSet) =
        inside (frontier (inside (H.arcOf false ∪ H.chordSet)))
      rw [(jordan_curve_theorem (hcross.isJordanCurve_union hcut)).frontier_inside]
    · change inside (H.arcOf true ∪ H.chordSet) =
        inside (frontier (inside (H.arcOf true ∪ H.chordSet)))
      rw [(jordan_curve_theorem (hcross.isJordanCurve_union hcut.symm)).frontier_inside]

 







theorem isWeaklyAdmissible (H : HexData)
    (hcross : IsCrosscut H.outerArcs H.chordSet (H.pos 1) (H.pos 4)) :
    H.realization.IsWeaklyAdmissible H.outerArcs (H.outerArcs ∪ inside H.outerArcs) where
  isTwoConnected := H.isTwoConnected_graph
  outerSet_eq := H.outerSet_realization
  isPolygonal := by
    rintro e he hne
    
    rcases (he : e ∈ InitialCell.edges) with ⟨i, rfl⟩ | rfl
    · exact absurd (Set.mem_range_self i) hne
    · exact hcross.polygonal
  cell_subset := by
    rintro e he hne
    rcases (he : e ∈ InitialCell.edges) with ⟨i, rfl⟩ | rfl
    · exact absurd (Set.mem_range_self i) hne
    · intro z hz
      exact ⟨Or.inr (hcross.sdiff_subset hz), (hcross.sdiff_subset hz).1⟩
  skeletonSet_subset := by
    rw [H.skeletonSet_realization]
    refine Set.union_subset Set.subset_union_left fun z hz => ?_
    rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
    · exact Or.inr (hcross.sdiff_subset h)
    · exact Or.inl (H.pos_mem_outerArcs 1)
    · exact Or.inl (H.pos_mem_outerArcs 4)

end HexData

 





 
theorem modelCurve_union_inside : modelCurve ∪ inside modelCurve = Plane.closedSquare 0 1 := by
  rw [inside_modelCurve]
  ext x
  rw [Set.mem_union, mem_openSquare_zero_one, mem_closedSquare_zero_one]
  constructor
  · rintro (h | h)
    · exact le_of_eq (h : Plane.supNorm x = 1)
    · exact h.le
  · intro h
    rcases lt_or_eq_of_le h with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

 





namespace InitialData

variable {C : Set Plane} (d : InitialData C)

 

theorem isCrosscut_src : IsCrosscut d.src.outerArcs d.src.chordSet (d.src.pos 1) (d.src.pos 4) := by
  rw [d.src_outerArcs]; exact d.isCrosscut

 
theorem isCrosscut_tgt : IsCrosscut d.tgt.outerArcs d.tgt.chordSet (d.tgt.pos 1) (d.tgt.pos 4) := by
  rw [d.tgt_outerArcs]; exact d.isCrosscutTarget

 
theorem src_isCellDecomposition : d.sourceRealization.IsCellDecomposition (C ∪ inside C) := by
  have h := d.src.isCellDecomposition d.isCrosscut_src
    (by rw [d.src_outerArcs]; exact d.isCutPair)
    (by rw [d.src_outerArcs]; exact d.hasArcCollarsSource)
  rwa [d.src_outerArcs] at h

 
theorem tgt_isCellDecomposition :
    d.targetRealization.IsCellDecomposition (Plane.closedSquare 0 1) := by
  have h := d.tgt.isCellDecomposition d.isCrosscut_tgt
    (by rw [d.tgt_outerArcs]; exact d.isCutPairTarget)
    (by rw [d.tgt_outerArcs]; exact d.hasArcCollarsTarget)
  rwa [d.tgt_outerArcs, modelCurve_union_inside] at h

 
theorem src_isWeaklyAdmissible : d.sourceRealization.IsWeaklyAdmissible C (C ∪ inside C) := by
  have h := d.src.isWeaklyAdmissible d.isCrosscut_src
  rwa [d.src_outerArcs] at h

 
theorem tgt_isWeaklyAdmissible :
    d.targetRealization.IsWeaklyAdmissible modelCurve (Plane.closedSquare 0 1) := by
  have h := d.tgt.isWeaklyAdmissible d.isCrosscut_tgt
  rwa [d.tgt_outerArcs, modelCurve_union_inside] at h

 

theorem isOpen_sourceRealization_cell_face (k : Bool) :
    IsOpen (d.sourceRealization.cell (.face k)) :=
  d.src.isOpen_cellSet_face d.isCrosscut_src (by rw [d.src_outerArcs]; exact d.isCutPair)
    (by rw [d.src_outerArcs]; exact d.hasArcCollarsSource) k

 
theorem isOpen_targetRealization_cell_face (k : Bool) :
    IsOpen (d.targetRealization.cell (.face k)) :=
  d.tgt.isOpen_cellSet_face d.isCrosscut_tgt (by rw [d.tgt_outerArcs]; exact d.isCutPairTarget)
    (by rw [d.tgt_outerArcs]; exact d.hasArcCollarsTarget) k

 







noncomputable def generatedPair :
    GeneratedPair initialStructure C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) where
  str := initialStructure
  generated := GeneratedStructure.base
  str_combInvariants := combInvariants_initialStructure
  str_boundaryCycles := boundaryCycles_initialStructure
  src := d.sourceRealization
  tgt := d.targetRealization
  homeo := d.skeletonHomeo
  src_isCellDecomposition := d.src_isCellDecomposition
  tgt_isCellDecomposition := d.tgt_isCellDecomposition
  src_isFaceJordan := d.src.isFaceJordan d.isCrosscut_src
    (by rw [d.src_outerArcs]; exact d.isCutPair)
  tgt_isFaceJordan := d.tgt.isFaceJordan d.isCrosscut_tgt
    (by rw [d.tgt_outerArcs]; exact d.isCutPairTarget)
  tgtInterior_isOpen := by
    rw [closedSquare_sdiff_modelCurve]
    exact Plane.isOpen_openSquare 0 1
  tgtInterior_frontier_subset := by
    rw [closedSquare_sdiff_modelCurve]
    refine (Plane.frontier_openSquare_subset 0 1).trans ?_
    rw [← modelCurve_eq_frontier, ← d.tgt_isWeaklyAdmissible.outerSet_eq]
    exact d.targetRealization.outerSet_subset_skeletonSet
  tgt_isPolygonal := by
    intro e he
    change e ∈ E(initSkel) at he
    change IsPolygonal (Graph.edgeArc d.tgt.draw e)
    exact d.isPolygonal_tgt_edgeArc he
  src_isWeaklyAdmissible := d.src_isWeaklyAdmissible
  tgt_isWeaklyAdmissible := d.tgt_isWeaklyAdmissible

@[simp] theorem generatedPair_str : d.generatedPair.str = initialStructure := rfl

@[simp] theorem generatedPair_src : d.generatedPair.src = d.sourceRealization := rfl

@[simp] theorem generatedPair_tgt : d.generatedPair.tgt = d.targetRealization := rfl

@[simp] theorem generatedPair_homeo : d.generatedPair.homeo = d.skeletonHomeo := rfl

 

theorem generatedPair_combInvariants : d.generatedPair.str.CombInvariants :=
  d.generatedPair.combInvariants combInvariants_initialStructure

 


theorem generatedPair_src_isAdmissible :
    d.generatedPair.src.IsAdmissible C (C ∪ inside C) :=
  d.generatedPair.src_isAdmissible d.isConnected_sourceRealization_nonboundary

theorem generatedPair_tgt_isAdmissible :
    d.generatedPair.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) :=
  d.generatedPair.tgt_isAdmissible d.isConnected_sourceRealization_nonboundary

end InitialData

 




noncomputable def AnchoredInitialData.generatedPair {C : Set Plane} {A : AnchorSet C}
    (D : AnchoredInitialData C A) :
    GeneratedPair initialStructure C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  D.toInitialData.generatedPair

 


















instance : Infinite InitialCell :=
  Infinite.of_injective InitialCell.aux fun _ _ h => by injection h

 



theorem infinite_initialCell : Infinite InitialCell := inferInstance

 





example {C : Set Plane} (hC : IsJordanCurve C) :
    ∃ P : GeneratedPair initialStructure C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1),
      P.str.CombInvariants ∧ P.src.IsAdmissible C (C ∪ inside C) ∧
        P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) :=
  ⟨(initialData hC).generatedPair, (initialData hC).generatedPair_combInvariants,
    (initialData hC).generatedPair_src_isAdmissible,
    (initialData hC).generatedPair_tgt_isAdmissible⟩

end Schoenflies
