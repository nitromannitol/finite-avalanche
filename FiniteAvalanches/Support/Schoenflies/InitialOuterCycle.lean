/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/InitialOuterCycle.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.FiniteTransferTarget
import FiniteAvalanches.Support.Schoenflies.InitialPairFixed

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 













open Set
open scoped Graph

namespace Schoenflies

open Graph

 
theorem initOuter_isLink_edge (i : Fin 6) :
    initOuter.IsLink (.edge i) (.vert i) (.vert (i + 1)) :=
  ⟨⟨i, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

 
theorem initOuter_inc_iff {e x : InitialCell} :
    initOuter.Inc e x ↔
      e ∈ InitialCell.outerEdges ∧ (x = e.ends.1 ∨ x = e.ends.2) := by
  constructor
  · rintro ⟨y, he, hxy⟩
    rcases hxy with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨he, Or.inl rfl⟩
    · exact ⟨he, Or.inr rfl⟩
  · rintro ⟨⟨i, rfl⟩, rfl | rfl⟩
    · exact (initOuter_isLink_edge i).inc_left
    · exact (initOuter_isLink_edge i).inc_right

 
theorem isPath_initOuter_complement :
    initOuter.IsPath (.vert 0)
      [.edge 5, .edge 4, .edge 3, .edge 2, .edge 1] (.vert 1) := by
  refine .cons (initOuter_isLink_edge 5).symm
    (.cons (initOuter_isLink_edge 4).symm
      (.cons (initOuter_isLink_edge 3).symm
        (.cons (initOuter_isLink_edge 2).symm
          (Graph.IsPath.single (initOuter_isLink_edge 1).symm (by simp)) ?_) ?_) ?_) ?_
  all_goals
    simp [Graph.walkVertices, Graph.coveredVertices,
      initOuter_inc_iff, InitialCell.outerEdges, InitialCell.ends]

 
theorem outerEdgesFormCycle_initialStructure : initialStructure.OuterEdgesFormCycle := by
  refine ⟨.edge 0, .vert 0, .vert 1,
    [.edge 5, .edge 4, .edge 3, .edge 2, .edge 1], ?_, ?_⟩
  · exact ⟨initOuter_isLink_edge 0, isPath_initOuter_complement, by simp⟩
  · ext c
    change c ∈ InitialCell.outerEdges ↔
      c ∈ [InitialCell.edge 0, .edge 5, .edge 4, .edge 3, .edge 2, .edge 1]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, rfl⟩

end Schoenflies
