import FiniteAvalanches.Wilson.Lattice.WiredStackCopies
import FiniteAvalanches.Wilson.CyclePopping.RootedComponents

/-! Root components of the copied edges selected by wired direction arrows. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The original edge copy selected at every nonroot active vertex. -/
def wiredArrowCopies (R : RootPair) (N : ℕ)
    (a : GoodArrows (wiredRoots R N).val (wiredHead N)) : Finset (FiniteWired.Edge N) :=
  (Finset.univ.filter (fun x : FiniteWired.Active N => some x ∉ (wiredRoots R N).val)).image
    (fun x => FiniteWired.directionEdge x (a.val (some x)))

/-- Each nonroot vertex has its selected original copy in the arrow set. -/
theorem wiredArrowCopies_step (R : RootPair) (N : ℕ)
    (a : GoodArrows (wiredRoots R N).val (wiredHead N))
    (v : FiniteWired.Vertex N) (hv : v ∉ (wiredRoots R N).val) :
    (WiredTrees.graph N).adjacent (wiredArrowCopies R N a) v (wiredHead N v (a.val v)) := by
  cases v with
  | none => exact (hv (Or.inr trivial)).elim
  | some x =>
    refine ⟨FiniteWired.directionEdge x (a.val (some x)), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hv⟩, rfl⟩
    · exact wiredHead_direction_endpoints x (a.val (some x))

/-- Every edge in the selected-copy set is one of the nonroot arrows. -/
theorem wiredArrowCopies_adj (R : RootPair) (N : ℕ)
    (a : GoodArrows (wiredRoots R N).val (wiredHead N))
    (v w : FiniteWired.Vertex N)
    (h : (WiredTrees.graph N).adjacent (wiredArrowCopies R N a) v w) :
    rootwardAdj (wiredRoots R N).val (fun v => wiredHead N v (a.val v)) v w := by
  obtain ⟨e, he, hvw⟩ := h
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  have hroot := (Finset.mem_filter.mp hx).2
  have hed : rootwardAdj (wiredRoots R N).val (fun v => wiredHead N v (a.val v))
      (FiniteWired.endpoints (FiniteWired.directionEdge x (a.val (some x)))).1
      (FiniteWired.endpoints (FiniteWired.directionEdge x (a.val (some x)))).2 := by
    rcases wiredHead_direction_endpoints x (a.val (some x)) with h | h
    · rw [h.1, h.2]
      exact Or.inl ⟨hroot, rfl⟩
    · rw [h.1, h.2]
      exact Or.inr ⟨hroot, rfl⟩
  change ((FiniteWired.endpoints (FiniteWired.directionEdge x (a.val (some x)))).1 = v ∧
      (FiniteWired.endpoints (FiniteWired.directionEdge x (a.val (some x)))).2 = w) ∨
    ((FiniteWired.endpoints (FiniteWired.directionEdge x (a.val (some x)))).2 = v ∧
      (FiniteWired.endpoints (FiniteWired.directionEdge x (a.val (some x)))).1 = w) at hvw
  rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hed
  · exact hed.symm

/-- Every component of the selected wired copies has exactly one prescribed root. -/
theorem wiredArrowCopies_rooted_components (R : RootPair) (N : ℕ)
    (a : GoodArrows (wiredRoots R N).val (wiredHead N)) :
    ∀ x, ∃ r ∈ (wiredRoots R N).val,
      (WiredTrees.graph N).reaches (wiredArrowCopies R N a) x r ∧
      ∀ r' ∈ (wiredRoots R N).val,
        (WiredTrees.graph N).reaches (wiredArrowCopies R N a) x r' → r' = r := by
  apply rootward_components (WiredTrees.graph N) (wiredArrowCopies R N a)
    (wiredRoots R N).val (fun v => wiredHead N v (a.val v))
  · exact GoodArrows.reaches_root _ _ _ a.property
  · exact wiredArrowCopies_step R N a
  · exact wiredArrowCopies_adj R N a

end
end FiniteAvalanches.Wilson.Lattice
