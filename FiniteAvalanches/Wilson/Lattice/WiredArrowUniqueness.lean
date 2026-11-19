import FiniteAvalanches.Wilson.Lattice.WiredArrowForest
import FiniteAvalanches.Wilson.CyclePopping.RootwardUniqueness

/-! A wired rooted forest determines every nonroot direction. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Equal rooted forests select equal directions at every nonroot vertex. -/
theorem wiredArrowForest_eq_imp_nonroot_eq (R : RootPair) (N : ℕ)
    (a b : GoodArrows (wiredRoots R N).val (wiredHead N))
    (h : wiredArrowForest R N a = wiredArrowForest R N b)
    {v : FiniteWired.Vertex N} (hv : v ∉ (wiredRoots R N).val) : a.val v = b.val v := by
  have hF : rootwardCopies (wiredRoots R N).val (wiredArrowEdge R N a) =
      rootwardCopies (wiredRoots R N).val (wiredArrowEdge R N b) := by
    rw [rootwardCopies_wiredArrowEdge R N a, rootwardCopies_wiredArrowEdge R N b]
    exact congrArg Subtype.val h
  have hend (c : GoodArrows (wiredRoots R N).val (wiredHead N)) :
      ∀ v ∉ (wiredRoots R N).val,
        ((WiredTrees.graph N).left (wiredArrowEdge R N c v) = v ∧
          (WiredTrees.graph N).right (wiredArrowEdge R N c v) = wiredHead N v (c.val v)) ∨
        ((WiredTrees.graph N).right (wiredArrowEdge R N c v) = v ∧
          (WiredTrees.graph N).left (wiredArrowEdge R N c v) = wiredHead N v (c.val v)) := by
    intro v hv
    cases v with
    | none => exact (hv (Or.inr trivial)).elim
    | some x => exact wiredHead_direction_endpoints x (c.val (some x))
  have he := rootwardCopies_eq_imp_edge_eq (WiredTrees.graph N) (wiredRoots R N).val
    (fun v => wiredHead N v (a.val v)) (fun v => wiredHead N v (b.val v))
    (wiredArrowEdge R N a) (wiredArrowEdge R N b)
    (GoodArrows.reaches_root _ _ _ a.property) (GoodArrows.reaches_root _ _ _ b.property)
    (hend a) (hend b) hF hv
  cases v with
  | none => exact (hv (Or.inr trivial)).elim
  | some x => exact Components.direction_edge_injective x he

/-- Directions at roots do not affect the selected wired forest. -/
theorem wiredArrowForest_eq_of_nonroot_eq (R : RootPair) (N : ℕ)
    (a b : GoodArrows (wiredRoots R N).val (wiredHead N))
    (h : ∀ v ∉ (wiredRoots R N).val, a.val v = b.val v) :
    wiredArrowForest R N a = wiredArrowForest R N b := by
  apply Subtype.ext
  change wiredArrowCopies R N a = wiredArrowCopies R N b
  apply Finset.image_congr
  intro x hx
  exact congrArg (FiniteWired.directionEdge x) (h (some x) (Finset.mem_filter.mp hx).2)

/-- Two cycle-free direction assignments give the same forest exactly when
they agree away from the roots. -/
theorem wiredArrowForest_eq_iff (R : RootPair) (N : ℕ)
    (a b : GoodArrows (wiredRoots R N).val (wiredHead N)) :
    wiredArrowForest R N a = wiredArrowForest R N b ↔
      ∀ v ∉ (wiredRoots R N).val, a.val v = b.val v :=
  ⟨fun h _ hv => wiredArrowForest_eq_imp_nonroot_eq R N a b h hv,
    wiredArrowForest_eq_of_nonroot_eq R N a b⟩

end
end FiniteAvalanches.Wilson.Lattice
