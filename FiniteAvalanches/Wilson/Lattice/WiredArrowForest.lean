import FiniteAvalanches.Wilson.Lattice.WiredArrowComponents
import FiniteAvalanches.Wilson.CyclePopping.RootwardForest

/-! Cycle-free wired arrows determine a forest of original edge copies. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

private def originActive (N : ℕ) : FiniteWired.Active N :=
  fun _ => ⟨0, by constructor <;> omega⟩

/-- The original copy selected by a wired direction at a nonroot vertex. -/
def wiredArrowEdge (R : RootPair) (N : ℕ)
    (a : GoodArrows (wiredRoots R N).val (wiredHead N)) :
    FiniteWired.Vertex N → FiniteWired.Edge N
  | none => FiniteWired.directionEdge (originActive N) (0, false)
  | some x => FiniteWired.directionEdge x (a.val (some x))

/-- The general nonroot-arrow copy set is the wired arrow-copy set. -/
theorem rootwardCopies_wiredArrowEdge (R : RootPair) (N : ℕ)
    (a : GoodArrows (wiredRoots R N).val (wiredHead N)) :
    rootwardCopies (wiredRoots R N).val (wiredArrowEdge R N a) = wiredArrowCopies R N a := by
  ext e
  constructor
  · intro he
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp he
    have hvR := (Finset.mem_filter.mp hv).2
    cases v with
    | none => exact (hvR (Or.inr trivial)).elim
    | some x =>
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hvR⟩, he⟩
  · intro he
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨some x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hx).2⟩, he⟩

/-- A cycle-free wired direction assignment selects a rooted forest of the
original interior and exit edge copies. -/
theorem wiredArrowCopies_is_rooted_forest (R : RootPair) (N : ℕ)
    (a : GoodArrows (wiredRoots R N).val (wiredHead N)) :
    (WiredTrees.graph N).is_rooted_forest (wiredRoots R N).val (wiredArrowCopies R N a) := by
  rw [← rootwardCopies_wiredArrowEdge R N a]
  apply rootwardCopies_is_rooted_forest (WiredTrees.graph N) (wiredRoots R N).val
    (fun v => wiredHead N v (a.val v)) (wiredArrowEdge R N a)
  · exact GoodArrows.reaches_root _ _ _ a.property
  · intro v hv
    cases v with
    | none => exact (hv (Or.inr trivial)).elim
    | some x => exact wiredHead_direction_endpoints x (a.val (some x))

/-- The rooted forest selected by a cycle-free wired direction assignment. -/
def wiredArrowForest (R : RootPair) (N : ℕ)
    (a : GoodArrows (wiredRoots R N).val (wiredHead N)) : FiniteForest R N :=
  ⟨wiredArrowCopies R N a, wiredArrowCopies_is_rooted_forest R N a⟩

end
end FiniteAvalanches.Wilson.Lattice
