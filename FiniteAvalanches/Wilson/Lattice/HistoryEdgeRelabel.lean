import FiniteAvalanches.Wilson.Lattice.HistoryListEdges
import FiniteAvalanches.Wilson.Lattice.HistoryColorRelabel

/-! Relabeling edges in finite Wilson branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- The edges of a vertex list commute with relabeling. -/
theorem vertexListEdges_map (f : V → W) (l : List V) :
    vertexListEdges (l.map f) = (vertexListEdges l).image (Sym2.map f) := by
  induction l with
  | nil => simp [vertexListEdges]
  | cons x xs ih =>
    cases xs with
    | nil => simp [vertexListEdges]
    | cons y ys =>
      have ih' := ih
      ext e
      simp only [vertexListEdges, List.map_cons, List.tail_cons, List.zip_cons_cons,
        List.toFinset_cons, Finset.image_insert, Finset.mem_insert, Sym2.map_mk] at ih' ⊢
      rw [ih']

/-- Compatible branch histories have the same edges after relabeling. -/
theorem branchHistoryEdgeSet_map_eq (head : V → FiniteWired.Direction → V)
    (head' : W → FiniteWired.Direction → W) (x : ℕ → V) (y : ℕ → W)
    (f : V → W) (T : Set V) (n : ℕ) (h : BranchHistory n)
    (hc : BranchHistory.ColorCompatible head head' x y f T n h) :
    (branchHistoryEdgeSet head x n h).image (Sym2.map f) = branchHistoryEdgeSet head' y n h := by
  letI : Quiver V := instructionQuiver head
  letI : Quiver W := instructionQuiver head'
  induction n with
  | zero => simp only [branchHistoryEdgeSet, Finset.image_empty]
  | succ n ih =>
    let p := loopErase (historyTrace head (x n) h.2).2
    let q := loopErase (historyTrace head' (y n) h.2).2
    have hvtx : p.vertices.map f = q.vertices := hc.2.2.2
    change (branchHistoryEdgeSet head x n h.1 ∪ pathUndirectedEdges p).image (Sym2.map f) =
      branchHistoryEdgeSet head' y n h.1 ∪ pathUndirectedEdges q
    rw [Finset.image_union, ih h.1 hc.1, pathUndirectedEdges_eq_vertexListEdges,
      pathUndirectedEdges_eq_vertexListEdges, ← vertexListEdges_map f p.vertices, hvtx]

end
end FiniteAvalanches.Wilson.Lattice
