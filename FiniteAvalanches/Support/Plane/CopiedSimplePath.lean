import FiniteAvalanches.Electrical.Geometry.CopiedGraphPath
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

/-!
# Simple ordered paths of original copied edges

A copied walk contains a vertex-simple path using its original edge IDs, even
when the graph has loops or parallel copies.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
/-- A copied walk contains a vertex-simple ordered path using the selected copies. -/
theorem CopiedGraph.exists_simple_ordered_path (J : CopiedGraph V E) (S : Finset E)
    {u v : V} (h : J.reaches S u v) :
    ∃ (m : ℕ) (vertices : Fin (m + 1) → V) (copies : Fin m → E),
      Function.Injective vertices ∧ vertices 0 = u ∧ vertices (Fin.last m) = v ∧
      (∀ i, copies i ∈ S) ∧
      (∀ i, (J.left (copies i) = vertices i.castSucc ∧ J.right (copies i) = vertices i.succ) ∨
        (J.right (copies i) = vertices i.castSucc ∧ J.left (copies i) = vertices i.succ)) := by
  classical
  let K : CopiedGraph V {e : E // e ∈ S} := ⟨fun e => J.left e.val, fun e => J.right e.val⟩
  have hK : K.reaches Finset.univ u v := by
    induction h with
    | refl => exact .refl
    | tail _ hadj ih =>
      obtain ⟨e, he, hends⟩ := hadj
      exact ih.tail ⟨⟨e, he⟩, Finset.mem_univ _, hends⟩
  obtain ⟨p, hp⟩ := (K.supportGraph_reachable_of_reaches hK).exists_isPath
  let vertices : Fin (p.length + 1) → V := fun i => p.getVert i.val
  have hver : Function.Injective vertices := by
    intro i j hij
    apply Fin.ext
    apply hp.getVert_injOn (by simp; omega) (by simp; omega)
    exact hij
  have hedges : ∀ i : Fin p.length, ∃ e : {e : E // e ∈ S},
      (J.left e.val = vertices i.castSucc ∧ J.right e.val = vertices i.succ) ∨
      (J.right e.val = vertices i.castSucc ∧ J.left e.val = vertices i.succ) := by
    intro i
    obtain ⟨_, e, he⟩ := p.adj_getVert_succ i.isLt
    exact ⟨e, he⟩
  choose edges he using hedges
  refine ⟨p.length, vertices, fun i => (edges i).val, hver, ?_, ?_, ?_, he⟩
  · exact p.getVert_zero
  · exact p.getVert_length
  · intro i
    exact (edges i).property

end FiniteAvalanches.Electrical.StatementGeometry
