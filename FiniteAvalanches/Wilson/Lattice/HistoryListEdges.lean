import FiniteAvalanches.Wilson.Lattice.HistoryRootwardEdges
import FiniteAvalanches.Wilson.Lattice.SamplerColorPropagation

/-! List and quiver representations of Wilson branch edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Unoriented edges between successive vertices of a finite list. -/
def vertexListEdges (l : List V) : Finset (Sym2 V) :=
  ((l.zip l.tail).map fun p => s(p.1, p.2)).toFinset

/-- Appending one vertex appends the edge from the previous endpoint. -/
theorem vertexListEdges_snoc (l : List V) (b c : V) :
    vertexListEdges (l ++ [b, c]) = vertexListEdges (l ++ [b]) ∪ {s(b, c)} := by
  induction l with
  | nil => simp [vertexListEdges]
  | cons x xs ih =>
    cases xs with
    | nil => simp [vertexListEdges]
    | cons y ys =>
      have ih' := ih
      ext e
      simp only [vertexListEdges, List.cons_append, List.tail_cons, List.zip_cons_cons,
        List.map_cons, List.toFinset_cons, Finset.mem_insert, Finset.mem_union,
        Finset.mem_singleton] at ih' ⊢
      rw [ih']
      simp only [Finset.mem_union, Finset.mem_singleton, or_assoc]

/-- The list of vertices of a quiver path gives exactly its unoriented edges. -/
theorem pathUndirectedEdges_eq_vertexListEdges [Quiver V] {a b : V} (p : Path a b) :
    pathUndirectedEdges p = vertexListEdges p.vertices := by
  induction p with
  | nil => simp [pathUndirectedEdges, vertexListEdges, Path.vertices]
  | @cons b c p e ih =>
    rw [pathUndirectedEdges, ih, Path.vertices_cons, List.concat_eq_append]
    have he := vertexListEdges_snoc p.vertices.dropLast b c
    rw [Path.dropLast_append_end_eq] at he
    have hh : p.vertices.dropLast ++ [b, c] = p.vertices ++ [c] := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        congrArg (fun l : List V => l ++ [c]) (Path.dropLast_append_end_eq p)
    rw [hh] at he
    exact he.symm

/-- Lattice list-edge extraction agrees with quiver path-edge extraction. -/
theorem branchEdges_eq_pathUndirectedEdges {a b : Site 2}
    (p : letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead; Quiver.Path a b) :
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    branchEdges p.vertices = pathUndirectedEdges p := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  exact (pathUndirectedEdges_eq_vertexListEdges p).symm

/-- A successful sampler step adds exactly the edges of its recorded erased branch. -/
theorem samplerStep_edges_eq_history (st out : SamplerState) (x : Site 2)
    (k : Cursor (Site 2)) (N : ℕ) (w : WalkDriver)
    (h : boundedWordHit latticeDirectionHead st.covered x k N w < N)
    (hs : samplerStep st x w = some out) :
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    let t := boundedWordHit latticeDirectionHead st.covered x k N w
    let p := historyTrace latticeDirectionHead x (stoppedDirectionHistory (fun _ => t) w)
    out.edges = st.edges ∪ pathUndirectedEdges (loopErase p.2) := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  let t := boundedWordHit latticeDirectionHead st.covered x k N w
  let p := historyTrace latticeDirectionHead x (stoppedDirectionHistory (fun _ => t) w)
  have ht : hitTime st.covered x w = some t := hitTime_eq_boundedWordHit st.covered x k N w h
  have he : (loopErase p.2).vertices = walkErase x w t :=
    historyTrace_stopped_loopErase_vertices x w t
  have hedge : pathUndirectedEdges (loopErase p.2) = branchEdges (walkErase x w t) := by
    rw [← branchEdges_eq_pathUndirectedEdges, he]
  change out.edges = st.edges ∪ pathUndirectedEdges (loopErase p.2)
  rw [hedge]
  by_cases hx : x ∈ st.covered
  · have ht0 : hitTime st.covered x w = some 0 := by
      apply (hitTime_eq_some_iff _ _ _ _).mpr
      exact ⟨by simpa only [position_zero] using hx, by simp⟩
    have ht' : t = 0 := Option.some.inj (ht.symm.trans ht0)
    have hout : out = st := by simpa only [samplerStep, if_pos hx, Option.some.injEq] using hs.symm
    subst out
    rw [ht']
    simp [walkErase, eraseStep, branchEdges]
  · simp only [samplerStep, if_neg hx, ht, Option.some.injEq] at hs
    subst out
    rfl

/-- The lattice sampler edge set is the initial edge set together with the
edges of all its successful recorded branches. -/
theorem samplerRun_edges_eq_branchHistoryEdgeSet (st : SamplerState) (x : ℕ → Site 2)
    (k : Cursor (Site 2)) (N n : ℕ) (rows : ℕ → WalkDriver) (out : SamplerState)
    (h : ∀ i < n, (rowBranchHistory latticeDirectionHead x st.covered k N rows (i + 1)).2.1 < N)
    (hs : samplerRun st ((List.range n).map x) rows = some out) :
    out.edges = st.edges ∪ branchHistoryEdgeSet latticeDirectionHead x n
      (rowBranchHistory latticeDirectionHead x st.covered k N rows n) := by
  induction n generalizing out with
  | zero =>
    have he : st = out := Option.some.inj hs
    subst out
    simp only [branchHistoryEdgeSet, Finset.union_empty]
  | succ n ih =>
    have hpast : ∀ i < n,
        (rowBranchHistory latticeDirectionHead x st.covered k N rows (i + 1)).2.1 < N :=
      fun i hi => h i (Nat.lt_succ_of_lt hi)
    obtain ⟨mid, hmid, hroots⟩ := samplerRun_covered_eq_rowBranchHistory st x k N n rows hpast
    have hedges := ih mid hpast hmid
    let a := rowBranchHistory latticeDirectionHead x st.covered k N rows n
    let c := branchHistoryCursor latticeDirectionHead x k n a
    let t := boundedWordHit latticeDirectionHead mid.covered (x n) c N (rows n)
    have hhit : t < N := by
      change boundedWordHit latticeDirectionHead mid.covered (x n) c N (rows n) < N
      rw [hroots]
      exact h n (Nat.lt_succ_self n)
    have hstep : samplerStep mid (x n) (rows n) = some out := by
      rw [List.range_succ, List.map_append, samplerRun_append_rows, hmid] at hs
      simp only [Option.bind_some, List.map_singleton, List.length_map, List.length_range,
        samplerRun, Nat.zero_add] at hs
      cases he : samplerStep mid (x n) (rows n) with
      | none =>
        simp only [he, Option.bind_none] at hs
        cases hs
      | some s => simpa only [he, Option.bind_some] using hs
    have hed := samplerStep_edges_eq_history mid out (x n) c N (rows n) hhit hstep
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    let p := historyTrace latticeDirectionHead (x n) (stoppedDirectionHistory (fun _ => t) (rows n))
    change out.edges = mid.edges ∪ pathUndirectedEdges (loopErase p.2) at hed
    have he : boundedWordHit latticeDirectionHead
        (branchHistoryRoots latticeDirectionHead x st.covered n a) (x n) c N (rows n) = t := by
      change boundedWordHit latticeDirectionHead _ (x n) c N (rows n) = _
      rw [← hroots]
    change out.edges = st.edges ∪ branchHistoryEdgeSet latticeDirectionHead x (n + 1)
      (a, stoppedDirectionHistory (boundedWordHit latticeDirectionHead
        (branchHistoryRoots latticeDirectionHead x st.covered n a) (x n) c N) (rows n))
    simp only [stoppedDirectionHistory]
    rw [he]
    change out.edges = st.edges ∪ (branchHistoryEdgeSet latticeDirectionHead x n a ∪
      pathUndirectedEdges (loopErase p.2))
    rw [hed, hedges, Finset.union_assoc]

end
end FiniteAvalanches.Wilson.Lattice
