import FiniteAvalanches.Wilson.Lattice.WiredAcyclicLimit

/-! Root paths recorded by the first successful Wilson exploration. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The lattice edge field recorded by a sampler state. -/
def samplerEdgeField (st : SamplerState) : EdgeField := fun e => decide (e.val ∈ st.edges)

/-- A lattice direction is a nearest-neighbor step. -/
theorem latticeDirectionHead_adj (x : Site 2) (d : FiniteWired.Direction) :
    (lattice 2).Adj x (latticeDirectionHead x d) := by
  simpa only [position_zero, position_succ, latticeDirectionHead] using
    position_adjacent x (fun _ => d) 0

/-- The undirected edges of an instruction path connect its endpoints. -/
theorem instructionPath_reachable {x y : Site 2}
    (p : letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead; Quiver.Path x y)
    (st : SamplerState)
    (he : letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
      pathUndirectedEdges p ⊆ st.edges) :
    (toGraph (samplerEdgeField st)).Reachable x y := by
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons b c p e ih =>
    have hp : pathUndirectedEdges p ⊆ st.edges :=
      (Finset.subset_union_left : pathUndirectedEdges p ⊆
        pathUndirectedEdges p ∪ {s(b, c)}).trans he
    have hc : s(b, c) ∈ st.edges := he (by simp only [pathUndirectedEdges,
      Finset.mem_union, Finset.mem_singleton, or_true])
    have hab : (lattice 2).Adj b c := e.property ▸ latticeDirectionHead_adj b e.val
    have hed : (toGraph (samplerEdgeField st)).Adj b c := by
      exact ⟨hab, by simp only [samplerEdgeField, decide_eq_true_eq]; exact hc⟩
    exact (ih hp).trans hed.reachable

/-- Successful steps retain all previously selected edges. -/
theorem samplerStep_edges_subset {st out : SamplerState} {x : Site 2} {w : WalkDriver}
    (h : samplerStep st x w = some out) : st.edges ⊆ out.edges := by
  by_cases hx : x ∈ st.covered
  · simp only [samplerStep, if_pos hx, Option.some.injEq] at h
    subst out
    exact Finset.Subset.rfl
  · cases ht : hitTime st.covered x w with
    | none => simp [samplerStep, hx, ht] at h
    | some t =>
      simp only [samplerStep, if_neg hx, ht, Option.some.injEq] at h
      subst out
      exact Finset.subset_union_left

/-- Successful runs retain every edge present at their start. -/
theorem samplerRun_edges_subset {st out : SamplerState} {L : List (Site 2)}
    {rows : ℕ → WalkDriver} (h : samplerRun st L rows = some out) : st.edges ⊆ out.edges := by
  induction L generalizing st rows with
  | nil =>
    have he : st = out := Option.some.inj h
    subst out
    exact Finset.Subset.rfl
  | cons x xs ih =>
    cases hs : samplerStep st x (rows 0) with
    | none => simp [samplerRun, hs] at h
    | some mid =>
      have ht : samplerRun mid xs (fun i => rows (i + 1)) = some out := by
        simpa only [samplerRun, hs, Option.bind_some] using h
      exact (samplerStep_edges_subset hs).trans (ih ht)

end
end FiniteAvalanches.Wilson.Lattice
