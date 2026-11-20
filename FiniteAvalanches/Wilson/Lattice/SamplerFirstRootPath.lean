import FiniteAvalanches.Wilson.Lattice.SamplerRootPath

/-! A successful first Wilson branch reaches a prescribed root. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The initially covered sites are precisely the prescribed roots. -/
theorem initialSampler_covered_roots (R : RootPair) :
    (initialSampler R).covered = R.zero ∪ R.one := by
  ext x
  simp only [SamplerState.covered, Set.mem_setOf_eq, initialSampler, Set.mem_union]
  split_ifs <;> simp_all

/-- The first successful exploration joins its query to a prescribed root by
edges recorded in its output state. -/
theorem samplerStep_initial_reaches_root (R : RootPair) (x : Site 2) (w : WalkDriver)
    (out : SamplerState) (hs : samplerStep (initialSampler R) x w = some out) :
    ∃ r ∈ R.zero ∪ R.one, (toGraph (samplerEdgeField out)).Reachable x r := by
  let st := initialSampler R
  change samplerStep st x w = some out at hs
  by_cases hx : x ∈ st.covered
  · exact ⟨x, initialSampler_covered_roots R ▸ hx, .refl x⟩
  · have hhit : ∃ t, position x w t ∈ st.covered := by
      cases ht : hitTime st.covered x w with
      | none => simp [samplerStep, hx, ht] at hs
      | some t => exact ⟨t, ((hitTime_eq_some_iff _ _ _ _).mp ht).1⟩
    let k : Cursor (Site 2) := fun _ => 0
    have hword : ∃ t, (wordState latticeDirectionHead x k w t).1 ∈ st.covered := by
      obtain ⟨t, ht⟩ := hhit
      exact ⟨t, (wordState_lattice_position x k w t).symm ▸ ht⟩
    obtain ⟨N, hN⟩ := exists_boundedWordHit_lt latticeDirectionHead st.covered x k w hword
    let t := boundedWordHit latticeDirectionHead st.covered x k N w
    letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
    let p := historyTrace latticeDirectionHead x (stoppedDirectionHistory (fun _ => t) w)
    have hend : p.1 ∈ st.covered :=
      (historyTrace_firstHit_of_boundedHit latticeDirectionHead st.covered x k N w hN).1
    have hedges : out.edges = st.edges ∪ pathUndirectedEdges (loopErase p.2) :=
      samplerStep_edges_eq_history st out x k N w hN hs
    have hsub : pathUndirectedEdges (loopErase p.2) ⊆ out.edges := by
      rw [hedges]
      exact Finset.subset_union_right
    exact ⟨p.1, initialSampler_covered_roots R ▸ hend,
      instructionPath_reachable (loopErase p.2) out hsub⟩

/-- A completed run beginning with a query retains its path to a root. -/
theorem samplerRun_initial_reaches_root (R : RootPair) (x : Site 2) (L : List (Site 2))
    (rows : ℕ → WalkDriver) (out : SamplerState)
    (hs : samplerRun (initialSampler R) (x :: L) rows = some out) :
    ∃ r ∈ R.zero ∪ R.one, (toGraph (samplerEdgeField out)).Reachable x r := by
  cases hstep : samplerStep (initialSampler R) x (rows 0) with
  | none => simp [samplerRun, hstep] at hs
  | some mid =>
    have htail : samplerRun mid L (fun i => rows (i + 1)) = some out := by
      simpa only [samplerRun, hstep, Option.bind_some] using hs
    have hsub := samplerRun_edges_subset htail
    obtain ⟨r, hr, hreach⟩ := samplerStep_initial_reaches_root R x (rows 0) mid hstep
    refine ⟨r, hr, hreach.mono ?_⟩
    intro a b hab
    refine ⟨hab.1, ?_⟩
    have hin : s(a, b) ∈ mid.edges := by
      simpa only [samplerEdgeField, decide_eq_true_eq] using hab.2
    simpa only [samplerEdgeField, decide_eq_true_eq] using hsub hin

end
end FiniteAvalanches.Wilson.Lattice
