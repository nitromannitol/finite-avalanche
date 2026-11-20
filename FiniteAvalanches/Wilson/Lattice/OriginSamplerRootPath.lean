import FiniteAvalanches.Wilson.Lattice.OriginSamplerLimit
import FiniteAvalanches.Wilson.Lattice.SamplerFirstRootPath

/-! Root paths in the single-origin Wilson sampler. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The origin is the only site covered before exploration begins. -/
theorem originInitialSampler_covered : originInitialSampler.covered = {0} := by
  ext x
  simp [SamplerState.covered, originInitialSampler]

/-- The first origin-rooted Wilson branch joins its starting point to the origin. -/
theorem samplerStep_origin_reaches_zero (x : Site 2) (w : WalkDriver)
    (out : SamplerState) (hs : samplerStep originInitialSampler x w = some out) :
    (toGraph (samplerEdgeField out)).Reachable x 0 := by
  let st := originInitialSampler
  change samplerStep st x w = some out at hs
  by_cases hx : x ∈ st.covered
  · have hx0 : x = 0 := Set.mem_singleton_iff.mp (originInitialSampler_covered ▸ hx)
    subst x
    exact .refl _
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
    have hend0 : p.1 = 0 := Set.mem_singleton_iff.mp (originInitialSampler_covered ▸ hend)
    have hedges : out.edges = st.edges ∪ pathUndirectedEdges (loopErase p.2) :=
      samplerStep_edges_eq_history st out x k N w hN hs
    have hsub : pathUndirectedEdges (loopErase p.2) ⊆ out.edges := by
      rw [hedges]
      exact Finset.subset_union_right
    simpa only [hend0] using instructionPath_reachable (loopErase p.2) out hsub

/-- Later branches retain the first branch's connection to the origin. -/
theorem samplerRun_origin_reaches_zero (x : Site 2) (L : List (Site 2))
    (rows : ℕ → WalkDriver) (out : SamplerState)
    (hs : samplerRun originInitialSampler (x :: L) rows = some out) :
    (toGraph (samplerEdgeField out)).Reachable x 0 := by
  cases hstep : samplerStep originInitialSampler x (rows 0) with
  | none => simp [samplerRun, hstep] at hs
  | some mid =>
    have htail : samplerRun mid L (fun i => rows (i + 1)) = some out := by
      simpa only [samplerRun, hstep, Option.bind_some] using hs
    have hsub := samplerRun_edges_subset htail
    have hreach := samplerStep_origin_reaches_zero x (rows 0) mid hstep
    apply hreach.mono
    intro a b hab
    refine ⟨hab.1, ?_⟩
    have hin : s(a, b) ∈ mid.edges := by
      simpa only [samplerEdgeField, decide_eq_true_eq] using hab.2
    simpa only [samplerEdgeField, decide_eq_true_eq] using hsub hin

end
end FiniteAvalanches.Wilson.Lattice
