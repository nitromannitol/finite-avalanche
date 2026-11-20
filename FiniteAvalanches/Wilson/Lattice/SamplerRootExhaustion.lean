import FiniteAvalanches.Wilson.Lattice.RootEdgeExhaustion

/-! Exhausted finite observations retain the first Wilson root path. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- A successful finite run beginning at the specified query preserves every
edge from its first successful step. -/
theorem samplerRun_firstStep_edges_subset (R : RootPair) (x : Site 2)
    (q : ℕ → Site 2) (n : ℕ) (rows : ℕ → WalkDriver) (mid out : SamplerState)
    (hq : q 0 = x) (hn : 0 < n)
    (hmid : samplerStep (initialSampler R) x (rows 0) = some mid)
    (hout : samplerRun (initialSampler R) ((List.range n).map q) rows = some out) :
    mid.edges ⊆ out.edges := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hL : (List.range (n + 1)).map q =
      x :: (List.range n).map (fun i => q (i + 1)) := by
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, hq, Function.comp_def,
      Nat.succ_eq_add_one]
  rw [hL] at hout
  have htail : samplerRun mid ((List.range n).map (fun i => q (i + 1)))
      (fun i => rows (i + 1)) = some out := by
    simpa only [samplerRun, hmid, Option.bind_some] using hout
  exact samplerRun_edges_subset htail

/-- Once a finite observation contains a first-step root path, every successful
run beginning at that step displays a root connection in its edge pattern. -/
theorem samplerEdgeObservation_mem_rootPattern (R : RootPair) (x : Site 2)
    (q : ℕ → Site 2) (n : ℕ) (E : Finset LatticeEdge) (rows : ℕ → WalkDriver)
    (mid out : SamplerState) (r : Site 2) (p : (lattice 2).Walk x r)
    (hq : q 0 = x) (hn : 0 < n) (hr : r ∈ R.zero ∪ R.one)
    (hmid : samplerStep (initialSampler R) x (rows 0) = some mid)
    (hout : samplerRun (initialSampler R) ((List.range n).map q) rows = some out)
    (hp : ∀ e ∈ p.edges, e ∈ (toGraph (samplerEdgeField mid)).edgeSet)
    (hE : walkLatticeEdges p ⊆ E) :
    samplerEdgeObservation R ((List.range n).map q) E rows ∈ rootConnectionPattern R x E := by
  have hsub := samplerRun_firstStep_edges_subset R x q n rows mid out hq hn hmid hout
  rw [samplerEdgeObservation_of_success R _ E rows out hout]
  refine ⟨r, hr, p, hE, ?_⟩
  intro e he
  have he' : e.val ∈ p.edges := (mem_walkLatticeEdges p e).mp he
  have hm : samplerEdgeField mid e = true := (edge_mem_toGraph_iff _ e).mp (hp e.val he')
  have hm' : e.val ∈ mid.edges := by simpa only [samplerEdgeField, decide_eq_true_eq] using hm
  simpa only [samplerEdgeField, decide_eq_true_eq] using hsub hm'

/-- Almost surely, all sufficiently large finite observations contain a
root path from their designated first query. -/
theorem wilsonRows_ae_eventually_rootConnectionPattern (R : RootPair) (x : Site 2) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ n : ℕ in atTop,
      samplerEdgeObservation R
        ((List.range (rootEdgeQueryLength x (finiteEdgeExhaustion n))).map
          (rootEdgeQueries x (finiteEdgeExhaustion n))) (finiteEdgeExhaustion n) rows ∈
        rootConnectionPattern R x (finiteEdgeExhaustion n) := by
  have hfirst : ∀ᵐ rows ∂wilsonRows, ∃ mid,
      samplerStep (initialSampler R) x (rows 0) = some mid := by
    filter_upwards [samplerRun_ae_success R [x]] with rows hrows
    obtain ⟨mid, hm⟩ := hrows
    cases hs : samplerStep (initialSampler R) x (rows 0) with
    | none => simp [samplerRun, hs] at hm
    | some st => exact ⟨st, rfl⟩
  have hall : ∀ᵐ rows ∂wilsonRows, ∀ n : ℕ, ∃ out,
      samplerRun (initialSampler R)
        ((List.range (rootEdgeQueryLength x (finiteEdgeExhaustion n))).map
          (rootEdgeQueries x (finiteEdgeExhaustion n))) rows = some out := by
    apply ae_all_iff.mpr
    intro n
    exact samplerRun_ae_success R _
  filter_upwards [hfirst, hall] with rows hmid hall'
  obtain ⟨mid, hm⟩ := hmid
  obtain ⟨r, hr, ⟨p⟩⟩ := samplerStep_initial_reaches_root R x (rows 0) mid hm
  let p' := p.mapLe (toGraph_le_lattice (samplerEdgeField mid))
  have hp : ∀ e ∈ p'.edges, e ∈ (toGraph (samplerEdgeField mid)).edgeSet := by
    intro e he
    apply p.edges_subset_edgeSet
    simpa only [p', SimpleGraph.Walk.edges_mapLe_eq_edges] using he
  filter_upwards [eventually_subset_finiteEdgeExhaustion (walkLatticeEdges p')] with n hE
  obtain ⟨out, hout⟩ := hall' n
  have hq := rootEdgeQueries_spec x (finiteEdgeExhaustion n)
  exact samplerEdgeObservation_mem_rootPattern R x _ _ _ rows mid out r p'
    hq.1 hq.2.1 hr hm hout hp hE

end
end FiniteAvalanches.Wilson.Lattice
