import FiniteAvalanches.Wilson.Lattice.OriginSamplerMarginals
import FiniteAvalanches.Wilson.Lattice.RootEdgeExhaustion
import FiniteAvalanches.Wilson.Lattice.WiredLimitAcyclic

/-! Connectivity of weak wired spanning tree limits. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical ENNReal

noncomputable section

/-- A finite edge pattern contains a path from a site to the origin. -/
def originConnectionPattern (x : Site 2) (E : Finset LatticeEdge) : Set (E → Bool) :=
  {f | ∃ p : (lattice 2).Walk x 0, ∃ h : walkLatticeEdges p ⊆ E,
    ∀ e (he : e ∈ walkLatticeEdges p), f ⟨e, h he⟩ = true}

/-- Every finite path certificate gives a connection in the full edge field. -/
theorem restrict_originConnection_subset (x : Site 2) (E : Finset LatticeEdge) :
    E.restrict ⁻¹' originConnectionPattern x E ⊆
      {ω : EdgeField | (toGraph ω).Reachable x 0} := by
  rintro ω ⟨p, hsub, hp⟩
  exact walk_reachable_of_edge_values p ω (fun e he => hp e he)

/-- Connection to the origin is an open event. -/
theorem isOpen_originConnection (x : Site 2) :
    IsOpen {ω : EdgeField | (toGraph ω).Reachable x 0} := by
  have he : {ω : EdgeField | (toGraph ω).Reachable x 0} =
      ⋃ p : (lattice 2).Walk x 0, FiniteAvalanches.Trees.Lattice.cylinder (walkLatticeEdges p) (fun _ => true) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨p⟩
      let q := p.mapLe (toGraph_le_lattice ω)
      refine ⟨q, ?_⟩
      change (walkLatticeEdges q).restrict ω = fun _ => true
      funext e
      have hm : e.val.val ∈ p.edges := by
        have hq := (mem_walkLatticeEdges q e.val).mp e.property
        simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hq
      exact (edge_mem_toGraph_iff ω e.val).mp (p.edges_subset_edgeSet hm)
    · rintro ⟨p, hp⟩
      apply walk_reachable_of_edge_values p ω
      intro e he
      have h := congrFun hp ⟨e, he⟩
      exact h
  rw [he]
  exact isOpen_iUnion fun p => (isClopen_cylinder (walkLatticeEdges p) (fun _ => true)).isOpen

/-- The first step's edges remain present in every successful continuation. -/
theorem originSamplerRun_firstStep_edges_subset (x : Site 2)
    (q : ℕ → Site 2) (n : ℕ) (rows : ℕ → WalkDriver) (mid out : SamplerState)
    (hq : q 0 = x) (hn : 0 < n)
    (hmid : samplerStep originInitialSampler x (rows 0) = some mid)
    (hout : samplerRun originInitialSampler ((List.range n).map q) rows = some out) :
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

/-- Exhausted observations almost surely eventually contain the first branch's root path. -/
theorem wilsonRows_ae_eventually_originConnectionPattern (x : Site 2) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ n : ℕ in atTop,
      originSamplerEdgeObservation
        ((List.range (rootEdgeQueryLength x (finiteEdgeExhaustion n))).map
          (rootEdgeQueries x (finiteEdgeExhaustion n))) (finiteEdgeExhaustion n) rows ∈
        originConnectionPattern x (finiteEdgeExhaustion n) := by
  have hfirst : ∀ᵐ rows ∂wilsonRows, ∃ mid,
      samplerStep originInitialSampler x (rows 0) = some mid := by
    filter_upwards [samplerRun_origin_ae_success [x]] with rows hrows
    obtain ⟨mid, hm⟩ := hrows
    cases hs : samplerStep originInitialSampler x (rows 0) with
    | none => simp [samplerRun, hs] at hm
    | some st => exact ⟨st, rfl⟩
  have hall : ∀ᵐ rows ∂wilsonRows, ∀ n : ℕ, ∃ out,
      samplerRun originInitialSampler
        ((List.range (rootEdgeQueryLength x (finiteEdgeExhaustion n))).map
          (rootEdgeQueries x (finiteEdgeExhaustion n))) rows = some out := by
    apply ae_all_iff.mpr
    intro n
    exact samplerRun_origin_ae_success _
  filter_upwards [hfirst, hall] with rows hmid hall'
  obtain ⟨mid, hm⟩ := hmid
  obtain ⟨p⟩ := samplerStep_origin_reaches_zero x (rows 0) mid hm
  let p' := p.mapLe (toGraph_le_lattice (samplerEdgeField mid))
  have hp : ∀ e ∈ p'.edges, e ∈ (toGraph (samplerEdgeField mid)).edgeSet := by
    intro e he
    apply p.edges_subset_edgeSet
    simpa only [p', SimpleGraph.Walk.edges_mapLe_eq_edges] using he
  filter_upwards [eventually_subset_finiteEdgeExhaustion (walkLatticeEdges p')] with n hE
  obtain ⟨out, hout⟩ := hall' n
  have hq := rootEdgeQueries_spec x (finiteEdgeExhaustion n)
  have hsub := originSamplerRun_firstStep_edges_subset x _ _ rows mid out hq.1 hq.2.1 hm hout
  rw [originSamplerEdgeObservation_of_success _ _ rows out hout]
  refine ⟨p', hE, ?_⟩
  intro e he
  have he' : e.val ∈ p'.edges := (mem_walkLatticeEdges p' e).mp he
  have hm' : samplerEdgeField mid e = true := (edge_mem_toGraph_iff _ e).mp (hp e.val he')
  have hm'' : e.val ∈ mid.edges := by simpa only [samplerEdgeField, decide_eq_true_eq] using hm'
  simpa only [samplerEdgeField, decide_eq_true_eq] using hsub hm''

/-- A weak wired UST limit almost surely connects each site to the origin. -/
theorem wiredLimit_ae_reaches_origin (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) (x : Site 2) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), (toGraph ω).Reachable x 0 := by
  let A : ℕ → Set (ℕ → WalkDriver) := fun n =>
    originSamplerEdgeObservation
      ((List.range (rootEdgeQueryLength x (finiteEdgeExhaustion n))).map
        (rootEdgeQueries x (finiteEdgeExhaustion n))) (finiteEdgeExhaustion n) ⁻¹'
      originConnectionPattern x (finiteEdgeExhaustion n)
  have hA : ∀ n, MeasurableSet (A n) := by
    intro n
    exact ((Set.to_countable (originConnectionPattern x (finiteEdgeExhaustion n))).measurableSet).preimage
      (measurable_originSamplerEdgeObservation _ _)
  have hpoint : ∀ᵐ rows ∂wilsonRows, ∀ᶠ n : ℕ in atTop,
      rows ∈ A n ↔ rows ∈ (Set.univ : Set (ℕ → WalkDriver)) := by
    filter_upwards [wilsonRows_ae_eventually_originConnectionPattern x] with rows hrows
    filter_upwards [hrows] with n hn
    simp only [Set.mem_univ, iff_true]
    exact hn
  have ht : Tendsto (fun n => wilsonRows (A n)) atTop (nhds 1) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      (μ := wilsonRows) (A := Set.univ) (As := A) MeasurableSet.univ hA hpoint
    simpa only [measure_univ] using h
  have hb : ∀ n, wilsonRows (A n) ≤
      (ν : Measure EdgeField) {ω | (toGraph ω).Reachable x 0} := by
    intro n
    let E := finiteEdgeExhaustion n
    let q := rootEdgeQueries x E
    let m := rootEdgeQueryLength x E
    have hq := rootEdgeQueries_spec x E
    have hmap := wiredLimit_map_restrict ν hν q m E hq.2.2
    have hm : MeasurableSet (originConnectionPattern x E) :=
      (Set.to_countable _).measurableSet
    have heq := congrArg (fun μ : Measure (E → Bool) => μ (originConnectionPattern x E)) hmap
    have hre : Measurable (E.restrict : EdgeField → E → Bool) :=
      measurable_pi_lambda _ (fun e => measurable_pi_apply e.val)
    rw [Measure.map_apply hre hm, Measure.map_apply (measurable_originSamplerEdgeObservation _ _) hm] at heq
    change wilsonRows (originSamplerEdgeObservation ((List.range m).map q) E ⁻¹'
      originConnectionPattern x E) ≤ _
    rw [← heq]
    exact measure_mono (restrict_originConnection_subset x E)
  have hlower : 1 ≤ (ν : Measure EdgeField) {ω | (toGraph ω).Reachable x 0} :=
    le_of_tendsto ht (Eventually.of_forall hb)
  have hupper : (ν : Measure EdgeField) {ω | (toGraph ω).Reachable x 0} ≤ 1 := by
    simpa only [measure_univ] using
      (measure_mono (μ := (ν : Measure EdgeField))
        (Set.subset_univ {ω | (toGraph ω).Reachable x 0}))
  exact (mem_ae_iff_prob_eq_one (isOpen_originConnection x).measurableSet).mpr
    (le_antisymm hupper hlower)

/-- Every weak wired UST limit is almost surely a spanning tree. -/
theorem wiredLimit_ae_tree (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), IsTree ω := by
  have hconn : ∀ᵐ ω ∂(ν : Measure EdgeField), ∀ x : Site 2,
      (toGraph ω).Reachable x 0 := by
    apply ae_all_iff.mpr
    exact wiredLimit_ae_reaches_origin ν hν
  filter_upwards [wiredLimit_ae_acyclic ν hν, hconn] with ω hac hconn'
  exact ⟨⟨fun x y => (hconn' x).trans (hconn' y).symm⟩, hac⟩

end
end FiniteAvalanches.Wilson.Lattice
