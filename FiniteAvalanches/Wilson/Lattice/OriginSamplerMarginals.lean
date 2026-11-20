import FiniteAvalanches.Wilson.Lattice.OriginSamplerRootPath
import FiniteAvalanches.Wilson.Lattice.FiniteUstWeakLimit

/-! Finite edge marginals of weak wired limits and the origin sampler. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Edge coordinates revealed by an origin-rooted finite sampler run. -/
def originSamplerEdgeObservation (L : List (Site 2)) (E : Finset LatticeEdge)
    (rows : ℕ → WalkDriver) : E → Bool :=
  match samplerRun originInitialSampler L rows with
  | none => fun _ => false
  | some st => fun e => samplerEdgeField st e.val

/-- A successful origin sampler run gives the recorded edge observations. -/
theorem originSamplerEdgeObservation_of_success (L : List (Site 2)) (E : Finset LatticeEdge)
    (rows : ℕ → WalkDriver) (st : SamplerState) (h : samplerRun originInitialSampler L rows = some st) :
    originSamplerEdgeObservation L E rows = fun e => samplerEdgeField st e.val := by
  simp only [originSamplerEdgeObservation, h]

/-- Origin sampler edge observations are measurable. -/
theorem measurable_originSamplerEdgeObservation (L : List (Site 2)) (E : Finset LatticeEdge) :
    Measurable (originSamplerEdgeObservation L E) := by
  apply measurable_pi_iff.mpr
  intro e
  apply measurable_to_bool
  have he : (fun rows => originSamplerEdgeObservation L E rows e) ⁻¹' {true} =
      originSamplerEvent L {e.val} (fun _ => true) := by
    ext rows
    simp only [Set.mem_preimage, Set.mem_singleton_iff, originSamplerEvent, Set.mem_setOf_eq]
    cases hs : samplerRun originInitialSampler L rows with
    | none => simp [originSamplerEdgeObservation, hs]
    | some st => simp [originSamplerEdgeObservation, hs, samplerEdgeField]
  rw [he]
  exact measurableSet_originSamplerEvent L {e.val} (fun _ => true)

/-- Every weak wired limit has the finite edge distributions of the
origin-rooted Wilson exploration. -/
theorem wiredLimit_map_restrict (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν))
    (q : ℕ → Site 2) (n : ℕ) (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, q i = z) :
    (ν : Measure EdgeField).map E.restrict =
      wilsonRows.map (originSamplerEdgeObservation ((List.range n).map q) E) := by
  let L := (List.range n).map q
  apply Measure.ext_of_singleton
  intro p
  have hm : Measurable (E.restrict : EdgeField → E → Bool) :=
    measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)
  rw [Measure.map_apply hm (measurableSet_singleton p),
    Measure.map_apply (measurable_originSamplerEdgeObservation L E) (measurableSet_singleton p)]
  let pe : LatticeEdge → Bool := fun e => if he : e ∈ E then p ⟨e, he⟩ else false
  have hfield : (E.restrict : EdgeField → E → Bool) ⁻¹' {p} =
      FiniteAvalanches.Trees.Lattice.cylinder E p := rfl
  rw [hfield]
  have hfinite := finiteLaw_cylinder_tendsto_originSampler q (fun _ => 0) (fun _ _ => 0)
    (fun _ => rfl) n E p hE
  have hcluster := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hν (E := FiniteAvalanches.Trees.Lattice.cylinder E p) (by
      rw [(isClopen_cylinder E p).frontier_eq]
      exact measure_empty)
  rw [tendsto_nhds_unique hcluster hfinite]
  apply measure_congr
  filter_upwards [samplerRun_origin_ae_success L] with rows hsuccess
  obtain ⟨st, hs⟩ := hsuccess
  change (rows ∈ originSamplerEvent L E pe) =
    (originSamplerEdgeObservation L E rows = p)
  apply propext
  symm
  change (originSamplerEdgeObservation L E rows = p) ↔
    (∃ st, samplerRun originInitialSampler L rows = some st ∧
      ∀ e ∈ E, decide (e.val ∈ st.edges) = pe e)
  rw [originSamplerEdgeObservation_of_success L E rows st hs]
  constructor
  · intro h
    refine ⟨st, hs, ?_⟩
    intro e he
    have hh := congrFun h ⟨e, he⟩
    simpa only [samplerEdgeField, pe, dif_pos he] using hh
  · rintro ⟨st', hs', he⟩
    have hst : st = st' := Option.some.inj (hs.symm.trans hs')
    subst st'
    funext e
    simpa only [samplerEdgeField, pe, dif_pos e.property] using he e.val e.property

end
end FiniteAvalanches.Wilson.Lattice
