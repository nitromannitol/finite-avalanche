import FiniteAvalanches.Wilson.Lattice.SamplerFirstRootPath

/-! Finite edge-coordinate distributions of the recurrent Wilson sampler. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- The edge coordinates observed after a finite sampler run. -/
def samplerEdgeObservation (R : RootPair) (L : List (Site 2)) (E : Finset LatticeEdge)
    (rows : ℕ → WalkDriver) : E → Bool :=
  match samplerRun (initialSampler R) L rows with
  | none => fun _ => false
  | some st => fun e => samplerEdgeField st e.val

/-- A successful run gives its recorded edge indicators. -/
theorem samplerEdgeObservation_of_success (R : RootPair) (L : List (Site 2))
    (E : Finset LatticeEdge) (rows : ℕ → WalkDriver) (st : SamplerState)
    (h : samplerRun (initialSampler R) L rows = some st) :
    samplerEdgeObservation R L E rows = fun e => samplerEdgeField st e.val := by
  simp only [samplerEdgeObservation, h]

/-- Finite edge observations of the partial sampler are measurable. -/
theorem measurable_samplerEdgeObservation (R : RootPair) (L : List (Site 2))
    (E : Finset LatticeEdge) : Measurable (samplerEdgeObservation R L E) := by
  apply measurable_pi_iff.mpr
  intro e
  apply measurable_to_bool
  have he : (fun rows => samplerEdgeObservation R L E rows e) ⁻¹' {true} =
      samplerEvent R L {e.val} ∅ (fun _ => true) (fun _ => false) := by
    ext rows
    simp only [Set.mem_preimage, Set.mem_singleton_iff, samplerEvent, Set.mem_setOf_eq]
    cases hs : samplerRun (initialSampler R) L rows with
    | none => simp [samplerEdgeObservation, hs]
    | some st =>
      simp [samplerEdgeObservation, hs, samplerEdgeField]
  rw [he]
  exact measurableSet_samplerEvent R L {e.val} ∅ (fun _ => true) (fun _ => false)

/-- Restriction of the full field to a finite family of lattice edges. -/
def restrictEdgeField (E : Finset LatticeEdge) (ω : ForestField) : E → Bool :=
  fun e => ω.1 e.val

/-- Restriction of the full field to finitely many edge coordinates is measurable. -/
theorem measurable_restrictEdgeField (E : Finset LatticeEdge) :
    Measurable (restrictEdgeField E) := by
  exact measurable_pi_iff.mpr fun e => (measurable_pi_apply e.val).comp measurable_fst

/-- Every finite edge marginal of the cylinder law is the corresponding
finite recurrent sampler marginal when the query covers the observed endpoints. -/
theorem IsWilsonCylinderLaw.map_restrictEdgeField (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (q : ℕ → Site 2) (n : ℕ) (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, q i = z) :
    (ν : Measure ForestField).map (restrictEdgeField E) =
      wilsonRows.map (samplerEdgeObservation R ((List.range n).map q) E) := by
  let L := (List.range n).map q
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_restrictEdgeField E) (measurableSet_singleton p),
    Measure.map_apply (measurable_samplerEdgeObservation R L E) (measurableSet_singleton p)]
  let pe : LatticeEdge → Bool := fun e => if he : e ∈ E then p ⟨e, he⟩ else false
  have hfield : restrictEdgeField E ⁻¹' {p} = jointEvent E ∅ pe (fun _ => false) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, jointEvent, Set.mem_setOf_eq,
      Finset.notMem_empty, IsEmpty.forall_iff]
    constructor
    · intro h
      refine ⟨?_, by simp⟩
      intro e he
      have hh := congrFun h ⟨e, he⟩
      simpa only [restrictEdgeField, pe, dif_pos he] using hh
    · intro h
      funext e
      exact (h.1 e.val e.property).trans (by simp only [pe, dif_pos e.property])
  rw [hfield, hν q n E ∅ pe (fun _ => false) hE (by simp)]
  apply measure_congr
  filter_upwards [samplerRun_ae_success R L] with rows hsuccess
  obtain ⟨st, hs⟩ := hsuccess
  change (rows ∈ samplerEvent R L E ∅ pe (fun _ => false)) =
    (samplerEdgeObservation R L E rows = p)
  apply propext
  symm
  change (samplerEdgeObservation R L E rows = p) ↔
    (∃ st, samplerRun (initialSampler R) L rows = some st ∧
      (∀ e ∈ E, decide (e.val ∈ st.edges) = pe e) ∧
      ∀ d ∈ (∅ : Finset (Site 2)), st.colors d = some false)
  have hobs := samplerEdgeObservation_of_success R L E rows st hs
  rw [hobs]
  constructor
  · intro h
    refine ⟨st, hs, ?_, by simp⟩
    intro e he
    have hh := congrFun h ⟨e, he⟩
    simpa only [samplerEdgeField, pe, dif_pos he] using hh
  · rintro ⟨st', hs', he, _⟩
    have hst : st = st' := Option.some.inj (hs.symm.trans hs')
    subst st'
    funext e
    simpa only [samplerEdgeField, pe, dif_pos e.property] using he e.val e.property

end
end FiniteAvalanches.Wilson.Lattice
