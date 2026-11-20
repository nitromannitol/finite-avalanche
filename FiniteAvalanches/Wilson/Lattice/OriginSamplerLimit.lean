import FiniteAvalanches.Wilson.Lattice.DistantOriginForestLaw
import FiniteAvalanches.Wilson.Lattice.RootContinuity

/-! Wilson explorations with a single root as distant roots move to infinity. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The initial Wilson state with the lattice origin as its only root. -/
def originInitialSampler : SamplerState where
  colors x := if x = 0 then some false else none
  edges := ∅
  history := []

/-- Finite edge observation of the origin-rooted lattice sampler. -/
def originSamplerEvent (L : List (Site 2)) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) : Set (ℕ → WalkDriver) :=
  {rows | ∃ out, samplerRun originInitialSampler L rows = some out ∧
    ∀ e ∈ E, decide (e.val ∈ out.edges) = p e}

/-- Origin-rooted finite sampler events are measurable. -/
theorem measurableSet_originSamplerEvent (L : List (Site 2)) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) : MeasurableSet (originSamplerEvent L E p) := by
  apply IsOpen.measurableSet
  apply isOpen_iff_mem_nhds.mpr
  rintro rows ⟨out, hout, he⟩
  filter_upwards [samplerRun_eventually_eq_of_some originInitialSampler out L rows hout] with rows' hs
  exact ⟨out, hs, he⟩

/-- Planar recurrence makes every finite origin-rooted sampler run terminate. -/
theorem samplerRun_origin_ae_success (L : List (Site 2)) :
    ∀ᵐ rows ∂wilsonRows, ∃ out, samplerRun originInitialSampler L rows = some out := by
  have hhit (x : Site 2) : ∀ᵐ w ∂walkLaw, ∃ n, position x w n = 0 := by
    have hm : MeasurableSet {w : WalkDriver | ∃ n, position x w n = 0} := by
      have he : {w : WalkDriver | ∃ n, position x w n = 0} =
          ⋃ n : ℕ, {w | position x w n = 0} := by ext w; simp
      rw [he]
      exact MeasurableSet.iUnion fun n =>
        (isClosed_eq (continuous_position x n) continuous_const).measurableSet
    exact (mem_ae_iff_prob_eq_one hm).mpr
      (FiniteAvalanches.ProvedStandards.polya_square_lattice_hits_every_site x 0)
  have hall : ∀ᵐ rows ∂wilsonRows, ∀ i (x : Site 2), ∃ n, position x (rows i) n = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro x
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => walkLaw) i).quasiMeasurePreserving.ae
      (hhit x)
  filter_upwards [hall] with rows hrows
  apply exists_samplerRun_of_hits originInitialSampler L rows 0 ?_ hrows
  simp [SamplerState.covered, originInitialSampler]

/-- Each fixed site's initial color stabilizes to its singleton-origin value. -/
theorem initialSampler_distantOrigin_eventually (z : Site 2) :
    ∀ᶠ B : ℕ in atTop,
      (initialSampler (distantOriginRootPair B)).colors z = originInitialSampler.colors z := by
  filter_upwards [eventually_finiteWired_inBox z] with B hbox
  have hne : z ≠ distantOriginRoot B := by
    intro he
    exact distantOriginRoot_not_inBox B (he ▸ hbox)
  simp [initialSampler, distantOriginRootPair, originInitialSampler, hne]

/-- Distant-root explorations eventually have the same finite edge observation
as the origin-rooted sampler, under common walk increments. -/
theorem wilsonRows_ae_eventually_distantOrigin_samplerEvent_iff
    (L : List (Site 2)) (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop,
      (rows ∈ samplerEvent (distantOriginRootPair B) L E ∅ p (fun _ => false) ↔
        rows ∈ originSamplerEvent L E p) := by
  filter_upwards [samplerRun_origin_ae_success L] with rows hrows
  obtain ⟨out, hout⟩ := hrows
  obtain ⟨outB, hrun, _, hedges, _⟩ := samplerRun_local_colors
    (fun B => initialSampler (distantOriginRootPair B)) originInitialSampler out
    initialSampler_distantOrigin_eventually (Eventually.of_forall fun _ => rfl)
    (Eventually.of_forall fun _ => rfl) L rows hout
  filter_upwards [hrun, hedges] with B hB heB
  constructor
  · rintro ⟨out', hout', hp, _⟩
    have heq : out' = outB B := Option.some.inj (hout'.symm.trans hB)
    refine ⟨out, hout, ?_⟩
    intro e he
    rw [← heB, ← heq]
    exact hp e he
  · rintro ⟨out', hout', hp⟩
    have heq : out' = out := Option.some.inj (hout'.symm.trans hout)
    refine ⟨outB B, hB, ?_, ?_⟩
    · intro e he
      rw [heB, ← heq]
      exact hp e he
    · simp

/-- Distant-root finite sampler probabilities converge to the origin-rooted
finite sampler probabilities. -/
theorem distantOrigin_samplerEvent_tendsto (L : List (Site 2))
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    Tendsto (fun B => wilsonRows (samplerEvent (distantOriginRootPair B) L E ∅ p (fun _ => false)))
      atTop (nhds (wilsonRows (originSamplerEvent L E p))) := by
  exact tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (measurableSet_originSamplerEvent L E p)
    (fun B => measurableSet_samplerEvent (distantOriginRootPair B) L E ∅ p (fun _ => false))
    (wilsonRows_ae_eventually_distantOrigin_samplerEvent_iff L E p)

end
end FiniteAvalanches.Wilson.Lattice
