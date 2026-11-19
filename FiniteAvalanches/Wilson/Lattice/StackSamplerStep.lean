import FiniteAvalanches.Wilson.Lattice.ErasureAgreement
import FiniteAvalanches.Wilson.Lattice.SamplerEvents

/-! The first lattice stack branch has the sampler's one-walk law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Any property of a successful sampler step is an open walk event. -/
theorem isOpen_samplerStep_event (st : SamplerState) (x : Site 2) (P : SamplerState → Prop) :
    IsOpen {w | ∃ out, samplerStep st x w = some out ∧ P out} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro w ⟨out, hout, hp⟩
  filter_upwards [samplerStep_eventually_eq_of_some st out x w hout] with w' hw'
  exact ⟨out, hw', hp⟩

/-- Reading the first walk from independent lattice stacks gives the same law
for every property of the sampler's complete successful step. -/
theorem stackSamplerStep_eq_walkLaw (st : SamplerState) (x : Site 2)
    (k : Cursor (Site 2)) (P : SamplerState → Prop) :
    directionStackLaw (Site 2) {σ |
      ∃ out, samplerStep st x (readingLetter latticeDirectionHead x k σ) = some out ∧ P out} =
    walkLaw {w | ∃ out, samplerStep st x w = some out ∧ P out} := by
  let A : Set WalkDriver := {w | ∃ out, samplerStep st x w = some out ∧ P out}
  have hA : MeasurableSet A := (isOpen_samplerStep_event st x P).measurableSet
  have hmap := congrArg (fun μ : Measure WalkDriver => μ A)
    (directionStackLaw_map_readingDriver (Site 2) latticeDirectionHead x k)
  rw [Measure.map_apply (measurable_readingDriver (Site 2) latticeDirectionHead x k) hA] at hmap
  exact hmap

end
end FiniteAvalanches.Wilson.Lattice
