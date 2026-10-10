import FiniteAvalanches.Sandpile.Law.Uniqueness

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

theorem eq_infiniteVolumeLaw_iff {μ : ProbabilityMeasure StableField} :
    μ = infiniteVolumeLaw ↔ IsInfiniteVolumeLaw μ :=
  ⟨fun h => by rw [h]; exact isInfiniteVolumeLaw_infiniteVolumeLaw, infiniteVolumeLaw_unique⟩

end

end FiniteAvalanches.External.SandpileLimit
