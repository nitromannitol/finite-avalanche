import FiniteAvalanches.Sandpile.Law.Characterization

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

theorem infiniteVolumeLaw_unique {μ : ProbabilityMeasure StableField}
    (h : IsInfiniteVolumeLaw μ) : μ = infiniteVolumeLaw :=
  h.unique isInfiniteVolumeLaw_infiniteVolumeLaw

end

end FiniteAvalanches.External.SandpileLimit
