import FiniteAvalanches.Sandpile.Law.ExistenceUnique

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

/-- The infinite-volume uniform recurrent sandpile law on `ℤ²`. -/
def infiniteVolumeLaw : ProbabilityMeasure StableField :=
  Classical.choose existsUnique_infiniteVolumeLaw.exists

end

end FiniteAvalanches.External.SandpileLimit
