import FiniteAvalanches.Sandpile.Law.Translation

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

theorem tendsto_finiteFieldProbability_infiniteVolumeLaw :
    Tendsto finiteFieldProbability atTop (nhds infiniteVolumeLaw) :=
  isInfiniteVolumeLaw_infiniteVolumeLaw.tendsto_boxes

end

end FiniteAvalanches.External.SandpileLimit
