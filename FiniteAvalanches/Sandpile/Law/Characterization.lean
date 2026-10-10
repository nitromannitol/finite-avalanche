import FiniteAvalanches.Sandpile.Law.InfiniteVolume

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

theorem isInfiniteVolumeLaw_infiniteVolumeLaw : IsInfiniteVolumeLaw infiniteVolumeLaw :=
  Classical.choose_spec existsUnique_infiniteVolumeLaw.exists

end

end FiniteAvalanches.External.SandpileLimit
