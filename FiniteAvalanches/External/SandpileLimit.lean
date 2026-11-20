import FiniteAvalanches.Sandpile.Law.Properties
import FiniteAvalanches.Sandpile.Limit.InfiniteVolumeLaw

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

/-- Athreya–Járai (2004), Theorem 1 and Remark 1(iii) with the 2006 correction (d = 2);
Járai–Werning (2014), Theorem 3. -/
theorem exists_infiniteVolumeLaw :
    ∃ μ : ProbabilityMeasure StableField, IsInfiniteVolumeLaw μ ∧ IsTranslationInvariant μ :=
  FiniteAvalanches.Sandpile.InfiniteVolume.exists_infiniteVolumeLaw_proof

end

end FiniteAvalanches.External.SandpileLimit
