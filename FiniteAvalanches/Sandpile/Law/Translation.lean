import FiniteAvalanches.Sandpile.Law.CharacterizationIff

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

theorem isTranslationInvariant_infiniteVolumeLaw : IsTranslationInvariant infiniteVolumeLaw := by
  obtain ⟨μ, hμ, hinv⟩ := exists_infiniteVolumeLaw
  rw [← infiniteVolumeLaw_unique hμ]
  exact hinv

end

end FiniteAvalanches.External.SandpileLimit
