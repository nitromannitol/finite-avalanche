import FiniteAvalanches.Paper.SectionThree.ExactOccupation
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths

namespace FiniteAvalanches.Paper.SectionThreeOrigin
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open FiniteAvalanches.Sandpile.SourceCounting (origin)
open scoped Classical BigOperators ENNReal
noncomputable section

theorem exact_occupation_origin {N : ℕ} :
    (∀ h : Punctured N (origin N), ∃ j : ℕ, terminal (inverse^[j] h)) ∧
    (∀ q : Punctured N (origin N) → ℝ,
      (∫ h, (∑ j : Fin (returnTime h), q (inverse^[j.val] h.val))
        ∂FiniteAvalanches.Sandpile.Waves.Source.terminalCountingMeasure (origin N)) =
      ∫ h, q h ∂puncturedCountingMeasure (origin N)) := by
  exact FiniteAvalanches.Paper.SectionThree.exact_occupation (origin N)

end
end FiniteAvalanches.Paper.SectionThreeOrigin
