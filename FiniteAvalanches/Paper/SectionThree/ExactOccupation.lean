import FiniteAvalanches.Paper.Providers.OccupationProvider

namespace FiniteAvalanches.Paper.SectionThree
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem exact_occupation {N : ℕ} (o : FiniteWired.Active N) :
    (∀ h : Punctured N o, ∃ j : ℕ, terminal (inverse^[j] h)) ∧
    (∀ q : Punctured N o → ℝ,
      (∫ h, (∑ j : Fin (returnTime h), q (inverse^[j.val] h.val))
        ∂FiniteAvalanches.Sandpile.Waves.Source.terminalCountingMeasure o) =
      ∫ h, q h ∂puncturedCountingMeasure o) := by
  exact FiniteAvalanches.Sandpile.Waves.Source.paper_exact_occupation o

end
end FiniteAvalanches.Paper.SectionThree
