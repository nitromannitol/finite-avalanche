import FiniteAvalanches.Paper.Providers.InverseWavesProvider

namespace FiniteAvalanches.Paper.SectionThree
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem inverse_waves {N : ℕ} (o : FiniteWired.Active N) (h : Punctured N o) :
    (∀ x : Site2, waveCounts h.val x = if x ∈ core (forward h).val then 1 else 0) ∧
    (∀ a : Fin 4, FiniteWired.recurrent (sourceExtension a h.val) ↔
      degree (core h.val) (FiniteWired.site o) ≤ a.val) := by
  exact FiniteAvalanches.Sandpile.Waves.Source.paper_inverse_waves o h

end
end FiniteAvalanches.Paper.SectionThree
