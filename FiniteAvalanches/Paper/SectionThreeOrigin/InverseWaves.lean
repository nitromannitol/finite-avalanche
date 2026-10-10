import FiniteAvalanches.Paper.SectionThree.InverseWaves
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths

namespace FiniteAvalanches.Paper.SectionThreeOrigin
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves MeasureTheory
open FiniteAvalanches.Sandpile.SourceCounting (origin)
open scoped Classical BigOperators ENNReal
noncomputable section

theorem inverse_waves_origin {N : ℕ} (h : Punctured N (origin N)) :
    (∀ x : Site2, waveCounts h.val x = if x ∈ core (forward h).val then 1 else 0) ∧
    (∀ a : Fin 4, FiniteWired.recurrent (sourceExtension a h.val) ↔
      degree (core h.val) (FiniteWired.site (origin N)) ≤ a.val) := by
  exact FiniteAvalanches.Paper.SectionThree.inverse_waves (origin N) h

end
end FiniteAvalanches.Paper.SectionThreeOrigin
