import FiniteAvalanches.Sandpile.Waves.Inverse
import FiniteAvalanches.Sandpile.Waves.SourceExtension

namespace FiniteAvalanches.Sandpile.Waves.Source
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem inverse_waves {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o) :
    (∀ x : Site2, waveCounts h.val x = if x ∈ core (forward h).val then 1 else 0) ∧
    (∀ a : Fin 4, FiniteWired.recurrent (sourceExtension a h.val) ↔
      degree (core h.val) (FiniteWired.site o) ≤ a.val) ∧
    forward (inverse h) = h ∧ inverse (forward h) = h ∧
    (waveCounts (inverse h).val).support = core h.val := by
  refine ⟨?_, source_extension_recurrent_iff h.property, forward_inverse h,
    inverse_forward h, ?_⟩
  · intro x
    have hs := wave_support_eq_core_output h.property
    change (waveCounts h.val).support = core (forward h).val at hs
    by_cases hx : x ∈ core (forward h).val
    · have hn : waveCounts h.val x ≠ 0 := Finsupp.mem_support_iff.mp (hs.symm ▸ hx)
      have hb := wave_counts_le_one h.val x
      rw [if_pos hx]
      omega
    · rw [if_neg hx]
      exact Finsupp.notMem_support_iff.mp (fun hh => hx (hs ▸ hh))
  · have hs := wave_support_eq_core_output (inverse h).property
    change (waveCounts (inverse h).val).support = core (forward (inverse h)).val at hs
    simpa only [forward_inverse] using hs

theorem paper_inverse_waves {N : ℕ} (o : FiniteWired.Active N) (h : Punctured N o) :
    (∀ x : Site2, waveCounts h.val x = if x ∈ core (forward h).val then 1 else 0) ∧
    (∀ a : Fin 4, FiniteWired.recurrent (sourceExtension a h.val) ↔
      degree (core h.val) (FiniteWired.site o) ≤ a.val) := by
  have hfull := FiniteAvalanches.Sandpile.Waves.Source.inverse_waves h
  exact ⟨hfull.1, hfull.2.1⟩

end
end FiniteAvalanches.Sandpile.Waves.Source
