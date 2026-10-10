import FiniteAvalanches.Sandpile.Waves.HeldBurning
import FiniteAvalanches.Sandpile.Waves.SourceExtension

/-! Holding the source in the actual burning algorithm leaves precisely the
source-minus-one largest forbidden set. This is deterministic, not a law of trees. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem held_source_eq_core {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    heldBurning (wiredHeight (-1) h) {FiniteWired.site o} (boxSites N)
      (by simpa using site_mem_box o) = core h := by
  have hB : ({FiniteWired.site o} : Finset Site2) ⊆ boxSites N := by simpa using site_mem_box o
  obtain ⟨hc, hsub, hmax⟩ := held_burning_largest (wiredHeight (-1) h) {FiniteWired.site o} (boxSites N) hB
  apply Finset.Subset.antisymm
  · apply forbidden_subset_core hsub
    refine ⟨⟨FiniteWired.site o, hc.1 (Finset.mem_singleton_self _)⟩, ?_⟩
    intro x hx
    by_cases hxo : x = FiniteWired.site o
    · subst x
      rw [wired_height_site, active_height_source]
      have hn : 0 ≤ (degree (heldBurning (wiredHeight (-1) h) {FiniteWired.site o} (boxSites N) hB)
          (FiniteWired.site o) : ℤ) := Nat.cast_nonneg _
      omega
    · exact hc.2 x hx (by simpa using hxo)
  · apply hmax (core h) (forbidden_core_subset _ _)
    exact ⟨by simpa using source_mem_core h, fun x hx _ => (core_forbidden h).2 x hx⟩

end
end FiniteAvalanches.Sandpile.Waves
