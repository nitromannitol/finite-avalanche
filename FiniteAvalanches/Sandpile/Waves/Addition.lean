import FiniteAvalanches.Sandpile.Waves.Inverse

/-! Firing the source once is exactly one grain at each active source neighbor;
subsequent topplings are an actual legal list with the source held. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

def afterSource {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) : Site2 → ℤ :=
  fun x => wiredHeight 4 h x + lap (dirac (FiniteWired.site o)) x

theorem after_source_off {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o)
    (x : OffVertex N o) : afterSource h (FiniteWired.site x.val) =
      (h x).val + if FiniteWired.site o ∈ nbrFinset (FiniteWired.site x.val) then 1 else 0 := by
  have hn : FiniteWired.site x.val ≠ FiniteWired.site o := fun he => x.property (FiniteWired.site_injective N he)
  rw [afterSource, wired_height_site, active_height_off, lap_dirac_off _ _ hn]

/-- The unique output is realized by a finite legal off-source list after the one source firing. -/
theorem exists_source_held_realization {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    ∃ v : List Site2, (∀ x ∈ v, x ∈ boxSites N ∧ x ≠ FiniteWired.site o) ∧
      LegalList (afterSource h) v ∧ heightAfter (afterSource h) v = waveHeight h := by
  obtain ⟨v, hv, hl, _, he⟩ := wave_counts_realizes h
  refine ⟨v, hv, legal_list_of_cons hl, ?_⟩
  funext x
  unfold heightAfter afterSource waveHeight
  rw [← he, list_counts_cons_int, lap_add]
  ring

end
end FiniteAvalanches.Sandpile.Waves
