import FiniteAvalanches.Sandpile.Waves.RadiusEvents

/-! The radius of the entire legal avalanche in a finite wired box. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

/-- Wired termination and Abelian uniqueness determine the complete count. -/
theorem existsUnique_finite_avalanche_counts {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) :
    ∃! u : Counts, ∃ w : List Site2,
      WiredStabilizes (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))
        (boxSites N) w ∧ listCounts w = u := by
  obtain ⟨w, hw⟩ := exists_wired_stabilizes (FiniteWired.zeroExtend N η)
    (oneGrain (FiniteWired.site o)) N
  refine ⟨listCounts w, ⟨w, hw, rfl⟩, ?_⟩
  rintro u ⟨v, hv, rfl⟩
  exact wiredStabilizes_counts_unique hv hw

/-- The unique complete wired count, with no selection of a wave. -/
def finiteAvalancheCounts {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) : Counts :=
  Classical.choose (existsUnique_finite_avalanche_counts o η)

theorem finiteAvalancheCounts_spec {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) :
    ∃ w : List Site2,
      WiredStabilizes (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))
        (boxSites N) w ∧ listCounts w = finiteAvalancheCounts o η :=
  (Classical.choose_spec (existsUnique_finite_avalanche_counts o η)).1

theorem finiteAvalancheCounts_eq_counts {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) {w : List Site2}
    (hw : WiredStabilizes (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))
      (boxSites N) w) : finiteAvalancheCounts o η = listCounts w := by
  obtain ⟨v, hv, he⟩ := finiteAvalancheCounts_spec o η
  exact he.symm.trans (wiredStabilizes_counts_unique hv hw)

/-- Sup radius of the entire fired support; an empty avalanche has radius zero. -/
def finiteAvalancheRadius {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) : ℕ :=
  countsRadius (FiniteWired.site o) (finiteAvalancheCounts o η)

theorem finite_avalanche_radius_gt_iff_leaves {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) (M : ℕ) :
    M < finiteAvalancheRadius o η ↔ finiteAvalancheLeaves o
      ((boxSites M).image (fun x => x + FiniteWired.site o)) η := by
  rw [finiteAvalancheRadius, ← not_le, counts_radius_le_iff_translated_support]
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := finiteAvalancheCounts_spec o η
    exact ⟨w, hw, by simpa only [he] using h⟩
  · rintro ⟨w, hw, h⟩
    simpa only [finiteAvalancheCounts_eq_counts o η hw] using h

theorem finite_avalanche_radius_eq_zero_of_source_lt {N : ℕ}
    (o : FiniteWired.Active N) (η : FiniteWired.Recurrent N) (hη : η.val o ≠ 3) :
    finiteAvalancheRadius o η = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [finite_avalanche_radius_gt_iff_leaves]
  exact not_finite_avalanche_leaves_of_source_lt _ η hη

end
end FiniteAvalanches.Sandpile.Waves

#print axioms FiniteAvalanches.Sandpile.Waves.existsUnique_finite_avalanche_counts
#print axioms FiniteAvalanches.Sandpile.Waves.finiteAvalancheCounts_spec
#print axioms FiniteAvalanches.Sandpile.Waves.finite_avalanche_radius_gt_iff_leaves
#print axioms FiniteAvalanches.Sandpile.Waves.finite_avalanche_radius_eq_zero_of_source_lt
