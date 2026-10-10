import FiniteAvalanches.Sandpile.Waves.Excursion
import FiniteAvalanches.Sandpile.Waves.Occupation
import FiniteAvalanches.Trees.Measure
import FiniteAvalanches.Sandpile.LocalConfinement

/-! The number of waves under the literal finite recurrent counting law. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical BigOperators
noncomputable section

/-- The source is fired once in each wave and nowhere else in the trace. -/
theorem IsWaveStabilization.source_count {V : Finset Site2} {o : Site2}
    {s : Site2 → ℤ} {ws : List (List Site2)} (hw : IsWaveStabilization V o s ws) :
    listCounts ws.flatten o = ws.length := by
  induction hw with
  | nil => simp [listCounts_apply]
  | @cons s v ws ho hs hv hl hstable ht ih =>
    have hn : o ∉ v := by intro h; exact (hv o h).2 rfl
    simp only [List.flatten_cons, listCounts_apply, List.count_append,
      List.count_cons_self, List.count_eq_zero_of_not_mem hn, List.length_cons]
    rw [listCounts_apply] at ih
    omega

/-- The inverse-excursion index for a source-three recurrent input. -/
def inputExcursion {N : ℕ} {o : FiniteWired.Active N} (η : SourceThree N o) : TerminalState N o :=
  excursionPredecessorEquiv.symm η

/-- The actual wave count, including all recurrent inputs with an empty avalanche. -/
def finiteWaveNumber {N : ℕ} (o : FiniteWired.Active N) (η : FiniteWired.Recurrent N) : ℕ :=
  if h : η.val o = 3 then returnTime (inputExcursion ⟨η, h⟩) else 0

theorem finite_wave_number_source_three {N : ℕ} {o : FiniteWired.Active N}
    (η : SourceThree N o) : finiteWaveNumber o η.val = returnTime (inputExcursion η) := by
  simp only [finiteWaveNumber, dif_pos η.property]

/-- Every legal wired stabilization has exactly this many source topplings. -/
theorem finite_wave_number_eq_source_count {N : ℕ} {o : FiniteWired.Active N}
    (η : FiniteWired.Recurrent N) {w : List Site2}
    (hw : WiredStabilizes (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))
      (boxSites N) w) : listCounts w (FiniteWired.site o) = finiteWaveNumber o η := by
  by_cases h : η.val o = 3
  · let x : SourceThree N o := ⟨η, h⟩
    let z := inputExcursion x
    obtain ⟨ws, _, hws, _, _⟩ := exists_excursion_wired_stabilization z
    have hp : excursionPredecessorEquiv z = x := excursionPredecessorEquiv.apply_symm_apply x
    have hagree : ∀ y ∈ boxSites N,
        FiniteWired.zeroExtend N η y = wiredStable (returnMap z).val.val y := by
      intro y hy
      let v := FiniteWired.activeOfSite N y ((mem_box_sites N y).mp hy)
      change FiniteWired.zeroExtend N η (FiniteWired.site v) =
        wiredStable (returnMap z).val.val (FiniteWired.site v)
      rw [FiniteWired.zeroExtend_site, excursion_predecessor_height z v, hp]
    have ht := wired_stabilizes_of_agree hws hagree
    have he := wiredStabilizes_counts_unique hw ht
    rw [he]
    -- The wave trace already supplied by hws has the same source count as any realization.
    have sourceCount : listCounts ws.flatten (FiniteWired.site o) = returnTime z := by
      obtain ⟨ws', hlen', htrace, _, _⟩ := exists_excursion_avalanche z
      have hc := wiredStabilizes_counts_unique hws htrace.flatten_stable
      rw [hc, htrace.source_count, hlen']
    rw [sourceCount]
    exact (finite_wave_number_source_three x).symm
  · have hη : (η.val o).val < 3 := by
      have hb := (η.val o).isLt
      have hn : (η.val o).val ≠ 3 := by intro he; apply h; exact Fin.ext he
      omega
    have hnil : WiredStabilizes (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))
        (boxSites N) [] := by
      refine ⟨by simp, ?_, ?_⟩
      · intro k hk
        simp at hk
      · intro y hy
        have hlo : 0 ≤ initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o)) y :=
          initial_nonneg _ _ y
        refine ⟨by simpa [listCounts, lap, nbrSumZ] using hlo, ?_⟩
        by_cases he : y = FiniteWired.site o
        · subst y
          simp only [initial, FiniteWired.zeroExtend_site, oneGrain, Finsupp.single_eq_same]
          simpa [listCounts, lap, nbrSumZ] using (show ((η.val o).val : ℤ) + 1 < 4 by omega)
        · simp only [initial, oneGrain, Finsupp.single_eq_of_ne he]
          simp [listCounts, lap, nbrSumZ]
    rw [wiredStabilizes_counts_unique hw hnil]
    simp [finiteWaveNumber, h, listCounts]

/-- The total wave count has the common normalization of recurrent inputs. -/
theorem sum_finite_wave_number {N : ℕ} (o : FiniteWired.Active N) :
    (∑ η : FiniteWired.Recurrent N, finiteWaveNumber o η) = Fintype.card (Punctured N o) := by
  have hsum : (∑ η : FiniteWired.Recurrent N, finiteWaveNumber o η) =
      ∑ η : SourceThree N o, returnTime (inputExcursion η) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun η : FiniteWired.Recurrent N => η.val o = 3)
      (finiteWaveNumber o)]
    have hz : (∑ η : {η : FiniteWired.Recurrent N // ¬η.val o = 3},
        finiteWaveNumber o η.val) = 0 := by
      apply Finset.sum_eq_zero
      intro η _
      simp only [finiteWaveNumber, dif_neg η.property]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro η _
    exact finite_wave_number_source_three η
  rw [hsum]
  change (∑ η : SourceThree N o, returnTime (excursionPredecessorEquiv.symm η)) = _
  rw [excursionPredecessorEquiv.symm.sum_comp returnTime]
  have hc := Fintype.card_congr (excursionEquiv (N := N) (o := o))
  simpa only [ExcursionPoint, Fintype.card_sigma, Fintype.card_fin] using hc

/-- The expected number of waves equals the total mass of punctured states,
each given the mass of one original recurrent configuration. -/
theorem integral_finite_wave_number {N : ℕ} (o : FiniteWired.Active N) :
    (∫ η, (finiteWaveNumber o η : ℝ) ∂FiniteWired.law N) =
      (Fintype.card (Punctured N o) : ℝ) / Fintype.card (FiniteWired.Recurrent N) := by
  have hl : FiniteWired.law N = uniformMeasure (FiniteWired.Recurrent N) := by
    simp only [FiniteWired.law, uniformMeasure, Nat.card_eq_fintype_card]
  rw [hl, integral_uniformMeasure, Nat.card_eq_fintype_card]
  congr 1
  exact_mod_cast sum_finite_wave_number o

end
end FiniteAvalanches.Sandpile.Waves
