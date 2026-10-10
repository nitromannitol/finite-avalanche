import FiniteAvalanches.Sandpile.Waves.AvalancheEvents
import Mathlib.Data.Fin.Rev

/-! Actual ordered supports of every complete finite one-grain avalanche.
Existence and uniqueness precede the selected list; all legal wave orders agree. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- Agreeing active heights preserve the full same-volume wave trace. -/
theorem IsWaveStabilization.congr_in {V : Finset Site2} {o : Site2}
    {s s' : Site2 → ℤ} {ws : List (List Site2)}
    (h : IsWaveStabilization V o s ws) (he : ∀ x ∈ V, s' x = s x) :
    IsWaveStabilization V o s' ws := by
  induction h generalizing s' with
  | nil hs => exact .nil (fun x hx => by rw [he x hx]; exact hs x hx)
  | @cons s v ws hoV ho hv hl hs ht ih =>
    have hwV : ∀ x ∈ o :: v, x ∈ V := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hoV
      · exact (hv x hx).1
    have ha : ∀ x ∈ V, heightAfter s' (o :: v) x = heightAfter s (o :: v) x :=
      fun x hx => by simp only [heightAfter, he x hx]
    exact .cons hoV (by rw [he o hoV]; exact ho) hv
      ((legal_list_congr_in he hwV).mpr hl)
      (fun x hx hxo => by rw [ha x hx]; exact hs x hx hxo) (ih ha)

/-- The complete ordered support list exists and is unique on every recurrent input. -/
theorem exists_unique_finite_wave_sets {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) :
    ∃! W : List (Finset Site2), ∃ ws : List (List Site2),
      IsWaveStabilization (boxSites N) (FiniteWired.site o)
        (initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))) ws ∧
      W = ws.map (fun w => (listCounts w).support) := by
  obtain ⟨ws, hw, _⟩ := exists_wave_stabilization (FiniteWired.zeroExtend N η)
    (FiniteWired.site o) N (site_mem_box o)
  refine ⟨ws.map (fun w => (listCounts w).support), ⟨ws, hw, rfl⟩, ?_⟩
  rintro W ⟨vs, hv, rfl⟩
  have hc := hv.counts_unique hw
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (fun u : Counts => u.support)) hc

/-- Actual chronological wave supports, selected only after proved existence and uniqueness. -/
def finiteWaveSets {N : ℕ} (o : FiniteWired.Active N) (η : FiniteWired.Recurrent N) :
    List (Finset Site2) := (exists_unique_finite_wave_sets o η).choose

theorem finite_wave_sets_realizes {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) : ∃ ws : List (List Site2),
    IsWaveStabilization (boxSites N) (FiniteWired.site o)
      (initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))) ws ∧
    finiteWaveSets o η = ws.map (fun w => (listCounts w).support) :=
  (exists_unique_finite_wave_sets o η).choose_spec.1

/-- Every complete legal wave trace has exactly this ordered support list. -/
theorem finite_wave_sets_eq {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) {ws : List (List Site2)}
    (hw : IsWaveStabilization (boxSites N) (FiniteWired.site o)
      (initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))) ws) :
    finiteWaveSets o η = ws.map (fun w => (listCounts w).support) :=
  ((exists_unique_finite_wave_sets o η).choose_spec.2 _ ⟨ws, hw, rfl⟩).symm

theorem finite_wave_sets_empty {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) (hη : η.val o ≠ 3) : finiteWaveSets o η = [] := by
  obtain ⟨ws, hw, he⟩ := finite_wave_sets_realizes o η
  have hc := finite_wave_number_eq_source_count η hw.flatten_stable
  rw [hw.source_count, finiteWaveNumber, dif_neg hη] at hc
  rw [he, List.length_eq_zero_iff.mp hc]
  rfl

/-- Forward replay gives every chronological wave, with the exact reversed inverse index. -/
theorem finite_wave_sets_source_three {N : ℕ} {o : FiniteWired.Active N}
    (η : SourceThree N o) :
    finiteWaveSets o η.val = List.ofFn (fun k : Fin (returnTime (inputExcursion η)) =>
      core (inverse^[returnTime (inputExcursion η) - (k.val + 1)] (inputExcursion η).val).val) := by
  let h := inputExcursion η
  obtain ⟨ws, hlen, hw, _, hsets⟩ := exists_excursion_avalanche h
  have hp : excursionPredecessorEquiv h = η := excursionPredecessorEquiv.apply_symm_apply η
  have he : ∀ y ∈ boxSites N,
      initial (FiniteWired.zeroExtend N η.val) (oneGrain (FiniteWired.site o)) y =
        initial (wiredStable (returnMap h).val.val) (oneGrain (FiniteWired.site o)) y := by
    intro y hy
    let v := FiniteWired.activeOfSite N y ((mem_box_sites N y).mp hy)
    change initial (FiniteWired.zeroExtend N η.val) (oneGrain (FiniteWired.site o)) (FiniteWired.site v) =
      initial (wiredStable (returnMap h).val.val) (oneGrain (FiniteWired.site o)) (FiniteWired.site v)
    simp only [initial, FiniteWired.zeroExtend_site, excursion_predecessor_height, hp]
  rw [finite_wave_sets_eq o η.val (hw.congr_in he)]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_ofFn]
    exact hlen
  · intro k hk hk'
    simp only [List.getElem_map, List.getElem_ofFn]
    exact hsets k (by simpa only [List.length_map] using hk)

/-- Arbitrary shape weights are summed over all actual waves, including an empty list. -/
def finiteWaveSum {M : Type*} [AddCommMonoid M] {N : ℕ}
    (o : FiniteWired.Active N) (Φ : Finset Site2 → M) (η : FiniteWired.Recurrent N) : M :=
  ((finiteWaveSets o η).map Φ).sum

theorem finite_wave_sum_trace {M : Type*} [AddCommMonoid M] {N : ℕ}
    (o : FiniteWired.Active N) (Φ : Finset Site2 → M) (η : FiniteWired.Recurrent N)
    {ws : List (List Site2)} (hw : IsWaveStabilization (boxSites N) (FiniteWired.site o)
      (initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))) ws) :
    finiteWaveSum o Φ η = (ws.map (fun w => Φ (listCounts w).support)).sum := by
  simp only [finiteWaveSum, finite_wave_sets_eq o η hw, List.map_map, Function.comp_def]

/-- Reversal changes chronology, not the full weighted sum or its multiplicities. -/
theorem finite_wave_sum_source_three {M : Type*} [AddCommMonoid M] {N : ℕ}
    {o : FiniteWired.Active N} (Φ : Finset Site2 → M) (η : SourceThree N o) :
    finiteWaveSum o Φ η.val =
      ∑ j : Fin (returnTime (inputExcursion η)),
        Φ (core (inverse^[j.val] (inputExcursion η).val).val) := by
  rw [finiteWaveSum, finite_wave_sets_source_three]
  simp only [List.map_ofFn, List.sum_ofFn]
  let q : Fin (returnTime (inputExcursion η)) → M :=
    fun j => Φ (core (inverse^[j.val] (inputExcursion η).val).val)
  have he : (∑ k : Fin (returnTime (inputExcursion η)),
      Φ (core (inverse^[returnTime (inputExcursion η) - (k.val + 1)] (inputExcursion η).val).val)) =
      ∑ k, q (Fin.revPerm k) := by
    apply Finset.sum_congr rfl
    intro k _
    change _ = Φ (core (inverse^[(Fin.rev k).val] (inputExcursion η).val).val)
    have hk : (Fin.rev k).val = returnTime (inputExcursion η) - (k.val + 1) := by
      rw [Fin.val_rev]
    rw [hk]
  exact he.trans (Equiv.sum_comp (Fin.revPerm : Fin (returnTime (inputExcursion η)) ≃ _) q)

/-- The complete weighted occupation count, with every source-height interval retained. -/
theorem sum_finite_wave_sum {M : Type*} [AddCommMonoid M] {N : ℕ}
    (o : FiniteWired.Active N) (Φ : Finset Site2 → M) :
    (∑ η : FiniteWired.Recurrent N, finiteWaveSum o Φ η) =
      ∑ g : Punctured N o, Φ (core g.val) := by
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun η : FiniteWired.Recurrent N => η.val o = 3) (finiteWaveSum o Φ)]
  have hz : (∑ η : {η : FiniteWired.Recurrent N // ¬η.val o = 3},
      finiteWaveSum o Φ η.val) = 0 := by
    apply Finset.sum_eq_zero
    intro η _
    simp only [finiteWaveSum, finite_wave_sets_empty o η.val η.property, List.map_nil, List.sum_nil]
  rw [hz, add_zero]
  simp only [finite_wave_sum_source_three]
  let q : TerminalState N o → M :=
    fun h => ∑ j : Fin (returnTime h), Φ (core (inverse^[j.val] h.val).val)
  change (∑ η : SourceThree N o, q (excursionPredecessorEquiv.symm η)) = _
  rw [excursionPredecessorEquiv.symm.sum_comp q]
  change (∑ h : TerminalState N o, ∑ j : Fin (returnTime h),
    Φ (core (inverse^[j.val] h.val).val)) = _
  calc
    _ = ∑ p : ExcursionPoint N o, Φ (core (excursionState p).val) :=
      (Fintype.sum_sigma (fun p : ExcursionPoint N o => Φ (core (excursionState p).val))).symm
    _ = _ := excursionEquiv.sum_comp (fun g => Φ (core g.val))

end
end FiniteAvalanches.Sandpile.Waves
