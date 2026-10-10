import FiniteAvalanches.Sandpile.Waves.WaveNumber
import FiniteAvalanches.Sandpile.Waves.ExcursionEvents

/-! The complete finite avalanche event under the original recurrent counting law. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical BigOperators
noncomputable section

theorem flatten_support_subset (ws : List (List Site2)) (B : Finset Site2) :
    (listCounts ws.flatten).support ⊆ B ↔
      ∀ w ∈ ws, (listCounts w).support ⊆ B := by
  simp only [listCounts_support]
  constructor
  · intro h w hw x hx
    apply h
    simp only [List.mem_toFinset] at hx ⊢
    exact List.mem_flatten.mpr ⟨w, hw, hx⟩
  · intro h x hx
    simp only [List.mem_toFinset] at hx
    obtain ⟨w, hw, hx⟩ := List.mem_flatten.mp hx
    exact h w hw (by simpa only [List.mem_toFinset] using hx)

/-- The reversed list of wave supports has the same confinement event. -/
theorem excursion_support_subset {N : ℕ} {o : FiniteWired.Active N}
    (h : TerminalState N o) {ws : List (List Site2)}
    (hlen : ws.length = returnTime h)
    (hsets : ∀ (k : ℕ) (hk : k < ws.length), (listCounts ws[k]).support =
      core (inverse^[returnTime h - (k + 1)] h.val).val)
    (B : Finset Site2) :
    (listCounts ws.flatten).support ⊆ B ↔
      ∀ j : Fin (returnTime h), core (inverse^[j.val] h.val).val ⊆ B := by
  rw [flatten_support_subset, List.forall_mem_iff_getElem]
  constructor
  · intro hw j
    let k := returnTime h - (j.val + 1)
    have hk : k < ws.length := by dsimp [k]; omega
    have he : returnTime h - (k + 1) = j.val := by dsimp [k]; omega
    simpa only [hsets k hk, he] using hw k hk
  · intro hw k hk
    rw [hsets k hk]
    exact hw ⟨returnTime h - (k + 1), by omega⟩

/-- This event uses an actual legal wired stabilization and its entire fired set. -/
def finiteAvalancheLeaves {N : ℕ} (o : FiniteWired.Active N) (B : Finset Site2)
    (η : FiniteWired.Recurrent N) : Prop :=
  ∃ w : List Site2, WiredStabilizes (FiniteWired.zeroExtend N η)
    (oneGrain (FiniteWired.site o)) (boxSites N) w ∧ ¬(listCounts w).support ⊆ B

/-- Every nonempty input event is exactly a visit of its complete inverse excursion. -/
theorem finite_avalanche_leaves_source_three {N : ℕ} {o : FiniteWired.Active N}
    (B : Finset Site2) (η : SourceThree N o) :
    finiteAvalancheLeaves o B η.val ↔
      ∃ j : Fin (returnTime (inputExcursion η)),
        ¬core (inverse^[j.val] (inputExcursion η).val).val ⊆ B := by
  let h := inputExcursion η
  obtain ⟨ws, hlen, hw, _, hsets⟩ := exists_excursion_wired_stabilization h
  have hp : excursionPredecessorEquiv h = η := excursionPredecessorEquiv.apply_symm_apply η
  have hagree : ∀ y ∈ boxSites N,
      FiniteWired.zeroExtend N η.val y = wiredStable (returnMap h).val.val y := by
    intro y hy
    let v := FiniteWired.activeOfSite N y ((mem_box_sites N y).mp hy)
    change FiniteWired.zeroExtend N η.val (FiniteWired.site v) =
      wiredStable (returnMap h).val.val (FiniteWired.site v)
    rw [FiniteWired.zeroExtend_site, excursion_predecessor_height h v, hp]
  have ht := wired_stabilizes_of_agree hw hagree
  have he : finiteAvalancheLeaves o B η.val ↔ ¬(listCounts ws.flatten).support ⊆ B := by
    constructor
    · rintro ⟨w, hw, hb⟩
      simpa only [wiredStabilizes_counts_unique hw ht] using hb
    · exact fun hb => ⟨ws.flatten, ht, hb⟩
  rw [he, excursion_support_subset h hlen hsets]
  push Not
  rfl

/-- Inputs below source height three have an empty avalanche. -/
theorem not_finite_avalanche_leaves_of_source_lt {N : ℕ} {o : FiniteWired.Active N}
    (B : Finset Site2) (η : FiniteWired.Recurrent N) (hη : η.val o ≠ 3) :
    ¬finiteAvalancheLeaves o B η := by
  rintro ⟨w, hw, hb⟩
  have hz := finite_wave_number_eq_source_count η hw
  simp only [finiteWaveNumber, dif_neg hη] at hz
  have hnil : w = [] := by
    by_contra hn
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hn
    have hlegal : 4 ≤ initial (FiniteWired.zeroExtend N η)
        (oneGrain (FiniteWired.site o)) x := by
      have hf := hw.2.1 0 (by simp)
      change 4 ≤ initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o)) x +
        lap (prefixCounts (x :: xs) 0) x at hf
      rw [prefix_zero] at hf
      simpa [lap, nbrSumZ] using hf
    by_cases hx : x = FiniteWired.site o
    · subst x
      have hc : listCounts (FiniteWired.site o :: xs) (FiniteWired.site o) ≠ 0 := by
        simp [listCounts_apply]
      exact hc hz
    · have hηx := (FiniteWired.zeroExtend N η x).isLt
      simp only [initial, oneGrain, Finsupp.single_eq_of_ne hx] at hlegal
      omega
  simp [hnil, listCounts_support] at hb

/-- Complete avalanche events are counted once, under the original recurrent inputs. -/
theorem sum_finite_avalanche_leaves {N : ℕ} (o : FiniteWired.Active N) (B : Finset Site2) :
    (∑ η : FiniteWired.Recurrent N, (if finiteAvalancheLeaves o B η then 1 else 0 : ℝ)) =
      ∑ h : TerminalState N o,
        (if ∃ j : Fin (returnTime h), ¬core (inverse^[j.val] h.val).val ⊆ B
          then 1 else 0 : ℝ) := by
  classical
  let f : FiniteWired.Recurrent N → ℝ := fun η => if finiteAvalancheLeaves o B η then 1 else 0
  let q : TerminalState N o → ℝ := fun h =>
    if ∃ j : Fin (returnTime h), ¬core (inverse^[j.val] h.val).val ⊆ B then 1 else 0
  change (∑ η, f η) = _
  calc
    (∑ η, f η) = ∑ η : SourceThree N o, q (inputExcursion η) := by
      rw [← Fintype.sum_subtype_add_sum_subtype
        (fun η : FiniteWired.Recurrent N => η.val o = 3)
        f]
      have hz : (∑ η : {η : FiniteWired.Recurrent N // ¬η.val o = 3},
          (if finiteAvalancheLeaves o B η.val then 1 else 0 : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro η _
        exact if_neg (not_finite_avalanche_leaves_of_source_lt B η.val η.property)
      change ((∑ η : SourceThree N o, (if finiteAvalancheLeaves o B η.val then 1 else 0 : ℝ)) +
        ∑ η : {η : FiniteWired.Recurrent N // ¬η.val o = 3},
          (if finiteAvalancheLeaves o B η.val then 1 else 0 : ℝ)) = _
      rw [hz, add_zero]
      apply Finset.sum_congr rfl
      intro η _
      simp only [finite_avalanche_leaves_source_three, q]
    _ = ∑ h : TerminalState N o, q h := excursionPredecessorEquiv.symm.sum_comp q
    _ = _ := rfl

/-- The complete-event estimate pays no factor equal to the number of waves. -/
theorem sum_finite_avalanche_leaves_le {N : ℕ} (o : FiniteWired.Active N)
    (S B : Finset Site2) (hS : nbrFinset (FiniteWired.site o) ⊆ S) :
    (∑ η : FiniteWired.Recurrent N, (if finiteAvalancheLeaves o B η then 1 else 0 : ℝ)) ≤
      (∑ x : Punctured N o,
        (if ¬S ⊆ core x.val ∧ S ⊆ core (inverse x).val then 1 else 0 : ℝ)) +
      ∑ x : Punctured N o,
        (if ¬S ⊆ core x.val ∧ ¬core x.val ⊆ B then 1 else 0 : ℝ) := by
  rw [sum_finite_avalanche_leaves]
  exact count_large_excursions_le S B hS

/-- Expectation uses the original recurrent denominator on both counting terms. -/
theorem integral_finite_avalanche_leaves_le {N : ℕ} (o : FiniteWired.Active N)
    (S B : Finset Site2) (hS : nbrFinset (FiniteWired.site o) ⊆ S) :
    (∫ η, (if finiteAvalancheLeaves o B η then 1 else 0 : ℝ) ∂FiniteWired.law N) ≤
      ((∑ x : Punctured N o,
        (if ¬S ⊆ core x.val ∧ S ⊆ core (inverse x).val then 1 else 0 : ℝ)) +
      ∑ x : Punctured N o,
        (if ¬S ⊆ core x.val ∧ ¬core x.val ⊆ B then 1 else 0 : ℝ)) /
          Fintype.card (FiniteWired.Recurrent N) := by
  have hl : FiniteWired.law N = uniformMeasure (FiniteWired.Recurrent N) := by
    simp only [FiniteWired.law, uniformMeasure, Nat.card_eq_fintype_card]
  rw [hl, integral_uniformMeasure, Nat.card_eq_fintype_card]
  exact div_le_div_of_nonneg_right (sum_finite_avalanche_leaves_le o S B hS)
    (Nat.cast_nonneg _)

/-- The indicator integral is the actual probability of the complete wired event. -/
theorem integral_finite_avalanche_leaves {N : ℕ} (o : FiniteWired.Active N) (B : Finset Site2) :
    (∫ η, (if finiteAvalancheLeaves o B η then 1 else 0 : ℝ) ∂FiniteWired.law N) =
      (FiniteWired.law N).real {η | finiteAvalancheLeaves o B η} := by
  have hm : MeasurableSet {η | finiteAvalancheLeaves o B η} := trivial
  simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
    (integral_indicator_one (μ := FiniteWired.law N) hm)

/-- The finite-volume excursion bound, with the original probability normalization. -/
theorem finite_avalanche_leaves_probability_le {N : ℕ} (o : FiniteWired.Active N)
    (S B : Finset Site2) (hS : nbrFinset (FiniteWired.site o) ⊆ S) :
    (FiniteWired.law N).real {η | finiteAvalancheLeaves o B η} ≤
      ((∑ x : Punctured N o,
        (if ¬S ⊆ core x.val ∧ S ⊆ core (inverse x).val then 1 else 0 : ℝ)) +
      ∑ x : Punctured N o,
        (if ¬S ⊆ core x.val ∧ ¬core x.val ⊆ B then 1 else 0 : ℝ)) /
          Fintype.card (FiniteWired.Recurrent N) := by
  rw [← integral_finite_avalanche_leaves]
  exact integral_finite_avalanche_leaves_le o S B hS

end
end FiniteAvalanches.Sandpile.Waves
