import FiniteAvalanches.Sandpile.Waves.Occupation

/-! Counting large complete excursions by transitions and omitted marked vertices. -/
open scoped Classical BigOperators
namespace FiniteAvalanches.Probability.Excursions

/-- A sequence initially outside an event must cross into it before any later visit. -/
theorem exists_first_transition {X : Type*} (f : ℕ → X) (P : X → Prop)
    (h0 : ¬P (f 0)) {k : ℕ} (hk : P (f k)) :
    ∃ j < k, ¬P (f j) ∧ P (f (j + 1)) := by
  classical
  have hex : ∃ n : ℕ, P (f n) := ⟨k, hk⟩
  let n := Nat.find hex
  have hn : P (f n) := Nat.find_spec hex
  have hnk : n ≤ k := Nat.find_min' hex hk
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    exact h0 (he ▸ hn)
  refine ⟨n - 1, by omega, ?_, ?_⟩
  · exact Nat.find_min hex (by omega)
  · simpa only [show n - 1 + 1 = n by omega] using hn

/-- One large visit is bounded by the numbers of crossings and large visits outside P. -/
theorem large_visit_indicator_le {X : Type*} (f : ℕ → X) (P B : X → Prop)
    [DecidablePred P] [DecidablePred B]
    (h0 : ¬P (f 0)) (n : ℕ) :
    (if ∃ j : Fin n, B (f j.val) then 1 else 0 : ℝ) ≤
      ∑ j : Fin n,
        ((if ¬P (f j.val) ∧ P (f (j.val + 1)) then 1 else 0) +
          (if ¬P (f j.val) ∧ B (f j.val) then 1 else 0) : ℝ) := by
  classical
  split_ifs with h
  · obtain ⟨k, hk⟩ := h
    by_cases hp : P (f k.val)
    · obtain ⟨j, hj, hj0, hj1⟩ := exists_first_transition f P h0 hp
      let i : Fin n := ⟨j, lt_trans hj k.isLt⟩
      have hs := Finset.single_le_sum (f := fun j : Fin n =>
        (if ¬P (f j.val) ∧ P (f (j.val + 1)) then 1 else 0 : ℝ) +
          (if ¬P (f j.val) ∧ B (f j.val) then 1 else 0 : ℝ))
        (fun _ _ => by positivity) (Finset.mem_univ i)
      have he : ¬P (f i.val) ∧ P (f (i.val + 1)) := ⟨hj0, hj1⟩
      rw [if_pos he] at hs
      have hz : (0 : ℝ) ≤ (if ¬P (f i.val) ∧ B (f i.val) then 1 else 0 : ℝ) := by positivity
      linarith
    · have hs := Finset.single_le_sum (f := fun j : Fin n =>
        (if ¬P (f j.val) ∧ P (f (j.val + 1)) then 1 else 0 : ℝ) +
          (if ¬P (f j.val) ∧ B (f j.val) then 1 else 0 : ℝ))
        (fun _ _ => by positivity) (Finset.mem_univ k)
      have hb : (if ¬P (f k.val) ∧ B (f k.val) then 1 else 0 : ℝ) = 1 := if_pos ⟨hp, hk⟩
      rw [hb] at hs
      have hz : (0 : ℝ) ≤ (if ¬P (f k.val) ∧ P (f (k.val + 1)) then 1 else 0 : ℝ) := by positivity
      linarith
  · apply Finset.sum_nonneg
    intro j _
    positivity

end FiniteAvalanches.Probability.Excursions

namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
noncomputable section

private theorem card_neighbors (x : Site2) : (nbrFinset x).card = 2 * 2 := by
  classical
  rw [nbrFinset, Finset.card_biUnion]
  · have : ∀ i : Fin 2, ({x + unit i, x - unit i} : Finset (Site 2)).card = 2 := by
      intro i
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      intro h
      have := congrFun h i
      simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
      omega
    simp [this, Finset.sum_const]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-- The initial inverse wave omits a marked vertex whenever all source neighbors are marked. -/
theorem terminal_omits_marked {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset Site2) (hS : nbrFinset (FiniteWired.site o) ⊆ S) (h : TerminalState N o) :
    ¬S ⊆ core h.val.val := by
  intro hs
  have hn : nbrFinset (FiniteWired.site o) ⊆ core h.val.val := hS.trans hs
  have hd : degree (core h.val.val) (FiniteWired.site o) = 4 := by
    rw [degree, Finset.inter_eq_left.mpr hn, card_neighbors]
  have ht := h.property
  unfold terminal at ht
  omega

/-- The excursion union bound counts states with their original common mass. -/
theorem count_large_excursions_le {N : ℕ} {o : FiniteWired.Active N}
    (S B : Finset Site2) (hS : nbrFinset (FiniteWired.site o) ⊆ S) :
    (∑ h : TerminalState N o,
      (if ∃ j : Fin (returnTime h), ¬core (inverse^[j.val] h.val).val ⊆ B
        then 1 else 0 : ℝ)) ≤
      (∑ x : Punctured N o,
        (if ¬S ⊆ core x.val ∧ S ⊆ core (inverse x).val then 1 else 0 : ℝ)) +
      ∑ x : Punctured N o,
        (if ¬S ⊆ core x.val ∧ ¬core x.val ⊆ B then 1 else 0 : ℝ) := by
  classical
  let q : Punctured N o → ℝ := fun x =>
    (if ¬S ⊆ core x.val ∧ S ⊆ core (inverse x).val then 1 else 0) +
      (if ¬S ⊆ core x.val ∧ ¬core x.val ⊆ B then 1 else 0)
  calc
    _ ≤ ∑ h : TerminalState N o, ∑ j : Fin (returnTime h), q (inverse^[j.val] h.val) := by
      apply Finset.sum_le_sum
      intro h _
      have hi := FiniteAvalanches.Probability.Excursions.large_visit_indicator_le
        (fun j => inverse^[j] h.val) (fun x : Punctured N o => S ⊆ core x.val)
        (fun x : Punctured N o => ¬core x.val ⊆ B)
        (by simpa only [Function.iterate_zero, id_eq] using terminal_omits_marked S hS h)
        (returnTime h)
      simpa only [Function.iterate_succ_apply', q] using hi
    _ = ∑ x : Punctured N o, q x := sum_inverse_excursions q
    _ = _ := by simp only [q, Finset.sum_add_distrib]

end
end FiniteAvalanches.Sandpile.Waves
