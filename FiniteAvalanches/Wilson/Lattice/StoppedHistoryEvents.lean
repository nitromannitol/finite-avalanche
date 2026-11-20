import FiniteAvalanches.Wilson.Lattice.StoppedStackReading

/-! Measurable events of finite stopped direction histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile
open scoped Classical

noncomputable section

/-- Two words that agree through the first word's finite stopping time have
the same stopped direction history. -/
theorem stoppedDirectionHistory_eq_of_prefix (t : WalkDriver → ℕ)
    (ht : ∀ w w', (∀ i < t w, w' i = w i) → t w' = t w)
    (w w' : WalkDriver) (h : ∀ i < t w, w' i = w i) :
    stoppedDirectionHistory t w' = stoppedDirectionHistory t w := by
  have he := ht w w' h
  change (⟨t w', fun i => w' i.val⟩ : DirectionHistory) = ⟨t w, fun i => w i.val⟩
  apply Sigma.ext he
  apply Function.hfunext (congrArg Fin he)
  intro i j hij
  apply heq_of_eq
  have hij' : i.val = j.val := Fin.val_eq_val_of_heq hij
  dsimp only
  rw [hij']
  exact h j.val j.isLt

/-- A finite history occurs exactly when its extension stops at its stated
length and the word matches its recorded directions. -/
theorem stoppedDirectionHistory_eq_iff (t : WalkDriver → ℕ)
    (ht : ∀ w w', (∀ i < t w, w' i = w i) → t w' = t w)
    (w : WalkDriver) (p : DirectionHistory) :
    stoppedDirectionHistory t w = p ↔
      t p.extend = p.1 ∧ ∀ i < p.1, w i = p.extend i := by
  constructor
  · intro hp
    have hn : t w = p.1 := congrArg Sigma.fst hp
    have hw : ∀ i < p.1, p.extend i = w i := by
      intro i hi
      cases p with
      | mk m u =>
        change t w = m at hn
        subst m
        have hu : (⟨t w, fun j => w j.val⟩ : DirectionHistory) = ⟨t w, u⟩ := hp
        have hv : (fun j : Fin (t w) => w j.val) = u := by
          have heq : HEq (fun j : Fin (t w) => w j.val) u := by
            cases hu
            rfl
          exact eq_of_heq heq
        have hval : w i = u ⟨i, hi⟩ := congrFun hv ⟨i, hi⟩
        simp only [DirectionHistory.extend, dif_pos hi]
        exact hval.symm
    have he := ht w p.extend (fun i hi => hw i (hn ▸ hi))
    exact ⟨he.trans hn, fun i hi => (hw i hi).symm⟩
  · rintro ⟨htime, hw⟩
    have hstop : stoppedDirectionHistory t w = stoppedDirectionHistory t p.extend :=
      stoppedDirectionHistory_eq_of_prefix t ht p.extend w (by simpa only [htime] using hw)
    rw [hstop]
    cases p with
    | mk m u =>
      change t (DirectionHistory.extend ⟨m, u⟩) = m at htime
      change (⟨t (DirectionHistory.extend ⟨m, u⟩),
        fun i => DirectionHistory.extend ⟨m, u⟩ i.val⟩ : DirectionHistory) = ⟨m, u⟩
      apply Sigma.ext htime
      apply Function.hfunext (congrArg Fin htime)
      intro i j hij
      apply heq_of_eq
      have hij' : i.val = j.val := Fin.val_eq_val_of_heq hij
      dsimp only
      rw [hij']
      simp only [DirectionHistory.extend, dif_pos j.isLt]

/-- Every exact finite stopped direction history is a measurable walk event. -/
theorem measurableSet_stoppedDirectionHistory_eq (t : WalkDriver → ℕ)
    (ht : ∀ w w', (∀ i < t w, w' i = w i) → t w' = t w)
    (p : DirectionHistory) : MeasurableSet {w | stoppedDirectionHistory t w = p} := by
  have he : {w | stoppedDirectionHistory t w = p} =
      if t p.extend = p.1 then {w | ∀ i < p.1, w i = p.extend i} else ∅ := by
    ext w
    simp only [Set.mem_setOf_eq]
    rw [stoppedDirectionHistory_eq_iff t ht w p]
    split_ifs with h
    · simp only [h, true_and, Set.mem_setOf_eq]
    · simp only [h, false_and, Set.mem_empty_iff_false]
  rw [he]
  split_ifs
  · have heq : {w : WalkDriver | ∀ i < p.1, w i = p.extend i} =
        ⋂ i : Fin p.1, {w | w i.val = p.extend i.val} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h i
        exact h i.val i.isLt
      · intro h i hi
        exact h ⟨i, hi⟩
    rw [heq]
    exact MeasurableSet.iInter fun i =>
      (show Measurable (fun w : WalkDriver => w i.val) from measurable_pi_apply _)
        (measurableSet_singleton _)
  · exact MeasurableSet.empty

end
end FiniteAvalanches.Wilson.Lattice
