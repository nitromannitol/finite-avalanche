import FiniteAvalanches.Electrical.Plane.SplitPermutation

/-! The two actual orbit segments after a common-orbit cross-splice. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

/-- The segment containing B has indices 1,...,k; A and the other segment have color false. -/
noncomputable def cutColor {X : Type*} [Fintype X] (f : Equiv.Perm X) (A : X) (k : ℕ) :
    X ⊕ Bool → Bool
  | .inl x => if h : f.SameCycle A x then decide (0 < (orbitIndex f A x h).val ∧ (orbitIndex f A x h).val ≤ k) else false
  | .inr c => c

theorem cutColor_pow {X : Type*} [Fintype X] (f : Equiv.Perm X) (A : X) (k i : ℕ)
    (hi : i < (cyclePoints f A).card) :
    cutColor f A k (.inl ((f^i) A)) = decide (0 < i ∧ i ≤ k) := by
  have h : f.SameCycle A ((f^i) A) := by
    simpa only [Equiv.Perm.sameCycle_pow_right] using Equiv.Perm.SameCycle.refl f A
  simp only [cutColor,dif_pos h,orbitIndex_pow f A i hi]

theorem cutColor_invariant {X : Type*} [Fintype X] (f : Equiv.Perm X) (A : X) (k : ℕ)
    (hk0 : 0 < k) (hk : k < (cyclePoints f A).card) (d : X ⊕ Bool) :
    cutColor f A k (splitPermutation f A ((f^k) A) d) = cutColor f A k d := by
  let n := (cyclePoints f A).card
  have hn : 0 < n := (cyclePoints_nonempty f A).card_pos
  have hne : A ≠ (f^k) A := by
    intro h
    have he := orbit_pow_inj f A hn hk (show (f^0) A = (f^k) A from h)
    omega
  have hstep (i : ℕ) : f ((f^i) A) = (f^(i+1)) A := by rw [pow_succ',Equiv.Perm.mul_apply]
  cases d with
  | inl x =>
    by_cases hx : f.SameCycle A x
    · obtain ⟨i,hi,he⟩ := (isCycleOn_cyclePoints f A).exists_pow_eq
        ((mem_cyclePoints f A A).mpr (.refl f A)) ((mem_cyclePoints f A x).mpr hx)
      subst x
      by_cases hi0 : i = 0
      · subst i
        rw [pow_zero,Equiv.Perm.one_apply,splitPermutation_A]
        have hz := cutColor_pow f A k 0 hn
        change cutColor f A k (.inl A) = false at hz
        exact hz.symm
      by_cases hik : i = k
      · subst i
        rw [splitPermutation_B _ _ _ hne,cutColor_pow f A k k hk]
        simp only [cutColor,hk0,le_refl,and_self,decide_true]
      · have ha : (f^i) A ≠ A := by
          intro he
          have hn' := orbit_pow_inj f A hi hn (show (f^i) A = (f^0) A from he)
          exact hi0 hn'
        have hb : (f^i) A ≠ (f^k) A := fun he => hik (orbit_pow_inj f A hi hk he)
        rw [splitPermutation_other _ _ _ _ ha hb,hstep,cutColor_pow f A k i hi]
        by_cases hlast : i+1 < n
        · rw [cutColor_pow f A k (i+1) hlast]
          exact Bool.decide_congr (by omega)
        · have he : i+1 = n := by omega
          rw [he,pow_cyclePoints_card]
          have hz := cutColor_pow f A k 0 hn
          change cutColor f A k (.inl A) = false at hz
          rw [hz]
          have hik' : ¬ i ≤ k := by omega
          simp only [hik',and_false,decide_false]
    · have ha : x ≠ A := by intro he; subst x; exact hx (.refl f A)
      have hb : x ≠ (f^k) A := by intro he; subst x; exact hx (by simpa using Equiv.Perm.SameCycle.refl f A)
      have hfx : ¬ f.SameCycle A (f x) := by simpa using hx
      rw [splitPermutation_other _ _ _ _ ha hb]
      simp only [cutColor,dif_neg hx,dif_neg hfx]
  | inr c => cases c with
    | false =>
      rw [splitPermutation_false,hstep]
      by_cases hlast : k+1 < n
      · rw [cutColor_pow f A k (k+1) hlast]
        simp [cutColor]
      · have he : k+1 = n := by omega
        rw [he,pow_cyclePoints_card]
        have hz := cutColor_pow f A k 0 hn
        change cutColor f A k (.inl A) = false at hz
        rw [hz]
        simp [cutColor]
    | true =>
      rw [splitPermutation_true _ _ _ hne,← show (f^1) A = f A from rfl,
        cutColor_pow f A k 1 (by omega)]
      have hk1 : 1 ≤ k := by omega
      simp [cutColor,hk1]

theorem cutColor_eq_of_sameCycle {X : Type*} [Fintype X] (f : Equiv.Perm X) (A : X) (k : ℕ)
    (hk0 : 0 < k) (hk : k < (cyclePoints f A).card) {d d' : X ⊕ Bool}
    (h : (splitPermutation f A ((f^k) A)).SameCycle d d') : cutColor f A k d = cutColor f A k d' := by
  obtain ⟨m,hm⟩ := h.exists_nat_pow_eq
  have hp : ∀ m : ℕ, cutColor f A k (((splitPermutation f A ((f^k) A))^m) d) = cutColor f A k d := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ',Equiv.Perm.mul_apply,cutColor_invariant f A k hk0 hk,ih]
  have ht := hp m
  rw [hm] at ht
  exact ht.symm

theorem splitPermutation_arc_not_sameCycle {X : Type*} [Fintype X] (f : Equiv.Perm X) (A : X) (k : ℕ)
    (hk0 : 0 < k) (hk : k < (cyclePoints f A).card) :
    ¬ (splitPermutation f A ((f^k) A)).SameCycle (.inr false) (.inr true) := by
  intro h
  exact Bool.false_ne_true (cutColor_eq_of_sameCycle f A k hk0 hk h)

theorem splitPermutation_lower_segment {X : Type*} [Fintype X] (f : Equiv.Perm X) (A : X) (k : ℕ)
    (hk0 : 0 < k) (hk : k < (cyclePoints f A).card) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ k) :
    (splitPermutation f A ((f^k) A)).SameCycle (.inr true) (.inl ((f^i) A)) := by
  have hn : 0 < (cyclePoints f A).card := (cyclePoints_nonempty f A).card_pos
  have hne : A ≠ (f^k) A := by
    intro h
    have he := orbit_pow_inj f A hn hk (show (f^0) A = (f^k) A from h)
    omega
  have step (d : X ⊕ Bool) : (splitPermutation f A ((f^k) A)).SameCycle d
      (splitPermutation f A ((f^k) A) d) := ⟨1,by simp⟩
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases hi' : i = 0
    · subst i
      have h := step (.inr true)
      rw [splitPermutation_true _ _ _ hne] at h
      exact h
    · have hiPos : 0 < i := by omega
      have hiLt : i < (cyclePoints f A).card := by omega
      have ha : (f^i) A ≠ A := by
        intro h
        have he := orbit_pow_inj f A hiLt hn (show (f^i) A = (f^0) A from h)
        omega
      have hb : (f^i) A ≠ (f^k) A := by
        intro h
        have he := orbit_pow_inj f A hiLt hk h
        omega
      have h := step (.inl ((f^i) A))
      rw [splitPermutation_other _ _ _ _ ha hb,← Equiv.Perm.mul_apply,← pow_succ'] at h
      exact (ih hiPos (by omega)).trans h

theorem splitPermutation_upper_segment {X : Type*} [Fintype X] (f : Equiv.Perm X) (A : X) (k : ℕ)
    (hk : k < (cyclePoints f A).card) (l : ℕ)
    (hl : l ≤ (cyclePoints f A).card-k-1) :
    (splitPermutation f A ((f^k) A)).SameCycle (.inr false) (.inl ((f^(k+1+l)) A)) := by
  have hn : 0 < (cyclePoints f A).card := (cyclePoints_nonempty f A).card_pos
  have step (d : X ⊕ Bool) : (splitPermutation f A ((f^k) A)).SameCycle d
      (splitPermutation f A ((f^k) A) d) := ⟨1,by simp⟩
  induction l with
  | zero =>
    have h := step (.inr false)
    rw [splitPermutation_false,← Equiv.Perm.mul_apply,← pow_succ'] at h
    simpa only [Nat.add_zero] using h
  | succ l ih =>
    have hiLt : k+1+l < (cyclePoints f A).card := by omega
    have ha : (f^(k+1+l)) A ≠ A := by
      intro h
      have he := orbit_pow_inj f A hiLt hn (show (f^(k+1+l)) A = (f^0) A from h)
      omega
    have hb : (f^(k+1+l)) A ≠ (f^k) A := by
      intro h
      have he := orbit_pow_inj f A hiLt hk h
      omega
    have h := step (.inl ((f^(k+1+l)) A))
    rw [splitPermutation_other _ _ _ _ ha hb,← Equiv.Perm.mul_apply,← pow_succ'] at h
    have he : k+1+l+1 = k+1+(l+1) := by omega
    rw [he] at h
    exact (ih (by omega)).trans h

theorem splitPermutation_cut_orbit {X : Type*} [Fintype X] (f : Equiv.Perm X) (A : X) (k : ℕ)
    (hk0 : 0 < k) (hk : k < (cyclePoints f A).card) (x : X) (hx : f.SameCycle A x) :
    (splitPermutation f A ((f^k) A)).SameCycle (.inr false) (.inl x) ∨
    (splitPermutation f A ((f^k) A)).SameCycle (.inr true) (.inl x) := by
  obtain ⟨i,hi,he⟩ := (isCycleOn_cyclePoints f A).exists_pow_eq
    ((mem_cyclePoints f A A).mpr (.refl f A)) ((mem_cyclePoints f A x).mpr hx)
  subst x
  by_cases hi0 : i = 0
  · subst i
    left
    have h := splitPermutation_upper_segment f A k hk ((cyclePoints f A).card-k-1) le_rfl
    have hn : k+1+((cyclePoints f A).card-k-1) = (cyclePoints f A).card := by omega
    rw [hn,pow_cyclePoints_card] at h
    simpa only [pow_zero,Equiv.Perm.one_apply] using h
  by_cases hik : i ≤ k
  · right
    exact splitPermutation_lower_segment f A k hk0 hk i (by omega) hik
  · left
    have h := splitPermutation_upper_segment f A k hk (i-(k+1)) (by omega)
    have he : k+1+(i-(k+1)) = i := by omega
    rwa [he] at h

end FiniteAvalanches.Electrical.Plane
