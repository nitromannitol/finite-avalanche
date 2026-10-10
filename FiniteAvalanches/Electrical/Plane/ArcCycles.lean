import FiniteAvalanches.Electrical.Plane.AuxiliaryArc

/-! The auxiliary insertion has exactly the intended vertex cycles. -/
namespace FiniteAvalanches.Electrical.Plane

open scoped Classical

theorem insertArcRotation_old_step {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (hne : da ≠ db) (d : Dart E) :
    (insertArcRotation R da db).SameCycle (.inl d) (.inl (R.next d)) := by
  have step (x : ArcDart E) : (insertArcRotation R da db).SameCycle x (insertArcRotation R da db x) :=
    ⟨1,by simp⟩
  by_cases ha : d = da
  · subst d
    have h1 := step (.inl da)
    have h2 := step (.inr false)
    rw [insertArcRotation_alpha] at h1
    rw [insertArcRotation_arc_false R da db hne] at h2
    exact h1.trans h2
  by_cases hb : d = db
  · subst d
    have h1 := step (.inl db)
    have h2 := step (.inr true)
    rw [insertArcRotation_beta R da db hne.symm] at h1
    rw [insertArcRotation_arc_true] at h2
    exact h1.trans h2
  · simpa only [insertArcRotation_other R da db d ha hb] using step (.inl d)

theorem insertArcRotation_lift_sameCycle {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (hne : da ≠ db) {d d' : Dart E}
    (h : R.next.SameCycle d d') : (insertArcRotation R da db).SameCycle (.inl d) (.inl d') := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hp : ∀ n : ℕ, (insertArcRotation R da db).SameCycle (.inl d) (.inl ((R.next^n) d)) := by
    intro n
    induction n with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact ih.trans (insertArcRotation_old_step R da db hne ((R.next^n) d))
  simpa only [hn] using hp n

/-- Erasing an auxiliary incidence returns the old incidence where it was inserted. -/
def arcAnchor {E : Type*} (da db : Dart E) : ArcDart E → Dart E
  | .inl d => d
  | .inr false => da
  | .inr true => db

theorem insertArcRotation_sameCycle_anchor {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (hne : da ≠ db) (d : ArcDart E) :
    (insertArcRotation R da db).SameCycle d (.inl (arcAnchor da db d)) := by
  have step (x : ArcDart E) : (insertArcRotation R da db).SameCycle x (insertArcRotation R da db x) :=
    ⟨1,by simp⟩
  cases d with
  | inl d => exact Equiv.Perm.SameCycle.refl _ _
  | inr d => cases d with
    | false =>
      have h := step (.inl da)
      rw [insertArcRotation_alpha] at h
      exact h.symm
    | true =>
      have h := step (.inl db)
      rw [insertArcRotation_beta R da db hne.symm] at h
      exact h.symm

theorem arcTail_eq_tail_anchor {V E : Type*} (a b : E → V) (alpha beta : V)
    (da db : Dart E) (ha : tail a b da = alpha) (hb : tail a b db = beta) (d : ArcDart E) :
    arcTail a b alpha beta d = tail a b (arcAnchor da db d) := by
  cases d with
  | inl d => rfl
  | inr d => cases d <;> simp [arcTail,arcAnchor,ha,hb]

/-- All actual augmented incidences at a vertex lie on one cycle, and no cycle mixes vertices. -/
theorem insertArcRotation_sameCycle_iff {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (d d' : ArcDart E) :
    (insertArcRotation R da db).SameCycle d d' ↔
      arcTail a b alpha beta d = arcTail a b alpha beta d' := by
  have hdab : da ≠ db := by intro h; rw [h,hb] at ha; exact hne ha.symm
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hp : ∀ n : ℕ, arcTail a b alpha beta (((insertArcRotation R da db)^n) d) = arcTail a b alpha beta d := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ',Equiv.Perm.mul_apply,arcTail_insertArcRotation R alpha beta hne da db ha hb]
        exact ih
    have htail := hp n
    rw [hn] at htail
    exact htail.symm
  · intro h
    have htail : tail a b (arcAnchor da db d) = tail a b (arcAnchor da db d') := by
      simpa only [arcTail_eq_tail_anchor a b alpha beta da db ha hb] using h
    have hcycle := (R.cycles _ _).mpr htail
    exact (insertArcRotation_sameCycle_anchor R da db hdab d).trans
      ((insertArcRotation_lift_sameCycle R da db hdab hcycle).trans
        (insertArcRotation_sameCycle_anchor R da db hdab d').symm)

end FiniteAvalanches.Electrical.Plane
