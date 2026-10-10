import FiniteAvalanches.Electrical.Plane.TerminalEnumeration

/-! Exact first return and neighboring slots of the original alpha enumeration. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

theorem incidenceCount_pos {V E : Type*} [Fintype E] {a b : E → V} (alpha : V)
    (da : Dart E) (ha : tail a b da = alpha) : 0 < incidenceCount a b alpha :=
  Fintype.card_pos_iff.mpr ⟨⟨da,ha⟩⟩

theorem alpha_first_return {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) :
    ((insertArcRotation R da db)^(incidenceCount a b alpha+1)) (.inr false) = .inr false ∧
      ∀ n : ℕ, 0 < n → n ≤ incidenceCount a b alpha →
        ((insertArcRotation R da db)^n) (.inr false) ≠ .inr false := by
  have hc := alpha_orbit_card R alpha beta hne da db ha hb
  constructor
  · simpa only [hc] using pow_cyclePoints_card (insertArcRotation R da db) (.inr false)
  · intro n hn hn' h
    have hlt : n < (cyclePoints (insertArcRotation R da db) (.inr false)).card := by rw [hc]; omega
    have h0 : 0 < (cyclePoints (insertArcRotation R da db) (.inr false)).card := by rw [hc]; omega
    have he := orbit_pow_inj (insertArcRotation R da db) (.inr false) hlt h0
      (show ((insertArcRotation R da db)^n) (.inr false) = ((insertArcRotation R da db)^0) (.inr false) from h)
    omega

theorem alphaEnumeration_first {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) :
    (alphaEnumeration R alpha beta hne da db ha hb ⟨0,incidenceCount_pos alpha da ha⟩).val = R.next da := by
  have hn : da ≠ db := by intro h; rw [h,hb] at ha; exact hne ha.symm
  have h := alphaEnumeration_spec R alpha beta hne da db ha hb ⟨0,incidenceCount_pos alpha da ha⟩
  simp only [Nat.zero_add,pow_one,insertArcRotation_arc_false R da db hn] at h
  exact Sum.inl_injective h

theorem alphaEnumeration_next {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (i j : Fin (incidenceCount a b alpha)) (hij : i.val+1 = j.val) :
    insertArcRotation R da db (.inl (alphaEnumeration R alpha beta hne da db ha hb i).val) =
      .inl (alphaEnumeration R alpha beta hne da db ha hb j).val := by
  rw [alphaEnumeration_spec,alphaEnumeration_spec,← Equiv.Perm.mul_apply,← pow_succ']
  rw [hij]

/-- Consecutive original incidences follow the original clockwise rotation itself. -/
theorem alphaEnumeration_next_original {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (i j : Fin (incidenceCount a b alpha)) (hij : i.val+1 = j.val) :
    R.next (alphaEnumeration R alpha beta hne da db ha hb i).val =
      (alphaEnumeration R alpha beta hne da db ha hb j).val := by
  have h := alphaEnumeration_next R alpha beta hne da db ha hb i j hij
  have hda : (alphaEnumeration R alpha beta hne da db ha hb i).val ≠ da := by
    intro he
    rw [he,insertArcRotation_alpha] at h
    cases h
  have hdb : (alphaEnumeration R alpha beta hne da db ha hb i).val ≠ db := by
    intro he
    have ht := (alphaEnumeration R alpha beta hne da db ha hb i).property
    rw [he,hb] at ht
    exact hne ht.symm
  rw [insertArcRotation_other R da db _ hda hdb] at h
  exact Sum.inl_injective h

theorem alphaEnumeration_last {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) :
    (alphaEnumeration R alpha beta hne da db ha hb
      ⟨incidenceCount a b alpha-1,by have h := incidenceCount_pos alpha da ha; omega⟩).val = da := by
  have hp := (alpha_first_return R alpha beta hne da db ha hb).1
  have hpos := incidenceCount_pos alpha da ha
  have h := alphaEnumeration_spec R alpha beta hne da db ha hb
    ⟨incidenceCount a b alpha-1,by omega⟩
  have hi : incidenceCount a b alpha-1+1 = incidenceCount a b alpha := by omega
  rw [hi] at h
  have ht : insertArcRotation R da db (.inl (alphaEnumeration R alpha beta hne da db ha hb
      ⟨incidenceCount a b alpha-1,by omega⟩).val) = .inr false := by
    rw [h,← Equiv.Perm.mul_apply,← pow_succ']
    exact hp
  rw [← insertArcRotation_alpha R da db] at ht
  exact Sum.inl_injective ((insertArcRotation R da db).injective ht)

end FiniteAvalanches.Electrical.Plane
