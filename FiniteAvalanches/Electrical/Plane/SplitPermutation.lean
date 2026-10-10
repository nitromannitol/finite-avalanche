import FiniteAvalanches.Electrical.Plane.Orbits
import FiniteAvalanches.Electrical.Plane.AuxiliaryArc

/-! Cut one permutation orbit at two distinct points and insert two arc darts. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

/-- Cross-splice the two successor links, retaining both original slots and two new darts. -/
noncomputable def splitPermutation {X : Type*} (f : Equiv.Perm X) (A B : X) :
    Equiv.Perm (X ⊕ Bool) :=
  (Equiv.swap (.inr false) (.inr true)).trans
    ((Equiv.swap (.inl A) (.inr false)).trans
      ((Equiv.swap (.inl B) (.inr true)).trans (Equiv.sumCongr f (Equiv.refl Bool))))

theorem splitPermutation_A {X : Type*} (f : Equiv.Perm X) (A B : X) :
    splitPermutation f A B (.inl A) = .inr false := by
  simp [splitPermutation,Equiv.swap_apply_def]

theorem splitPermutation_B {X : Type*} (f : Equiv.Perm X) (A B : X) (hne : A ≠ B) :
    splitPermutation f A B (.inl B) = .inr true := by
  simp [splitPermutation,Equiv.swap_apply_def,hne.symm]

theorem splitPermutation_false {X : Type*} (f : Equiv.Perm X) (A B : X) :
    splitPermutation f A B (.inr false) = .inl (f B) := by
  simp [splitPermutation,Equiv.swap_apply_def]

theorem splitPermutation_true {X : Type*} (f : Equiv.Perm X) (A B : X) (hne : A ≠ B) :
    splitPermutation f A B (.inr true) = .inl (f A) := by
  simp [splitPermutation,Equiv.swap_apply_def,hne]

theorem splitPermutation_other {X : Type*} (f : Equiv.Perm X) (A B x : X)
    (ha : x ≠ A) (hb : x ≠ B) : splitPermutation f A B (.inl x) = .inl (f x) := by
  simp [splitPermutation,Equiv.swap_apply_def,ha,hb]

/-- The actual augmented face walk is this cross-splice at the original right-face slots. -/
theorem arcFaceNext_eq_splitPermutation {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (hne : da ≠ db) :
    arcFaceNext R da db = splitPermutation R.faceNext (reverse E da) (reverse E db) := by
  have hn : reverse E da ≠ reverse E db := (reverse E).injective.ne hne
  ext d
  cases d with
  | inl d =>
    by_cases hda : d = reverse E da
    · subst d
      rw [splitPermutation_A]
      simp only [arcFaceNext,Equiv.trans_apply,arcReverse,Equiv.sumCongr_apply,Sum.map_inl,
        reverse_reverse,insertArcRotation_alpha]
    by_cases hdb : d = reverse E db
    · subst d
      rw [splitPermutation_B _ _ _ hn]
      simp only [arcFaceNext,Equiv.trans_apply,arcReverse,Equiv.sumCongr_apply,Sum.map_inl,
        reverse_reverse,insertArcRotation_beta R da db hne.symm]
    · rw [splitPermutation_other _ _ _ _ hda hdb]
      have ha : reverse E d ≠ da := by intro h; apply hda; rw [← h,reverse_reverse]
      have hb : reverse E d ≠ db := by intro h; apply hdb; rw [← h,reverse_reverse]
      simp only [arcFaceNext,Equiv.trans_apply,arcReverse,Equiv.sumCongr_apply,Sum.map_inl,
        insertArcRotation_other R da db _ ha hb,EdgeRotation.faceNext]
  | inr d => cases d with
    | false =>
      rw [splitPermutation_false]
      simp only [arcFaceNext,Equiv.trans_apply,arcReverse,Equiv.sumCongr_apply,Sum.map_inr,
        Equiv.swap_apply_left,insertArcRotation_arc_true,EdgeRotation.faceNext,reverse_reverse]
    | true =>
      rw [splitPermutation_true _ _ _ hn]
      simp only [arcFaceNext,Equiv.trans_apply,arcReverse,Equiv.sumCongr_apply,Sum.map_inr,
        Equiv.swap_apply_right,insertArcRotation_arc_false R da db hne,EdgeRotation.faceNext,reverse_reverse]

end FiniteAvalanches.Electrical.Plane
