import FiniteAvalanches.Electrical.Plane.CutOrbits

/-! Projection onto the original face orbits and preservation of every uncut orbit. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

abbrev OrbitQuotient {X : Type*} (f : Equiv.Perm X) := Quotient (Equiv.Perm.SameCycle.setoid f)
noncomputable instance {X : Type*} [Fintype X] (f : Equiv.Perm X) : Fintype (OrbitQuotient f) := Fintype.ofFinite _
def orbitClass {X : Type*} (f : Equiv.Perm X) (x : X) : OrbitQuotient f := Quotient.mk _ x

@[simp] theorem orbitClass_eq_iff {X : Type*} (f : Equiv.Perm X) (x y : X) :
    orbitClass f x = orbitClass f y ↔ f.SameCycle x y := Quotient.eq

theorem orbitClass_apply {X : Type*} (f : Equiv.Perm X) (x : X) :
    orbitClass f (f x) = orbitClass f x :=
  Quotient.sound (show f.SameCycle x (f x) from ⟨1,by simp⟩).symm

/-- Contract the two auxiliary darts onto their actual insertion slots. -/
def splitAnchor {X : Type*} (A B : X) : X ⊕ Bool → X
  | .inl x => x
  | .inr false => A
  | .inr true => B

theorem splitAnchor_class_step {X : Type*} (f : Equiv.Perm X) (A B : X)
    (hne : A ≠ B) (hAB : f.SameCycle A B) (d : X ⊕ Bool) :
    orbitClass f (splitAnchor A B (splitPermutation f A B d)) = orbitClass f (splitAnchor A B d) := by
  cases d with
  | inl x =>
    by_cases ha : x = A
    · subst x; rw [splitPermutation_A]; rfl
    by_cases hb : x = B
    · subst x; rw [splitPermutation_B _ _ _ hne]; rfl
    · rw [splitPermutation_other _ _ _ _ ha hb]; exact orbitClass_apply f x
  | inr c => cases c with
    | false => rw [splitPermutation_false]; exact (orbitClass_apply f B).trans (Quotient.sound hAB.symm)
    | true => rw [splitPermutation_true _ _ _ hne]; exact (orbitClass_apply f A).trans (Quotient.sound hAB)

/-- Every augmented face has a uniquely determined original face. -/
noncomputable def splitProjection {X : Type*} [Fintype X] (f : Equiv.Perm X) (A B : X)
    (hne : A ≠ B) (hAB : f.SameCycle A B) : OrbitQuotient (splitPermutation f A B) → OrbitQuotient f :=
  Quotient.lift (fun d => orbitClass f (splitAnchor A B d)) (by
    intro d d' h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hp : ∀ n : ℕ, orbitClass f (splitAnchor A B (((splitPermutation f A B)^n) d)) = orbitClass f (splitAnchor A B d) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,splitAnchor_class_step f A B hne hAB,ih]
    have ht := hp n
    rw [hn] at ht
    exact ht.symm)

@[simp] theorem splitProjection_class {X : Type*} [Fintype X] (f : Equiv.Perm X) (A B : X)
    (hne : A ≠ B) (hAB : f.SameCycle A B) (d : X ⊕ Bool) :
    splitProjection f A B hne hAB (orbitClass (splitPermutation f A B) d) = orbitClass f (splitAnchor A B d) := rfl

theorem splitPermutation_uncut_orbit {X : Type*} [Fintype X] (f : Equiv.Perm X) (A B x y : X)
    (hAB : f.SameCycle A B) (hx : ¬ f.SameCycle A x) (hxy : f.SameCycle x y) :
    (splitPermutation f A B).SameCycle (.inl x) (.inl y) := by
  obtain ⟨n,hn⟩ := hxy.exists_nat_pow_eq
  have hp : ∀ n : ℕ, (splitPermutation f A B).SameCycle (.inl x) (.inl ((f^n) x)) := by
    intro n
    induction n with
    | zero => exact .refl _ _
    | succ n ih =>
      have hnx : ¬ f.SameCycle A ((f^n) x) := by simpa only [Equiv.Perm.sameCycle_pow_right] using hx
      have ha : (f^n) x ≠ A := by intro h; rw [h] at hnx; exact hnx (.refl f A)
      have hb : (f^n) x ≠ B := by intro h; rw [h] at hnx; exact hnx hAB
      have hs : (splitPermutation f A B).SameCycle (.inl ((f^n) x))
          (splitPermutation f A B (.inl ((f^n) x))) := ⟨1,by simp⟩
      rw [splitPermutation_other _ _ _ _ ha hb,← Equiv.Perm.mul_apply,← pow_succ'] at hs
      exact ih.trans hs
  simpa only [hn] using hp n

end FiniteAvalanches.Electrical.Plane
