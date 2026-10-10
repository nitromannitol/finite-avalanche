import FiniteAvalanches.Electrical.Plane.FaceProjection
import Mathlib.Data.Fintype.Sum

/-! Exact cardinality of the actual cross-spliced face quotient. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

theorem split_faces_card_at_index {X : Type*} [Fintype X] (f : Equiv.Perm X) (A : X) (k : ℕ)
    (hk0 : 0 < k) (hk : k < (cyclePoints f A).card) :
    Fintype.card (OrbitQuotient (splitPermutation f A ((f^k) A))) =
      Fintype.card (OrbitQuotient f)+1 := by
  let B := (f^k) A
  have hAB : f.SameCycle A B := by dsimp [B]; simpa only [Equiv.Perm.sameCycle_pow_right] using Equiv.Perm.SameCycle.refl f A
  have hn : 0 < (cyclePoints f A).card := (cyclePoints_nonempty f A).card_pos
  have hne : A ≠ B := by
    intro h
    have he := orbit_pow_inj f A hn hk (show (f^0) A = (f^k) A from h)
    omega
  let qa := orbitClass f A
  let proj := splitProjection f A B hne hAB
  let t : ({q : OrbitQuotient f // q ≠ qa} ⊕ Bool) → OrbitQuotient (splitPermutation f A B)
    | .inl q => orbitClass (splitPermutation f A B) (.inl q.val.out)
    | .inr c => orbitClass (splitPermutation f A B) (.inr c)
  have hout (q : OrbitQuotient f) : orbitClass f q.out = q := Quotient.out_eq q
  have hp (z : {q : OrbitQuotient f // q ≠ qa} ⊕ Bool) :
      proj (t z) = match z with | .inl q => q.val | .inr _ => qa := by
    cases z with
    | inl q => exact hout q.val
    | inr c => cases c with
      | false => rfl
      | true => exact Quotient.sound hAB.symm
  have hbool : t (.inr false) ≠ t (.inr true) := by
    intro h
    exact splitPermutation_arc_not_sameCycle f A k hk0 hk (Quotient.exact h)
  have hbij : Function.Bijective t := by
    constructor
    · intro z w h
      have he := congrArg proj h
      rw [hp,hp] at he
      cases z with
      | inl z => cases w with
        | inl w => exact congrArg Sum.inl (Subtype.ext he)
        | inr c => exact (z.property he).elim
      | inr c => cases w with
        | inl w => exact (w.property he.symm).elim
        | inr d =>
          cases c <;> cases d
          · rfl
          · exact (hbool h).elim
          · exact (hbool h.symm).elim
          · rfl
    · intro q
      induction q using Quotient.inductionOn with
      | _ d =>
        cases d with
        | inl x =>
          by_cases hx : f.SameCycle A x
          · rcases splitPermutation_cut_orbit f A k hk0 hk x hx with h | h
            · exact ⟨.inr false,Quotient.sound h⟩
            · exact ⟨.inr true,Quotient.sound h⟩
          · have hq : orbitClass f x ≠ qa := by
              intro h
              exact hx ((Quotient.exact h : f.SameCycle x A).symm)
            let q : {q : OrbitQuotient f // q ≠ qa} := ⟨orbitClass f x,hq⟩
            have hxy : f.SameCycle q.val.out x := by
              change f.SameCycle (orbitClass f x).out x
              exact Quotient.mk_out (s := Equiv.Perm.SameCycle.setoid f) x
            have ho : ¬ f.SameCycle A q.val.out := fun h => hx (h.trans hxy)
            exact ⟨.inl q,Quotient.sound (splitPermutation_uncut_orbit f A B _ x hAB ho hxy)⟩
        | inr c => exact ⟨.inr c,rfl⟩
  have hc := Fintype.card_congr (Equiv.ofBijective t hbij)
  rw [Fintype.card_sum,Fintype.card_bool] at hc
  have hcompl : Fintype.card {q : OrbitQuotient f // q ≠ qa} = Fintype.card (OrbitQuotient f)-1 := by
    simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun q : OrbitQuotient f => q = qa)
  change Fintype.card {q : OrbitQuotient f // q ≠ qa}+2 =
    Fintype.card (OrbitQuotient (splitPermutation f A ((f^k) A))) at hc
  have hpos : 0 < Fintype.card (OrbitQuotient f) := Fintype.card_pos_iff.mpr ⟨qa⟩
  omega

theorem split_faces_card_of_sameCycle {X : Type*} [Fintype X] (f : Equiv.Perm X) (A B : X)
    (hne : A ≠ B) (hAB : f.SameCycle A B) :
    Fintype.card (OrbitQuotient (splitPermutation f A B)) = Fintype.card (OrbitQuotient f)+1 := by
  let k := orbitIndex f A B hAB
  have hspec : (f^k.val) A = B := orbitIndex_spec f A B hAB
  have hk0 : 0 < k.val := by
    by_contra h
    have he : k.val = 0 := by omega
    rw [he,pow_zero,Equiv.Perm.one_apply] at hspec
    exact hne hspec
  rw [← hspec]
  exact split_faces_card_at_index f A k.val hk0 k.isLt

theorem split_arc_not_sameCycle_of_sameCycle {X : Type*} [Fintype X] (f : Equiv.Perm X) (A B : X)
    (hne : A ≠ B) (hAB : f.SameCycle A B) :
    ¬ (splitPermutation f A B).SameCycle (.inr false) (.inr true) := by
  let k := orbitIndex f A B hAB
  have hspec : (f^k.val) A = B := orbitIndex_spec f A B hAB
  have hk0 : 0 < k.val := by
    by_contra h
    have he : k.val = 0 := by omega
    rw [he,pow_zero,Equiv.Perm.one_apply] at hspec
    exact hne hspec
  rw [← hspec]
  exact splitPermutation_arc_not_sameCycle f A k.val hk0 k.isLt

/-- Common RIGHT-face insertion splits exactly that original orbit, with distinct arc sides. -/
theorem arcFace_card_and_distinct {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (hne : da ≠ db)
    (hface : R.rightFace da = R.rightFace db) :
    Fintype.card (ArcFace R da db) = Fintype.card R.Face+1 ∧
      arcLeftFace R da db (.inr false) ≠ arcRightFace R da db (.inr false) := by
  have hab : R.faceNext.SameCycle (reverse E da) (reverse E db) := Quotient.exact hface
  have hn : reverse E da ≠ reverse E db := (reverse E).injective.ne hne
  have he := arcFaceNext_eq_splitPermutation R da db hne
  constructor
  · change Fintype.card (OrbitQuotient (arcFaceNext R da db)) = Fintype.card (OrbitQuotient R.faceNext)+1
    have hc := Fintype.card_congr (Equiv.cast (congrArg OrbitQuotient he))
    exact hc.trans (split_faces_card_of_sameCycle R.faceNext _ _ hn hab)
  · change orbitClass (arcFaceNext R da db) (.inr false) ≠ orbitClass (arcFaceNext R da db) (.inr true)
    intro h
    have hc : (arcFaceNext R da db).SameCycle (.inr false) (.inr true) := Quotient.exact h
    rw [he] at hc
    exact split_arc_not_sameCycle_of_sameCycle R.faceNext _ _ hn hab hc

end FiniteAvalanches.Electrical.Plane
