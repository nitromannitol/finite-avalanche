import FiniteAvalanches.Electrical.Geometry.DrawingContraction
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.DrawingContraction
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open scoped Classical
noncomputable section

def fiberStep {V E W : Type} (J : CopiedGraph V E) (p : V → W) (x y : V) : Prop :=
  p x = p y ∧ ∃ e, (J.left e = x ∧ J.right e = y) ∨ (J.right e = x ∧ J.left e = y)

def restrictDrawing {V E F : Type} [Fintype V] [Fintype E] [Fintype F]
    {J : CopiedGraph V E} {K : CopiedGraph V F} (D : Drawing J)
    (i : F → E) (hi : Function.Injective i)
    (hl : ∀ f, J.left (i f) = K.left f) (hr : ∀ f, J.right (i f) = K.right f) : Drawing K where
  point := D.point
  point_injective := D.point_injective
  curve := fun f => D.curve (i f)
  continuous := fun f => D.continuous (i f)
  injective := fun f => D.injective (i f)
  start := fun f => (D.start (i f)).trans (congrArg D.point (hl f))
  finish := fun f => (D.finish (i f)).trans (congrArg D.point (hr f))
  avoids := fun f => D.avoids (i f)
  intersects := fun f g hfg => D.intersects (i f) (i g) (fun h => hfg (hi h))

def merge {V : Type} (a b : V) (hne : a ≠ b) (x : V) : {v : V // v ≠ b} :=
  if hx : x = b then ⟨a, hne⟩ else ⟨x, hx⟩

theorem merge_coe {V : Type} (a b : V) (hne : a ≠ b) (x : {v : V // v ≠ b}) :
    merge a b hne x.val = x := by
  simp only [merge, dif_neg x.property]

theorem merge_surjective {V : Type} (a b : V) (hne : a ≠ b) :
    Function.Surjective (merge a b hne) := by
  intro x
  exact ⟨x.val, merge_coe a b hne x⟩

theorem merge_kernel {V : Type} (a b : V) (hne : a ≠ b) (x y : V) :
    merge a b hne x = merge a b hne y ↔
      x = y ∨ ((x = a ∨ x = b) ∧ (y = a ∨ y = b)) := by
  by_cases hx : x = b <;> by_cases hy : y = b
  all_goals simp only [merge, hx, hy, dite_true, dite_false, Subtype.mk.injEq]
  all_goals aesop

theorem merge_fiber {V W : Type} (p : V → W) (a b : V) (hne : a ≠ b)
    (hab : p a = p b) (x : V) : p (merge a b hne x).val = p x := by
  by_cases hx : x = b
  · simp only [merge, dif_pos hx]
    exact hab.trans (congrArg p hx.symm)
  · simp only [merge, dif_neg hx]

private theorem quotient_induction (n : ℕ) :
    ∀ {V E W : Type} [Fintype V] [Fintype E] [Fintype W]
      (J : CopiedGraph V E) (D : Drawing J) (p : V → W),
      Fintype.card V = n → Function.Surjective p →
      (∀ x y, p x = p y → Relation.ReflTransGen (fiberStep J p) x y) →
      ∃ q : Plane → Plane, Continuous q ∧ ∃ Q : Drawing (quotientGraph J p),
        (∀ v, Q.point (p v) = q (D.point v)) ∧
        (∀ f t, Q.curve f t = q (D.curve f.val t)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E W _ _ _ J D p hn hsurj hconn
    by_cases hinj : Function.Injective p
    · let point (w : W) := D.point (Classical.choose (hsurj w))
      have point_eq (v : V) : point (p v) = D.point v := by
        exact congrArg D.point (hinj (Classical.choose_spec (hsurj (p v))))
      have point_inj : Function.Injective point := by
        intro x y he
        have hv := D.point_injective he
        exact (Classical.choose_spec (hsurj x)).symm.trans
          ((congrArg p hv).trans (Classical.choose_spec (hsurj y)))
      let Q : Drawing (quotientGraph J p) := {
        point := point
        point_injective := point_inj
        curve := fun f => D.curve f.val
        continuous := fun f => D.continuous f.val
        injective := fun f => D.injective f.val
        start := fun f => (D.start f.val).trans (point_eq _).symm
        finish := fun f => (D.finish f.val).trans (point_eq _).symm
        avoids := fun f t ht0 ht1 w => D.avoids f.val t ht0 ht1 (Classical.choose (hsurj w))
        intersects := fun f g hfg => D.intersects f.val g.val (fun h => hfg (Subtype.ext h)) }
      exact ⟨id, continuous_id, Q, point_eq, fun _ _ => rfl⟩
    · have edge_exists : ∃ e : E, J.left e ≠ J.right e ∧ p (J.left e) = p (J.right e) := by
        by_contra hh
        push Not at hh
        apply hinj
        intro x y hxy
        have hw := hconn x y hxy
        induction hw with
        | refl => rfl
        | @tail y z _ hstep hi =>
          obtain ⟨he, e, hor⟩ := hstep
          have ends : J.left e = J.right e := by
            by_contra hne
            apply hh e hne
            rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact he
            · exact he.symm
          have hyz : y = z := by
            rcases hor with ⟨hl, hr⟩ | ⟨hr, hl⟩
            · exact hl.symm.trans (ends.trans hr)
            · exact hr.symm.trans (ends.symm.trans hl)
          exact (hi (hxy.trans he.symm)).trans hyz
      obtain ⟨e, hne, he⟩ := edge_exists
      let m := merge (J.left e) (J.right e) hne
      let V' := {v : V // v ≠ J.right e}
      let E' := {f : E // m (J.left f) ≠ m (J.right f)}
      letI : Fintype E' := @Subtype.fintype E
        (fun f => m (J.left f) ≠ m (J.right f))
        (fun f => @instDecidableNot (m (J.left f) = m (J.right f))
          (Classical.propDecidable _)) inferInstance
      let J' : CopiedGraph V' E' := quotientGraph J m
      let p' : V' → W := fun v => p v.val
      have hpm (v : V) : p' (m v) = p v := merge_fiber p _ _ hne he v
      have hsurj' : Function.Surjective p' := by
        intro w
        obtain ⟨v, hv⟩ := hsurj w
        exact ⟨m v, (hpm v).trans hv⟩
      have hconn' : ∀ x y, p' x = p' y → Relation.ReflTransGen (fiberStep J' p') x y := by
        intro x y hxy
        have hw := hconn x.val y.val hxy
        have lift {a b : V} (h : Relation.ReflTransGen (fiberStep J p) a b) :
            Relation.ReflTransGen (fiberStep J' p') (m a) (m b) := by
          induction h with
          | refl => exact .refl
          | @tail b c _ hstep hi =>
            obtain ⟨hbc, f, hor⟩ := hstep
            by_cases hmc : m b = m c
            · exact hmc ▸ hi
            · have hf : m (J.left f) ≠ m (J.right f) := by
                rcases hor with ⟨hl, hr⟩ | ⟨hr, hl⟩
                · rw [hl, hr]
                  exact hmc
                · rw [hr, hl]
                  exact Ne.symm hmc
              apply hi.tail
              refine ⟨(hpm b).trans (hbc.trans (hpm c).symm), ⟨f, hf⟩, ?_⟩
              rcases hor with ⟨hl, hr⟩ | ⟨hr, hl⟩
              · exact Or.inl ⟨congrArg m hl, congrArg m hr⟩
              · exact Or.inr ⟨congrArg m hr, congrArg m hl⟩
        simpa only [m, merge_coe] using lift hw
      have hcard : Fintype.card V' < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := J.right e) (not_not.mpr rfl)
      obtain ⟨q0, hq0cont, _, D', hp0, hc0⟩ := contract_edge J D e hne m
        (merge_surjective _ _ hne) (merge_kernel _ _ hne)
      obtain ⟨q1, hq1cont, Q', hp1, hc1⟩ :=
        ih (Fintype.card V') hcard J' D' p' rfl hsurj' hconn'
      let i (f : {f : E // p (J.left f) ≠ p (J.right f)}) :
          {g : E' // p' (J'.left g) ≠ p' (J'.right g)} :=
        ⟨⟨f.val, fun hh => f.property ((hpm _).symm.trans
          ((congrArg p' hh).trans (hpm _)))⟩,
          fun hh => f.property ((hpm _).symm.trans (hh.trans (hpm _)))⟩
      have hi : Function.Injective i := by
        intro f g h
        exact Subtype.ext (congrArg (fun z => z.val.val) h)
      let Q : Drawing (quotientGraph J p) := restrictDrawing Q' i hi
        (fun f => hpm (J.left f.val)) (fun f => hpm (J.right f.val))
      refine ⟨q1 ∘ q0, hq1cont.comp hq0cont, Q, ?_, ?_⟩
      · intro v
        change Q'.point (p v) = q1 (q0 (D.point v))
        rw [← hpm v, hp1, hp0]
      · intro f t
        change Q'.curve (i f) t = q1 (q0 (D.curve f.val t))
        rw [hc1, hc0]

theorem connected_quotient {V E W : Type} [Fintype V] [Fintype E] [Fintype W]
    (J : CopiedGraph V E) (D : Drawing J) (p : V → W)
    (hsurj : Function.Surjective p)
    (hconn : ∀ x y, p x = p y → Relation.ReflTransGen (fiberStep J p) x y) :
    ∃ q : Plane → Plane, Continuous q ∧ ∃ Q : Drawing (quotientGraph J p),
      (∀ v, Q.point (p v) = q (D.point v)) ∧
      (∀ f t, Q.curve f t = q (D.curve f.val t)) :=
  quotient_induction (Fintype.card V) J D p rfl hsurj hconn

end
end FiniteAvalanches.Electrical.DrawingContraction
