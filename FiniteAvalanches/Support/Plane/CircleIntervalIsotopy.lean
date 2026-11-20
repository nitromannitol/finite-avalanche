import FiniteAvalanches.Support.Plane.IntervalIsotopy
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.CompactOpen

/-!
# Circle isotopies from interval maps

An increasing homeomorphism of the unit interval induces a circle isotopy by
identifying its endpoints. Both the isotopy and its inverse are jointly continuous.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- The relation identifying the endpoints of the unit interval. -/
inductive CircleEndpointIdent : unitInterval → unitInterval → Prop
  | mk : CircleEndpointIdent 0 1

/-- The circle as the unit interval with its endpoints identified. -/
abbrev CircleQuot := Quot CircleEndpointIdent

/-- An increasing interval homeomorphism induces a jointly continuous circle
isotopy through equivalences, with jointly continuous inverses. -/
theorem exists_circle_isotopy_of_interval_homeomorph
    (f : unitInterval ≃ₜ unitInterval) (hf : StrictMono f) :
    ∃ E : unitInterval → CircleQuot ≃ CircleQuot,
      Continuous (fun p : unitInterval × CircleQuot => E p.1 p.2) ∧
      Continuous (fun p : unitInterval × CircleQuot => (E p.1).symm p.2) ∧
      (∀ x, E 0 x = x) ∧
      (∀ x : unitInterval, E 1 (Quot.mk _ x) = Quot.mk _ (f x)) := by
  obtain ⟨e, heq, he, hei, he0, he1⟩ := exists_interval_isotopy f hf
  have hmono (t : unitInterval) : StrictMono (e t) := by
    intro x y hxy
    rw [heq, heq]
    exact intervalInterpolation_strictMono f hf t hxy
  have ezero (t : unitInterval) : e t 0 = 0 := by
    obtain ⟨x, hx⟩ := (e t).surjective 0
    have h : e t 0 ≤ e t x := (hmono t).monotone (show 0 ≤ x from x.property.1)
    rw [hx] at h
    exact le_antisymm h (e t 0).property.1
  have eone (t : unitInterval) : e t 1 = 1 := by
    obtain ⟨x, hx⟩ := (e t).surjective 1
    have h : e t x ≤ e t 1 := (hmono t).monotone (show x ≤ 1 from x.property.2)
    rw [hx] at h
    exact le_antisymm (e t 1).property.2 h
  have hrel (t : unitInterval) (x y : unitInterval) :
      CircleEndpointIdent x y ↔
      CircleEndpointIdent (e t x) (e t y) := by
    constructor
    · intro h
      cases h
      simpa only [ezero, eone] using CircleEndpointIdent.mk
    · intro h
      have hend : ∀ {a b : unitInterval}, CircleEndpointIdent a b → a = 0 ∧ b = 1 := by
        intro a b hab
        cases hab
        exact ⟨rfl, rfl⟩
      obtain ⟨hx, hy⟩ := hend h
      have hx' : x = 0 := (e t).injective (hx.trans (ezero t).symm)
      have hy' : y = 1 := (e t).injective (hy.trans (eone t).symm)
      subst x
      subst y
      exact CircleEndpointIdent.mk
  let E : unitInterval → CircleQuot ≃ CircleQuot := fun t => Quot.congr (e t) (hrel t)
  have hE : Continuous (fun p : unitInterval × CircleQuot => E p.1 p.2) := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    change Continuous (fun p : unitInterval × unitInterval => Quot.mk _ (e p.1 p.2))
    exact continuous_quot_mk.comp he
  have hEi : Continuous (fun p : unitInterval × CircleQuot => (E p.1).symm p.2) := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    change Continuous (fun p : unitInterval × unitInterval => Quot.mk _ ((e p.1).symm p.2))
    exact continuous_quot_mk.comp hei
  refine ⟨E, hE, hEi, ?_, ?_⟩
  · intro x
    induction x using Quot.ind with
    | _ x => change Quot.mk _ (e 0 x) = Quot.mk _ x; rw [he0]
  · intro x
    change Quot.mk _ (e 1 x) = Quot.mk _ (f x)
    rw [he1]

end FiniteAvalanches.Electrical.StatementGeometry
