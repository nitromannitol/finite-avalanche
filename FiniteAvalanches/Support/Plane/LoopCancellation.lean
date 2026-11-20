import FiniteAvalanches.Support.Plane.NestedLoops

/-!
# Laminar families of loops

Nested intervals of a path can be combined into upper loops without introducing
new interior points. This supports the loop-cancellation construction of
J. Brazas, *Constructing arcs from paths using Zorn's Lemma*, Lemma 3,
https://arxiv.org/abs/2207.07242.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- Two parameter intervals are nested or disjoint in their interiors. -/
def IsLaminarIntervalFamily (S : Set (unitInterval × unitInterval)) : Prop :=
  ∀ v ∈ S, ∀ w ∈ S, (Ioo v.1 v.2 ∩ Ioo w.1 w.2).Nonempty →
    (v.1 ≤ w.1 ∧ w.2 ≤ v.2) ∨ (w.1 ≤ v.1 ∧ v.2 ≤ w.2)

/-- An interval is the covered upper interval of a laminar family at a point. -/
def IsIntervalUpperAt (S : Set (unitInterval × unitInterval))
    (t : unitInterval) (w : unitInterval × unitInterval) : Prop :=
  t ∈ Ioo w.1 w.2 ∧
    (∀ v ∈ S, t ∈ Ioo v.1 v.2 → w.1 ≤ v.1 ∧ v.2 ≤ w.2) ∧
    ∀ s ∈ Ioo w.1 w.2, ∃ v ∈ S, t ∈ Ioo v.1 v.2 ∧ s ∈ Ioo v.1 v.2

/-- The loops containing a point in a laminar family admit a covered upper loop. -/
theorem exists_intervalUpperAt {X : Type*} [TopologicalSpace X] [T2Space X]
    {x y : X} (p : Path x y) (S : Set (unitInterval × unitInterval))
    (hloop : ∀ v ∈ S, v.1 ≤ v.2 ∧ p v.1 = p v.2)
    (hlam : IsLaminarIntervalFamily S) {t : unitInterval}
    (ht : ∃ v ∈ S, t ∈ Ioo v.1 v.2) :
    ∃ w : unitInterval × unitInterval, p w.1 = p w.2 ∧ IsIntervalUpperAt S t w := by
  let T := {v ∈ S | t ∈ Ioo v.1 v.2}
  have hTne : T.Nonempty := by obtain ⟨v, hv, ht⟩ := ht; exact ⟨v, hv, ht⟩
  have hTloop : ∀ v ∈ T, v.1 ≤ v.2 ∧ p v.1 = p v.2 :=
    fun v hv => hloop v hv.1
  have hTchain : ∀ v ∈ T, ∀ w ∈ T,
      (v.1 ≤ w.1 ∧ w.2 ≤ v.2) ∨ (w.1 ≤ v.1 ∧ v.2 ≤ w.2) := by
    intro v hv w hw
    exact hlam v hv.1 w hw.1 ⟨t, hv.2, hw.2⟩
  obtain ⟨a, b, _, hab, hupper, hcover⟩ :=
    exists_upper_subloop_of_nested_with_coverage p T hTne hTloop hTchain
  have htupper : t ∈ Ioo a b := by
    obtain ⟨v, hv, htv⟩ := ht
    have hvT : v ∈ T := ⟨hv, htv⟩
    exact ⟨lt_of_le_of_lt (hupper v hvT).1 htv.1,
      lt_of_lt_of_le htv.2 (hupper v hvT).2⟩
  refine ⟨(a, b), hab, htupper, ?_, ?_⟩
  · intro v hv htv
    exact hupper v ⟨hv, htv⟩
  · intro s hs
    obtain ⟨v, hvT, hsv⟩ := hcover s hs.1 hs.2
    exact ⟨v, hvT.1, hvT.2, hsv⟩

end FiniteAvalanches.Electrical.StatementGeometry
