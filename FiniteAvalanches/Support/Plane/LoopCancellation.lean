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

/-- A member of a laminar family meeting a covered upper interval is contained
in that interval. -/
theorem IsIntervalUpperAt.contains_of_overlap
    {S : Set (unitInterval × unitInterval)} (hlam : IsLaminarIntervalFamily S)
    {t : unitInterval} {w v : unitInterval × unitInterval}
    (hw : IsIntervalUpperAt S t w) (hv : v ∈ S)
    (hoverlap : (Ioo w.1 w.2 ∩ Ioo v.1 v.2).Nonempty) :
    w.1 ≤ v.1 ∧ v.2 ≤ w.2 := by
  obtain ⟨s, hsw, hsv⟩ := hoverlap
  obtain ⟨u, hu, htu, hsu⟩ := hw.2.2 s hsw
  rcases hlam v hv u hu ⟨s, hsv, hsu⟩ with hvu | huv
  · have htv : t ∈ Ioo v.1 v.2 :=
      ⟨lt_of_le_of_lt hvu.1 htu.1, lt_of_lt_of_le htu.2 hvu.2⟩
    exact hw.2.1 v hv htv
  · have huupper := hw.2.1 u hu htu
    exact ⟨huupper.1.trans huv.1, huv.2.trans huupper.2⟩

/-- Two covered upper intervals of a laminar family that meet are equal. -/
theorem IsIntervalUpperAt.eq_of_overlap
    {S : Set (unitInterval × unitInterval)} (hlam : IsLaminarIntervalFamily S)
    {t u : unitInterval} {v w : unitInterval × unitInterval}
    (hv : IsIntervalUpperAt S t v) (hw : IsIntervalUpperAt S u w)
    (hoverlap : (Ioo v.1 v.2 ∩ Ioo w.1 w.2).Nonempty) : v = w := by
  obtain ⟨s, hsv, hsw⟩ := hoverlap
  obtain ⟨v', hv'S, htv', hsv'⟩ := hv.2.2 s hsv
  have hv'sub := hw.contains_of_overlap hlam hv'S ⟨s, hsw, hsv'⟩
  have htw : t ∈ Ioo w.1 w.2 :=
    ⟨lt_of_le_of_lt hv'sub.1 htv'.1, lt_of_lt_of_le htv'.2 hv'sub.2⟩
  obtain ⟨w', hw'S, huw', hsw'⟩ := hw.2.2 s hsw
  have hw'sub := hv.contains_of_overlap hlam hw'S ⟨s, hsv, hsw'⟩
  have huv : u ∈ Ioo v.1 v.2 :=
    ⟨lt_of_le_of_lt hw'sub.1 huw'.1, lt_of_lt_of_le huw'.2 hw'sub.2⟩
  have hsubvw : Ioo v.1 v.2 ⊆ Ioo w.1 w.2 := by
    intro z hz
    obtain ⟨k, hkS, htk, hzk⟩ := hv.2.2 z hz
    have hk := hw.contains_of_overlap hlam hkS ⟨t, htw, htk⟩
    exact ⟨lt_of_le_of_lt hk.1 hzk.1, lt_of_lt_of_le hzk.2 hk.2⟩
  have hsubwv : Ioo w.1 w.2 ⊆ Ioo v.1 v.2 := by
    intro z hz
    obtain ⟨k, hkS, huk, hzk⟩ := hw.2.2 z hz
    have hk := hv.contains_of_overlap hlam hkS ⟨u, huv, huk⟩
    exact ⟨lt_of_le_of_lt hk.1 hzk.1, lt_of_lt_of_le hzk.2 hk.2⟩
  have hvne : v.1 < v.2 := lt_trans hv.1.1 hv.1.2
  have hwne : w.1 < w.2 := lt_trans hw.1.1 hw.1.2
  have hvw := (Ioo_subset_Ioo_iff hvne).mp hsubvw
  have hwv := (Ioo_subset_Ioo_iff hwne).mp hsubwv
  apply Prod.ext
  · exact le_antisymm hwv.1 hvw.1
  · exact le_antisymm hvw.2 hwv.2

/-- A laminar family of nondegenerate subloops has a disjoint family of upper
subloops with the same union of interiors. -/
theorem exists_disjoint_upper_loop_family {X : Type*} [TopologicalSpace X] [T2Space X]
    {x y : X} (p : Path x y) (S : Set (unitInterval × unitInterval))
    (hloop : ∀ v ∈ S, v.1 < v.2 ∧ p v.1 = p v.2)
    (hlam : IsLaminarIntervalFamily S) :
    ∃ T : Set (unitInterval × unitInterval),
      (∀ v ∈ T, v.1 < v.2 ∧ p v.1 = p v.2) ∧
      (∀ v ∈ T, ∀ w ∈ T, v ≠ w → Disjoint (Ioo v.1 v.2) (Ioo w.1 w.2)) ∧
      (∀ v ∈ S, ∃ w ∈ T, w.1 ≤ v.1 ∧ v.2 ≤ w.2) ∧
      ∀ w ∈ T, ∀ t ∈ Ioo w.1 w.2, ∃ v ∈ S, t ∈ Ioo v.1 v.2 := by
  let T : Set (unitInterval × unitInterval) :=
    {w | p w.1 = p w.2 ∧ ∃ t, IsIntervalUpperAt S t w}
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · rintro v ⟨hv, t, ht⟩
    exact ⟨lt_trans ht.1.1 ht.1.2, hv⟩
  · rintro v ⟨_, t, ht⟩ w ⟨_, u, hu⟩ hne
    apply Set.disjoint_left.mpr
    intro s hs ht'
    exact hne (ht.eq_of_overlap hlam hu ⟨s, hs, ht'⟩)
  · intro v hv
    obtain ⟨t, ht1, ht2⟩ := exists_between (hloop v hv).1
    obtain ⟨w, hwloop, hw⟩ := exists_intervalUpperAt p S
      (fun z hz => ⟨(hloop z hz).1.le, (hloop z hz).2⟩) hlam ⟨v, hv, ht1, ht2⟩
    exact ⟨w, ⟨hwloop, t, hw⟩, hw.2.1 v hv ⟨ht1, ht2⟩⟩
  · rintro w ⟨_, t, hw⟩ s hs
    obtain ⟨v, hv, _, hsv⟩ := hw.2.2 s hs
    exact ⟨v, hv, hsv⟩

/-- A loop cancellation consists of pairwise interior-disjoint subloops. -/
def IsLoopCancellation {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (S : Set (unitInterval × unitInterval)) : Prop :=
  (∀ v ∈ S, v.1 < v.2 ∧ p v.1 = p v.2) ∧
  ∀ v ∈ S, ∀ w ∈ S, v ≠ w → Disjoint (Ioo v.1 v.2) (Ioo w.1 w.2)

/-- One loop family refines another if each of its intervals is contained in
an interval of the latter family. -/
def LoopFamilyRefines (S T : Set (unitInterval × unitInterval)) : Prop :=
  ∀ v ∈ S, ∃ w ∈ T, w.1 ≤ v.1 ∧ v.2 ≤ w.2

/-- Refinement of loop families is transitive. -/
theorem LoopFamilyRefines.trans {S T U : Set (unitInterval × unitInterval)}
    (hST : LoopFamilyRefines S T) (hTU : LoopFamilyRefines T U) : LoopFamilyRefines S U := by
  intro v hv
  obtain ⟨w, hw, hw1, hw2⟩ := hST v hv
  obtain ⟨z, hz, hz1, hz2⟩ := hTU w hw
  exact ⟨z, hz, hz1.trans hw1, hw2.trans hz2⟩

/-- The union of a refinement chain of loop cancellations is laminar. -/
theorem laminar_sUnion_of_loopCancellation_chain
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (C : Set (Set (unitInterval × unitInterval)))
    (hcancel : ∀ A ∈ C, IsLoopCancellation p A)
    (hchain : ∀ A ∈ C, ∀ B ∈ C, LoopFamilyRefines A B ∨ LoopFamilyRefines B A) :
    IsLaminarIntervalFamily (⋃₀ C) := by
  intro v hv w hw hoverlap
  obtain ⟨A, hAC, hvA⟩ := mem_sUnion.mp hv
  obtain ⟨B, hBC, hwB⟩ := mem_sUnion.mp hw
  obtain ⟨s, hsv, hsw⟩ := hoverlap
  rcases hchain A hAC B hBC with hAB | hBA
  · obtain ⟨u, huB, hu1, hu2⟩ := hAB v hvA
    have hsu : s ∈ Ioo u.1 u.2 :=
      ⟨lt_of_le_of_lt hu1 hsv.1, lt_of_lt_of_le hsv.2 hu2⟩
    have huw : u = w := by
      by_contra hne
      exact Set.disjoint_left.mp ((hcancel B hBC).2 u huB w hwB hne) hsu hsw
    subst u
    exact Or.inr ⟨hu1, hu2⟩
  · obtain ⟨u, huA, hu1, hu2⟩ := hBA w hwB
    have hsu : s ∈ Ioo u.1 u.2 :=
      ⟨lt_of_le_of_lt hu1 hsw.1, lt_of_lt_of_le hsw.2 hu2⟩
    have huv : u = v := by
      by_contra hne
      exact Set.disjoint_left.mp ((hcancel A hAC).2 u huA v hvA hne) hsu hsv
    subst u
    exact Or.inl ⟨hu1, hu2⟩

/-- Every refinement chain of loop cancellations has an upper loop cancellation. -/
theorem exists_upper_loopCancellation_of_chain
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X} (p : Path x y)
    (C : Set (Set (unitInterval × unitInterval)))
    (hcancel : ∀ A ∈ C, IsLoopCancellation p A)
    (hchain : ∀ A ∈ C, ∀ B ∈ C, LoopFamilyRefines A B ∨ LoopFamilyRefines B A) :
    ∃ T, IsLoopCancellation p T ∧ ∀ A ∈ C, LoopFamilyRefines A T := by
  have hloop : ∀ v ∈ ⋃₀ C, v.1 < v.2 ∧ p v.1 = p v.2 := by
    intro v hv
    obtain ⟨A, hA, hvA⟩ := mem_sUnion.mp hv
    exact (hcancel A hA).1 v hvA
  obtain ⟨T, hTloop, hTdisj, hTcover, _⟩ := exists_disjoint_upper_loop_family p (⋃₀ C)
    hloop (laminar_sUnion_of_loopCancellation_chain p C hcancel hchain)
  refine ⟨T, ⟨hTloop, hTdisj⟩, ?_⟩
  intro A hA v hv
  exact hTcover v (mem_sUnion.mpr ⟨A, hA, hv⟩)

end FiniteAvalanches.Electrical.StatementGeometry
