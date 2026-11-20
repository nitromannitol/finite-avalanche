import FiniteAvalanches.Support.Plane.ArcAccess.NestedLoops
import Mathlib.Order.Zorn

/-!
# Laminar families of loops

Nested intervals of a path can be combined into upper loops without introducing
new interior points. This supports the loop-cancellation construction of
J. Brazas, *Constructing arcs from paths using Zorn's Lemma*, Lemma 3,
https://arxiv.org/abs/2207.07242.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.ArcAccess

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

/-- Every path in a Hausdorff space has a maximal loop cancellation. -/
theorem exists_maximal_loopCancellation
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X} (p : Path x y) :
    ∃ M, IsLoopCancellation p M ∧ ∀ T, IsLoopCancellation p T →
      LoopFamilyRefines M T → LoopFamilyRefines T M := by
  let α := {S : Set (unitInterval × unitInterval) // IsLoopCancellation p S}
  let rel : α → α → Prop := fun A B => LoopFamilyRefines A.1 B.1
  have hbound : ∀ C : Set α, IsChain rel C → ∃ B, ∀ A ∈ C, rel A B := by
    intro C hC
    let D : Set (Set (unitInterval × unitInterval)) := Subtype.val '' C
    have hcancel : ∀ A ∈ D, IsLoopCancellation p A := by
      rintro A ⟨A', _, rfl⟩
      exact A'.2
    have hchain : ∀ A ∈ D, ∀ B ∈ D, LoopFamilyRefines A B ∨ LoopFamilyRefines B A := by
      rintro A ⟨A', hA', rfl⟩ B ⟨B', hB', rfl⟩
      by_cases heq : A' = B'
      · subst B'
        left
        intro v hv
        exact ⟨v, hv, le_rfl, le_rfl⟩
      · exact hC hA' hB' heq
    obtain ⟨T, hT, hupper⟩ := exists_upper_loopCancellation_of_chain p D hcancel hchain
    refine ⟨⟨T, hT⟩, ?_⟩
    intro A hA
    exact hupper A.1 ⟨A, hA, rfl⟩
  obtain ⟨M, hM⟩ := exists_maximal_of_chains_bounded hbound
    (fun hAB hBC => LoopFamilyRefines.trans hAB hBC)
  refine ⟨M.1, M.2, ?_⟩
  intro T hT hMT
  exact hM ⟨T, hT⟩ hMT

/-- Distinct subloops in a maximal cancellation cannot share an endpoint. -/
theorem IsLoopCancellation.not_adjacent_of_maximal
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    {v w : unitInterval × unitInterval} (hv : v ∈ S) (hw : w ∈ S)
    (hjoin : v.2 = w.1) : False := by
  have hvlt := (hS.1 v hv).1
  have hwlt := (hS.1 w hw).1
  have hvw : v ≠ w := by
    intro heq
    subst w
    have heq' : v.2 = v.1 := hjoin
    exact (ne_of_lt hvlt) heq'.symm
  let j : unitInterval × unitInterval := (v.1, w.2)
  have hjlt : j.1 < j.2 := lt_trans hvlt (hjoin ▸ hwlt)
  have hjloop : p j.1 = p j.2 := (hS.1 v hv).2.trans (hjoin ▸ (hS.1 w hw).2)
  have hjdisj : ∀ k ∈ S, k ≠ v → k ≠ w → Disjoint (Ioo j.1 j.2) (Ioo k.1 k.2) := by
    intro k hk hkv hkw
    apply Set.disjoint_left.mpr
    intro z hzj hzk
    by_cases hzv : z < v.2
    · have hzv' : z ∈ Ioo v.1 v.2 := ⟨hzj.1, hzv⟩
      exact Set.disjoint_left.mp (hS.2 v hv k hk hkv.symm) hzv' hzk
    · by_cases hwz : w.1 < z
      · have hzw : z ∈ Ioo w.1 w.2 := ⟨hwz, hzj.2⟩
        exact Set.disjoint_left.mp (hS.2 w hw k hk hkw.symm) hzw hzk
      · have heq : z = v.2 := le_antisymm (by simpa only [hjoin] using le_of_not_gt hwz)
          (le_of_not_gt hzv)
        have hmaxlt : max v.1 k.1 < v.2 := by
          apply max_lt
          · exact hvlt
          · simpa only [← heq] using hzk.1
        obtain ⟨s, hs1, hs2⟩ := exists_between hmaxlt
        have hsv : s ∈ Ioo v.1 v.2 := ⟨lt_of_le_of_lt (le_max_left _ _) hs1, hs2⟩
        have hsk : s ∈ Ioo k.1 k.2 :=
          ⟨lt_of_le_of_lt (le_max_right _ _) hs1, lt_trans hs2 (heq ▸ hzk.2)⟩
        exact Set.disjoint_left.mp (hS.2 v hv k hk hkv.symm) hsv hsk
  let T : Set (unitInterval × unitInterval) := insert j {k ∈ S | k ≠ v ∧ k ≠ w}
  have hT : IsLoopCancellation p T := by
    constructor
    · intro k hk
      simp only [T, mem_insert_iff, mem_setOf_eq] at hk
      rcases hk with rfl | ⟨hk, -, -⟩
      · exact ⟨hjlt, hjloop⟩
      · exact hS.1 k hk
    · intro k hk l hl hne
      simp only [T, mem_insert_iff, mem_setOf_eq] at hk hl
      rcases hk with rfl | ⟨hk, hkv, hkw⟩ <;>
        rcases hl with rfl | ⟨hl, hlv, hlw⟩
      · exact (hne rfl).elim
      · exact hjdisj l hl hlv hlw
      · exact (hjdisj k hk hkv hkw).symm
      · exact hS.2 k hk l hl hne
  have href : LoopFamilyRefines S T := by
    intro k hk
    by_cases hkv : k = v
    · subst k
      exact ⟨j, mem_insert j _, le_rfl, le_of_lt (hjoin ▸ hwlt)⟩
    · by_cases hkw : k = w
      · subst k
        exact ⟨j, mem_insert j _, le_of_lt (hjoin ▸ hvlt), le_rfl⟩
      · exact ⟨k, mem_insert_of_mem j ⟨hk, hkv, hkw⟩, le_rfl, le_rfl⟩
  obtain ⟨r, hrS, hr1, hr2⟩ := hmax T hT href j (mem_insert j _)
  obtain ⟨t, htv1, htv2⟩ := exists_between hvlt
  have htr : t ∈ Ioo r.1 r.2 :=
    ⟨lt_of_le_of_lt hr1 htv1, lt_of_lt_of_le htv2
      (le_trans (le_of_lt (hjoin ▸ hwlt)) hr2)⟩
  have hrv : r = v := by
    by_contra hne
    exact Set.disjoint_left.mp (hS.2 r hrS v hv hne) htr ⟨htv1, htv2⟩
  subst r
  exact (not_le_of_gt (hjoin ▸ hwlt)) hr2

/-- The closed intervals of distinct loops in a maximal cancellation are
strictly separated. -/
theorem IsLoopCancellation.separated_of_maximal
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    {v w : unitInterval × unitInterval} (hv : v ∈ S) (hw : w ∈ S) (hne : v ≠ w) :
    v.2 < w.1 ∨ w.2 < v.1 := by
  by_contra h
  push Not at h
  have hvwne : v.2 ≠ w.1 := fun heq => hS.not_adjacent_of_maximal p hmax hv hw heq
  have hwvne : w.2 ≠ v.1 := fun heq => hS.not_adjacent_of_maximal p hmax hw hv heq
  have hleft : w.1 < v.2 := lt_of_le_of_ne h.1 hvwne.symm
  have hright : v.1 < w.2 := lt_of_le_of_ne h.2 hwvne.symm
  have hmaxmin : max v.1 w.1 < min v.2 w.2 := by
    rw [lt_min_iff, max_lt_iff, max_lt_iff]
    exact ⟨⟨(hS.1 v hv).1, hleft⟩, ⟨hright, (hS.1 w hw).1⟩⟩
  obtain ⟨t, ht1, ht2⟩ := exists_between hmaxmin
  have htv : t ∈ Ioo v.1 v.2 :=
    ⟨lt_of_le_of_lt (le_max_left _ _) ht1, lt_of_lt_of_le ht2 (min_le_left _ _)⟩
  have htw : t ∈ Ioo w.1 w.2 :=
    ⟨lt_of_le_of_lt (le_max_right _ _) ht1, lt_of_lt_of_le ht2 (min_le_right _ _)⟩
  exact Set.disjoint_left.mp (hS.2 v hv w hw hne) htv htw

/-- Equal path values at two points outside the interiors of a maximal loop
cancellation are the endpoints of one cancelled loop. -/
theorem IsLoopCancellation.eq_off_interiors_of_maximal
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    {a b : unitInterval} (hab : a < b) (heq : p a = p b)
    (ha : ∀ v ∈ S, a ∉ Ioo v.1 v.2) (hb : ∀ v ∈ S, b ∉ Ioo v.1 v.2) :
    ∃ v ∈ S, v.1 = a ∧ v.2 = b := by
  classical
  let j : unitInterval × unitInterval := (a, b)
  have hinside : ∀ v ∈ S, (Ioo a b ∩ Ioo v.1 v.2).Nonempty →
      a ≤ v.1 ∧ v.2 ≤ b := by
    intro v hv hoverlap
    obtain ⟨t, htj, htv⟩ := hoverlap
    constructor
    · by_contra h
      have hva : v.1 < a := lt_of_not_ge h
      exact ha v hv ⟨hva, lt_trans htj.1 htv.2⟩
    · by_contra h
      have hbv : b < v.2 := lt_of_not_ge h
      exact hb v hv ⟨lt_trans htv.1 htj.2, hbv⟩
  let T : Set (unitInterval × unitInterval) :=
    insert j {v ∈ S | Disjoint (Ioo a b) (Ioo v.1 v.2)}
  have hT : IsLoopCancellation p T := by
    constructor
    · intro v hv
      simp only [T, mem_insert_iff, mem_setOf_eq] at hv
      rcases hv with rfl | ⟨hv, -⟩
      · exact ⟨hab, heq⟩
      · exact hS.1 v hv
    · intro v hv w hw hvw
      simp only [T, mem_insert_iff, mem_setOf_eq] at hv hw
      rcases hv with rfl | ⟨hv, hdv⟩ <;> rcases hw with rfl | ⟨hw, hdw⟩
      · exact (hvw rfl).elim
      · exact hdw
      · exact hdv.symm
      · exact hS.2 v hv w hw hvw
  have href : LoopFamilyRefines S T := by
    intro v hv
    by_cases hd : Disjoint (Ioo a b) (Ioo v.1 v.2)
    · exact ⟨v, mem_insert_of_mem j ⟨hv, hd⟩, le_rfl, le_rfl⟩
    · have hinter : (Ioo a b ∩ Ioo v.1 v.2).Nonempty := Set.not_disjoint_iff_nonempty_inter.mp hd
      have hvj := hinside v hv hinter
      exact ⟨j, mem_insert j _, hvj.1, hvj.2⟩
  obtain ⟨v, hv, hv1, hv2⟩ := hmax T hT href j (mem_insert j _)
  have hv1' : a ≤ v.1 := by
    by_contra h
    have hlt : v.1 < a := lt_of_not_ge h
    exact ha v hv ⟨hlt, lt_of_lt_of_le hab hv2⟩
  have hv2' : v.2 ≤ b := by
    by_contra h
    have hlt : b < v.2 := lt_of_not_ge h
    exact hb v hv ⟨lt_of_le_of_lt hv1 hab, hlt⟩
  exact ⟨v, hv, le_antisymm hv1 hv1', le_antisymm hv2' hv2⟩

end FiniteAvalanches.Electrical.StatementGeometry.ArcAccess
