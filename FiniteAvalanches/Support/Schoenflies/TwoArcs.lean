/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/TwoArcs.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Subarc
import FiniteAvalanches.Support.Schoenflies.Concatenate

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





































open Set unitInterval

namespace Schoenflies

namespace IsLoop

variable {f : ℝ → Plane} {s t : ℝ}

 





 


theorem injective_before_finish (hf : IsLoop f) {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (h : f u = f v) : u = v :=
  hf.injOn ⟨hu.1, hu.2.lt_of_ne hu1⟩ ⟨hv.1, hv.2.lt_of_ne hv1⟩ h

 


theorem parameter_before_finish (hf : IsLoop f) {p : Plane} (hp : p ∈ f '' I) :
    ∃ u ∈ I, u ≠ 1 ∧ f u = p := by
  obtain ⟨u, hu, rfl⟩ := hp
  rcases eq_or_ne u 1 with rfl | hu1
  · exact ⟨0, zero_mem_I, one_ne_zero.symm, hf.closes⟩
  · exact ⟨u, hu, hu1, rfl⟩

 

theorem finish_eq_start (hf : IsLoop f) : f 1 = f 0 := hf.closes.symm

 







theorem front_subset_I (hs : s ∈ I) : Icc 0 s ⊆ I := Icc_subset_Icc le_rfl hs.2

theorem middle_subset_I (hs : s ∈ I) (ht : t ∈ I) : Icc s t ⊆ I := Icc_subset_Icc hs.1 ht.2

theorem back_subset_I (ht : t ∈ I) : Icc t 1 ⊆ I := Icc_subset_Icc ht.1 le_rfl

 

theorem injective_on_front (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) : InjOn f (Icc 0 s) := by
  have hs' : s < 1 := hs.2.lt_of_ne hs1
  intro u hu v hv h
  exact hf.injective_before_finish (front_subset_I hs hu) (front_subset_I hs hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 hs')) (ne_of_lt (lt_of_le_of_lt hv.2 hs')) h

 

theorem injective_on_middle (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1) :
    InjOn f (Icc s t) := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  intro u hu v hv h
  exact hf.injective_before_finish (middle_subset_I hs ht hu) (middle_subset_I hs ht hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 ht')) (ne_of_lt (lt_of_le_of_lt hv.2 ht')) h

 


theorem back_at_finish (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) {w : ℝ} (hw : w ∈ Icc t 1)
    (h : f w = f 1) : w = 1 := by
  by_contra hw1
  have : w = 0 :=
    hf.injective_before_finish (back_subset_I ht hw) zero_mem_I hw1 one_ne_zero.symm
      (h.trans hf.finish_eq_start)
  exact absurd (this ▸ hw.1) (not_le.mpr ht0)

 

theorem injective_on_back (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) : InjOn f (Icc t 1) := by
  intro u hu v hv h
  rcases eq_or_ne u 1 with rfl | hu1
  · exact (hf.back_at_finish ht ht0 hv h.symm).symm
  · rcases eq_or_ne v 1 with rfl | hv1
    · exact hf.back_at_finish ht ht0 hu h
    · exact hf.injective_before_finish (back_subset_I ht hu) (back_subset_I ht hv) hu1 hv1 h

 

 
theorem middle_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1)
    (hst : s < t) : IsArcBetween (f '' Icc s t) (f s) (f t) := by
  rw [← uIcc_of_le hst.le]
  refine isArcBetween_subarc hf.continuousOn ?_ hs ht (ne_of_lt hst)
  rw [uIcc_of_le hst.le]
  exact hf.injective_on_middle hs ht ht1

 
theorem front_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) (hs0 : 0 < s) :
    IsArcBetween (f '' Icc 0 s) (f 0) (f s) := by
  rw [← uIcc_of_le hs0.le]
  refine isArcBetween_subarc hf.continuousOn ?_ zero_mem_I hs (ne_of_lt hs0)
  rw [uIcc_of_le hs0.le]
  exact hf.injective_on_front hs hs1

 
theorem back_IsArcBetween (hf : IsLoop f) (ht : t ∈ I) (ht1 : t ≠ 1) (ht0 : 0 < t) :
    IsArcBetween (f '' Icc t 1) (f t) (f 1) := by
  rw [← uIcc_of_le ht.2]
  refine isArcBetween_subarc hf.continuousOn ?_ ht one_mem_I ht1
  rw [uIcc_of_le ht.2]
  exact hf.injective_on_back ht ht0

 






 



theorem back_meet_front (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1) (hst : s < t)
    {z : Plane} (hzb : z ∈ f '' Icc t 1) (hzf : z ∈ f '' Icc 0 s) : z = f 1 := by
  obtain ⟨b, hb, rfl⟩ := hzb
  obtain ⟨a, ha, hab⟩ := hzf
  have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
  rcases eq_or_ne b 1 with rfl | hb1
  · rfl
  · 
    
    have : b = a :=
      hf.injective_before_finish (back_subset_I ht hb) (front_subset_I hs ha) hb1 ha1 hab.symm
    exact absurd (this ▸ hb.1) (not_le.mpr (lt_of_le_of_lt ha.2 hst))

 
theorem outside_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    IsArcBetween (f '' Icc 0 s ∪ f '' Icc t 1) (f t) (f s) := by
  have ht0 : 0 < t := lt_of_le_of_lt hs.1 hst
  have hback : IsArcBetween (f '' Icc t 1) (f t) (f 1) := hf.back_IsArcBetween ht ht1 ht0
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · 
    
    have hfront : f '' Icc 0 s = {f 1} := by
      rw [← hs0, Icc_self, image_singleton, hf.finish_eq_start]
    have hone : f 1 ∈ f '' Icc t 1 := ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩
    rw [hfront, singleton_union, insert_eq_self.mpr hone, ← hs0, ← hf.finish_eq_start]
    exact hback
  · 
    have hfront : IsArcBetween (f '' Icc 0 s) (f 1) (f s) := by
      rw [hf.finish_eq_start]
      exact hf.front_IsArcBetween hs hs1 hs0
    have := hback.concatenate hfront (fun z hzb hzf => hf.back_meet_front hs ht hs1 hst hzb hzf)
    rwa [union_comm] at this

 

 


theorem parameters_split (hs : s ∈ I) (ht : t ∈ I) :
    I = Icc s t ∪ (Icc 0 s ∪ Icc t 1) := by
  ext x
  constructor
  · rintro ⟨h0, h1⟩
    rcases le_total x s with h | h
    · exact Or.inr (Or.inl ⟨h0, h⟩)
    · rcases le_total x t with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr (Or.inr ⟨h', h1⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨hs.1.trans h1, h2.trans ht.2⟩
    · exact ⟨h1, h2.trans hs.2⟩
    · exact ⟨ht.1.trans h1, h2⟩

 
theorem pieces_cover (hs : s ∈ I) (ht : t ∈ I) :
    f '' Icc s t ∪ (f '' Icc 0 s ∪ f '' Icc t 1) = f '' I := by
  rw [parameters_split hs ht, image_union, image_union]

 





theorem pieces_meet_at_ends (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    f '' Icc s t ∩ (f '' Icc 0 s ∪ f '' Icc t 1) = {f s, f t} := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  apply Subset.antisymm
  · rintro z ⟨⟨m, hm, rfl⟩, hzout⟩
    have hmI : m ∈ I := middle_subset_I hs ht hm
    have hm1 : m ≠ 1 := ne_of_lt (lt_of_le_of_lt hm.2 ht')
    rcases hzout with ⟨a, ha, hazm⟩ | ⟨b, hb, hbzm⟩
    · 
      have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
      have : m = a :=
        hf.injective_before_finish hmI (front_subset_I hs ha) hm1 ha1 hazm.symm
      rw [le_antisymm (this ▸ ha.2) hm.1]
      exact mem_insert _ _
    · rcases eq_or_ne b 1 with rfl | hb1
      · 
        
        have : m = 0 :=
          hf.injective_before_finish hmI zero_mem_I hm1 one_ne_zero.symm
            (hbzm.symm.trans hf.finish_eq_start)
        have hs0 : s = 0 := le_antisymm (this ▸ hm.1) hs.1
        rw [hs0, ← this]
        exact mem_insert _ _
      · 
        have : m = b :=
          hf.injective_before_finish hmI (back_subset_I ht hb) hm1 hb1 hbzm.symm
        rw [le_antisymm hm.2 (this ▸ hb.1)]
        exact mem_insert_of_mem _ rfl
  · rintro z (rfl | rfl)
    · exact ⟨⟨s, ⟨le_rfl, hst.le⟩, rfl⟩, Or.inl ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩⟩
    · exact ⟨⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, Or.inr ⟨t, ⟨le_rfl, ht.2⟩, rfl⟩⟩

 

 




theorem two_arcs_at_parameters (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    ∃ A B, IsArcBetween A (f s) (f t) ∧ IsArcBetween B (f t) (f s) ∧
      A ∪ B = f '' I ∧ A ∩ B = {f s, f t} :=
  ⟨f '' Icc s t, f '' Icc 0 s ∪ f '' Icc t 1,
    hf.middle_IsArcBetween hs ht ht1 hst,
    hf.outside_IsArcBetween hs ht hs1 ht1 hst,
    pieces_cover hs ht,
    hf.pieces_meet_at_ends hs ht hs1 ht1 hst⟩

end IsLoop

 

 









theorem IsJordanCurve.two_arcs {C : Set Plane} (hC : IsJordanCurve C) {p q : Plane}
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A B, IsArcBetween A p q ∧ IsArcBetween B p q ∧ A ∪ B = C ∧ A ∩ B = {p, q} := by
  obtain ⟨f, hf, rfl⟩ := hC
  obtain ⟨s, hs, hs1, rfl⟩ := hf.parameter_before_finish hp
  obtain ⟨t, ht, ht1, rfl⟩ := hf.parameter_before_finish hq
  
  rcases lt_or_gt_of_ne (fun h : s = t => hpq (by rw [h])) with hst | hts
  · obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters hs ht hs1 ht1 hst
    exact ⟨A, B, hA, hB.reverse, hcov, hmeet⟩
  · 
    obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters ht hs ht1 hs1 hts
    refine ⟨B, A, hB, hA.reverse, ?_, ?_⟩
    · rw [union_comm]; exact hcov
    · rw [inter_comm, hmeet, pair_comm]

 

theorem IsJordanCurve.two_arcs_of_two_arcs {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) (hmeet : A ∩ B = {p, q}) :
    IsJordanCurve (A ∪ B) :=
  IsJordanCurve.of_two_arcs hA hB.reverse fun z hzA hzB => by
    have : z ∈ ({p, q} : Set Plane) := hmeet ▸ ⟨hzA, hzB⟩
    exact this

end Schoenflies
