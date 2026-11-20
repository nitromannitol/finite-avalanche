/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Concatenate.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Curve

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




































open Set unitInterval

namespace Schoenflies

 

 
def lowerHalf : Set ℝ := Icc 0 (1 / 2)

 

def upperHalf : Set ℝ := Icc (1 / 2) 1

theorem lowerHalf_subset_I : lowerHalf ⊆ I := Icc_subset_Icc le_rfl (by norm_num)

theorem upperHalf_subset_I : upperHalf ⊆ I := Icc_subset_Icc (by norm_num) le_rfl

theorem halves_union : lowerHalf ∪ upperHalf = I :=
  Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)

theorem isClosed_lowerHalf : IsClosed lowerHalf := isClosed_Icc

theorem isClosed_upperHalf : IsClosed upperHalf := isClosed_Icc

 
theorem double_mem_I {t : ℝ} (ht : t ∈ lowerHalf) : 2 * t ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

 
theorem doubleBack_mem_I {t : ℝ} (ht : t ∈ upperHalf) : 2 * t - 1 ∈ I :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

 

 

noncomputable def concatenate (f g : ℝ → Plane) : ℝ → Plane :=
  fun t => if t ≤ 1 / 2 then f (2 * t) else g (2 * t - 1)

variable {f g : ℝ → Plane}

theorem concatenate_of_le {t : ℝ} (ht : t ≤ 1 / 2) : concatenate f g t = f (2 * t) :=
  if_pos ht

theorem concatenate_of_not_le {t : ℝ} (ht : ¬t ≤ 1 / 2) :
    concatenate f g t = g (2 * t - 1) :=
  if_neg ht

theorem concatenate_zero : concatenate f g 0 = f 0 := by
  rw [concatenate_of_le (by norm_num)]
  norm_num

theorem concatenate_one : concatenate f g 1 = g 1 := by
  rw [concatenate_of_not_le (by norm_num)]
  norm_num

 



theorem concatenate_upperHalf (hmid : f 1 = g 0) {t : ℝ} (ht : t ∈ upperHalf) :
    concatenate f g t = g (2 * t - 1) := by
  by_cases h : t ≤ 1 / 2
  · 
    have : t = 1 / 2 := le_antisymm h ht.1
    subst this
    rw [concatenate_of_le h]
    norm_num
    exact hmid
  · exact concatenate_of_not_le h

 

 

theorem continuousOn_concatenate (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (hmid : f 1 = g 0) : ContinuousOn (concatenate f g) I := by
  rw [← halves_union]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_lowerHalf isClosed_upperHalf
  · 
    have h : ContinuousOn (fun t : ℝ => f (2 * t)) lowerHalf :=
      hf.comp (by fun_prop) fun t ht => double_mem_I ht
    exact h.congr fun t ht => concatenate_of_le ht.2
  · 
    have h : ContinuousOn (fun t : ℝ => g (2 * t - 1)) upperHalf :=
      hg.comp (by fun_prop) fun t ht => doubleBack_mem_I ht
    exact h.congr fun t ht => concatenate_upperHalf hmid ht

 





theorem lowerHalf_at_finish (hfi : InjOn f I) {t : ℝ} (ht : t ∈ lowerHalf)
    (h : f (2 * t) = f 1) : t = 1 / 2 := by
  have := hfi (double_mem_I ht) one_mem_I h
  linarith

theorem lowerHalf_at_start (hfi : InjOn f I) {t : ℝ} (ht : t ∈ lowerHalf)
    (h : f (2 * t) = f 0) : t = 0 := by
  have := hfi (double_mem_I ht) zero_mem_I h
  linarith

theorem upperHalf_at_start (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 0) : t = 1 / 2 := by
  have := hgi (doubleBack_mem_I ht) zero_mem_I h
  linarith

theorem upperHalf_at_finish (hgi : InjOn g I) {t : ℝ} (ht : t ∈ upperHalf)
    (h : g (2 * t - 1) = g 1) : t = 1 := by
  have := hgi (doubleBack_mem_I ht) one_mem_I h
  linarith

 

 



theorem concatenate_seam (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  have hz : f (2 * x) = f 1 :=
    hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩
  have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
  rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

 
theorem injOn_concatenate (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1) : InjOn (concatenate f g) I := by
  intro x hx y hy h
  rcases le_or_gt x (1 / 2) with hxl | hxg
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · 
      rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
      have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
      linarith
    · exact concatenate_seam hfi hgi hmid hmeet ⟨hx.1, hxl⟩ ⟨hyg.le, hy.2⟩ h
  · rcases le_or_gt y (1 / 2) with hyl | hyg
    · exact (concatenate_seam hfi hgi hmid hmeet ⟨hy.1, hyl⟩ ⟨hxg.le, hx.2⟩ h.symm).symm
    · 
      rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
      have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2⟩) (doubleBack_mem_I ⟨hyg.le, hy.2⟩) h
      linarith

 

 

theorem image_concatenate (hmid : f 1 = g 0) : concatenate f g '' I = f '' I ∪ g '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases le_or_gt t (1 / 2) with h | h
    · exact Or.inl ⟨2 * t, double_mem_I ⟨ht.1, h⟩, (concatenate_of_le h).symm⟩
    · exact Or.inr ⟨2 * t - 1, doubleBack_mem_I ⟨h.le, ht.2⟩,
        (concatenate_of_not_le (not_le.2 h)).symm⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · 
      refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_of_le (by linarith [hu.2])]
      congr 1
      ring
    · refine ⟨(u + 1) / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      rw [concatenate_upperHalf hmid ⟨by linarith [hu.1], by linarith [hu.2]⟩]
      congr 1
      ring

 




 
theorem IsArcBetween.concatenate {A B : Set Plane} {a b c : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b c) (hmeet : ∀ z ∈ A, z ∈ B → z = b) :
    IsArcBetween (A ∪ B) a c := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf1]
    exact hmeet z hz hz'
  refine ⟨_, continuousOn_concatenate hfc hgc hmid, injOn_concatenate hfi hgi hmid hmeet',
    ?_, ?_, ?_⟩
  · rw [image_concatenate hmid, hfim, hgim]
  · rw [concatenate_zero]; exact hf0
  · rw [concatenate_one]; exact hg1

 
theorem IsArc.concatenate {A B : Set Plane} {a b c : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b c) (hmeet : ∀ z ∈ A, z ∈ B → z = b) : IsArc (A ∪ B) :=
  (hA.concatenate hB hmeet).isArc

 







 


theorem concatenate_seam_loop (hfi : InjOn f I) (hgi : InjOn g I) (hmid : f 1 = g 0)
    (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) {x y : ℝ}
    (hx : x ∈ lowerHalf) (hy : y ∈ upperHalf) (hy1 : y ≠ 1)
    (h : concatenate f g x = concatenate f g y) : x = y := by
  rw [concatenate_of_le hx.2, concatenate_upperHalf hmid hy] at h
  rcases hmeet _ ⟨2 * x, double_mem_I hx, rfl⟩ ⟨2 * y - 1, doubleBack_mem_I hy, h.symm⟩ with
    hz | hz
  · 
    exact absurd (upperHalf_at_finish hgi hy (by rw [← h, hz]; exact hclose.symm)) hy1
  · have hy' : g (2 * y - 1) = g 0 := by rw [← h, hz]; exact hmid
    rw [lowerHalf_at_finish hfi hx hz, upperHalf_at_start hgi hy hy']

 
theorem IsLoop.concatenate (hfc : ContinuousOn f I) (hfi : InjOn f I) (hgc : ContinuousOn g I)
    (hgi : InjOn g I) (hmid : f 1 = g 0) (hclose : g 1 = f 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1) :
    IsLoop (Schoenflies.concatenate f g) where
  continuousOn := continuousOn_concatenate hfc hgc hmid
  closes := by rw [concatenate_zero, concatenate_one]; exact hclose.symm
  injOn := by
    intro x hx y hy h
    have hy1 : y ≠ 1 := ne_of_lt hy.2
    have hx1 : x ≠ 1 := ne_of_lt hx.2
    rcases le_or_gt x (1 / 2) with hxl | hxg
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · rw [concatenate_of_le hxl, concatenate_of_le hyl] at h
        have := hfi (double_mem_I ⟨hx.1, hxl⟩) (double_mem_I ⟨hy.1, hyl⟩) h
        linarith
      · exact concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hx.1, hxl⟩
          ⟨hyg.le, hy.2.le⟩ hy1 h
    · rcases le_or_gt y (1 / 2) with hyl | hyg
      · exact (concatenate_seam_loop hfi hgi hmid hclose hmeet ⟨hy.1, hyl⟩
          ⟨hxg.le, hx.2.le⟩ hx1 h.symm).symm
      · rw [concatenate_of_not_le (not_le.2 hxg), concatenate_of_not_le (not_le.2 hyg)] at h
        have := hgi (doubleBack_mem_I ⟨hxg.le, hx.2.le⟩)
          (doubleBack_mem_I ⟨hyg.le, hy.2.le⟩) h
        linarith

 


theorem IsJordanCurve.of_two_arcs {A B : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
    (hB : IsArcBetween B b a) (hmeet : ∀ z ∈ A, z ∈ B → z = a ∨ z = b) :
    IsJordanCurve (A ∪ B) := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hmid : f 1 = g 0 := by rw [hf1, hg0]
  have hclose : g 1 = f 0 := by rw [hg1, hf0]
  have hmeet' : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0 ∨ z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    rw [hf0, hf1]
    exact hmeet z hz hz'
  refine ⟨_, IsLoop.concatenate hfc hfi hgc hgi hmid hclose hmeet', ?_⟩
  rw [image_concatenate hmid, hfim, hgim]

end Schoenflies
