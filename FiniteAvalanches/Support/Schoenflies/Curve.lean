/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Curve.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Plane
import Mathlib.Topology.UnitInterval

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 

























open Set unitInterval

namespace Schoenflies

 

 
def IsArc (A : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A

 

def IsArcBetween (A : Set Plane) (p q : Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A ∧ f 0 = p ∧ f 1 = q

 
structure IsLoop (f : ℝ → Plane) : Prop where
  continuousOn : ContinuousOn f I
  closes : f 0 = f 1
  injOn : InjOn f (Ico 0 1)

 
def IsJordanCurve (C : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, IsLoop f ∧ f '' I = C

 

theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_refl 0, zero_le_one⟩

theorem one_mem_I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_refl 1⟩

theorem isCompact_I : IsCompact I := isCompact_Icc

theorem isConnected_I : IsConnected I := isConnected_Icc zero_le_one

 

theorem isCompact_image_of_subset_I {f : ℝ → Plane} (hf : ContinuousOn f I)
    {S : Set ℝ} (hS : S ⊆ I) (hSc : IsClosed S) : IsCompact (f '' S) :=
  (isCompact_I.of_isClosed_subset hSc hS).image_of_continuousOn (hf.mono hS)

 

namespace IsArcBetween

variable {A : Set Plane} {p q : Plane}

theorem isArc (h : IsArcBetween A p q) : IsArc A := by
  obtain ⟨f, hc, hi, him, -, -⟩ := h
  exact ⟨f, hc, hi, him⟩

theorem left_mem (h : IsArcBetween A p q) : p ∈ A := by
  obtain ⟨f, -, -, rfl, rfl, -⟩ := h
  exact mem_image_of_mem f zero_mem_I

theorem right_mem (h : IsArcBetween A p q) : q ∈ A := by
  obtain ⟨f, -, -, rfl, -, rfl⟩ := h
  exact mem_image_of_mem f one_mem_I

 
theorem reverse (h : IsArcBetween A p q) : IsArcBetween A q p := by
  obtain ⟨f, hc, hi, him, hp, hq⟩ := h
  refine ⟨fun t => f (1 - t), ?_, ?_, ?_, by simpa using hq, by simpa using hp⟩
  · 
    refine hc.comp (by fun_prop) fun t ht => ?_
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro s hs t ht hst
    have hs' : 1 - s ∈ I := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have := hi hs' ht' hst
    linarith
  · rw [← him]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring_nf⟩

end IsArcBetween

namespace IsArc

variable {A : Set Plane}

theorem isCompact (h : IsArc A) : IsCompact A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hc

theorem isConnected (h : IsArc A) : IsConnected A := by
  obtain ⟨f, hc, -, rfl⟩ := h
  exact isConnected_I.image f hc

theorem nonempty (h : IsArc A) : A.Nonempty := h.isConnected.nonempty

theorem isClosed (h : IsArc A) : IsClosed A := h.isCompact.isClosed

 
theorem exists_isArcBetween (h : IsArc A) : ∃ p q, IsArcBetween A p q := by
  obtain ⟨f, hc, hi, him⟩ := h
  exact ⟨f 0, f 1, f, hc, hi, him, rfl, rfl⟩

end IsArc

namespace IsJordanCurve

variable {C : Set Plane}

theorem isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isCompact_I.image_of_continuousOn hf.continuousOn

theorem isConnected (h : IsJordanCurve C) : IsConnected C := by
  obtain ⟨f, hf, rfl⟩ := h
  exact isConnected_I.image f hf.continuousOn

theorem nonempty (h : IsJordanCurve C) : C.Nonempty := h.isConnected.nonempty

theorem isClosed (h : IsJordanCurve C) : IsClosed C := h.isCompact.isClosed

end IsJordanCurve

end Schoenflies
