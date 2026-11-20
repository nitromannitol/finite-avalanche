/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Subarc.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Curve

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 







































open Set unitInterval

namespace Schoenflies

 

 

def reparam (a b : ℝ) : ℝ → ℝ := fun t => a + t * (b - a)

variable {a b : ℝ}

@[simp] theorem reparam_zero : reparam a b 0 = a := by simp [reparam]

@[simp] theorem reparam_one : reparam a b 1 = b := by simp [reparam]

theorem continuous_reparam : Continuous (reparam a b) := by unfold reparam; fun_prop

 
theorem reparam_injective (hab : a ≠ b) : Function.Injective (reparam a b) := by
  intro s t hst
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have : s * (b - a) = t * (b - a) := by
    have := hst
    simp only [reparam] at this
    linarith
  exact mul_right_cancel₀ hba this

 

theorem image_reparam_I : reparam a b '' I = uIcc a b := by
  have h : (fun θ : ℝ => a + θ • (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b := by
    rw [← segment_eq_image' ℝ a b, segment_eq_uIcc]
  simpa [reparam, smul_eq_mul] using h

theorem mapsTo_reparam : MapsTo (reparam a b) I (uIcc a b) :=
  mapsTo_iff_image_subset.mpr image_reparam_I.subset

 

theorem uIcc_subset_I (ha : a ∈ I) (hb : b ∈ I) : uIcc a b ⊆ I :=
  uIcc_subset_Icc ha hb

 

 

def subarc (f : ℝ → Plane) (a b : ℝ) : ℝ → Plane := fun t => f (reparam a b t)

variable {f : ℝ → Plane}

@[simp] theorem subarc_zero : subarc f a b 0 = f a := by simp [subarc]

@[simp] theorem subarc_one : subarc f a b 1 = f b := by simp [subarc]

 

theorem subarc_image : subarc f a b '' I = f '' uIcc a b := by
  rw [show subarc f a b = f ∘ reparam a b from rfl, image_comp, image_reparam_I]

theorem subarc_image_subset (ha : a ∈ I) (hb : b ∈ I) : subarc f a b '' I ⊆ f '' I := by
  rw [subarc_image]
  exact image_mono (uIcc_subset_I ha hb)

theorem continuousOn_subarc (hc : ContinuousOn f I) (ha : a ∈ I) (hb : b ∈ I) :
    ContinuousOn (subarc f a b) I :=
  hc.comp continuous_reparam.continuousOn
    (mapsTo_reparam.mono_right (uIcc_subset_I ha hb))

 
theorem injOn_subarc (hi : InjOn f (uIcc a b)) (hab : a ≠ b) : InjOn (subarc f a b) I := by
  intro s hs t ht hst
  exact reparam_injective hab (hi (mapsTo_reparam hs) (mapsTo_reparam ht) hst)

 


theorem isArcBetween_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  ⟨subarc f a b, continuousOn_subarc hc ha hb, injOn_subarc hi hab,
    subarc_image, subarc_zero, subarc_one⟩

theorem isArc_subarc (hc : ContinuousOn f I) (hi : InjOn f (uIcc a b))
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) : IsArc (f '' uIcc a b) :=
  (isArcBetween_subarc hc hi ha hb hab).isArc

 
theorem isArcBetween_subarc_of_injOn_I (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    IsArcBetween (f '' uIcc a b) (f a) (f b) :=
  isArcBetween_subarc hc (hi.mono (uIcc_subset_I ha hb)) ha hb hab

 

theorem IsArc.exists_isArcBetween_subset {A : Set Plane} (h : IsArc A) {p q : Plane}
    (hp : p ∈ A) (hq : q ∈ A) (hpq : p ≠ q) : ∃ B ⊆ A, IsArcBetween B p q := by
  obtain ⟨f, hc, hi, rfl⟩ := h
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  refine ⟨f '' uIcc s t, image_mono (uIcc_subset_I hs ht), ?_⟩
  exact isArcBetween_subarc_of_injOn_I hc hi hs ht (fun h => hpq (by rw [h]))

 

 





def openArc (f : ℝ → Plane) : Set Plane := f '' Ioo 0 1

theorem Ioo_subset_I : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self

theorem openArc_subset : openArc f ⊆ f '' I := image_mono Ioo_subset_I

 


theorem openArc_eq_diff (hi : InjOn f I) : openArc f = f '' I \ {f 0, f 1} := by
  have hIoo : Ioo (0 : ℝ) 1 = I \ {0, 1} := by
    ext t
    simp only [mem_Ioo, mem_sdiff, mem_Icc, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨⟨h0.le, h1.le⟩, h0.ne', h1.ne⟩
    · rintro ⟨⟨h0, h1⟩, hne0, hne1⟩; exact ⟨h0.lt_of_ne' hne0, h1.lt_of_ne hne1⟩
  have hpair : f '' ({0, 1} : Set ℝ) = {f 0, f 1} := image_pair f 0 1
  rw [openArc, hIoo, hi.image_sdiff_subset (by
        rintro t (rfl | rfl); exacts [zero_mem_I, one_mem_I]), hpair]

 
theorem openArc_subarc (hab : a ≠ b) : openArc (subarc f a b) = f '' uIoo a b := by
  have h : reparam a b '' Ioo 0 1 = uIoo a b := by
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · 
      rw [uIoo_of_lt hlt]
      ext x
      simp only [mem_image, mem_Ioo, reparam]
      refine ⟨?_, fun hx => ⟨(x - a) / (b - a), ⟨?_, ?_⟩, by field_simp; ring⟩⟩
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · exact div_pos (by linarith [hx.1]) (by linarith)
      · exact (div_lt_one (by linarith)).mpr (by linarith [hx.2])
    · exact absurd rfl hab
    · 
      rw [uIoo_of_gt hgt]
      ext x
      simp only [mem_image, mem_Ioo, reparam]
      refine ⟨?_, fun hx => ⟨(a - x) / (a - b), ⟨?_, ?_⟩, by field_simp; ring⟩⟩
      · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
        constructor <;> nlinarith
      · exact div_pos (by linarith [hx.2]) (by linarith)
      · exact (div_lt_one (by linarith)).mpr (by linarith [hx.1])
  rw [openArc, show subarc f a b = f ∘ reparam a b from rfl, image_comp, h]

 








 

theorem IsArcBetween.diff_eq_openArc {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    ∃ f : ℝ → Plane, ContinuousOn f I ∧ A \ {p, q} = f '' Ioo 0 1 := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  exact ⟨f, hc, by rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]⟩

 
theorem IsArcBetween.isPreconnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsPreconnected (A \ {p, q}) := by
  obtain ⟨f, hc, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact isPreconnected_Ioo.image _ (hc.mono Ioo_subset_I)

 
theorem IsArcBetween.nonempty_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    (A \ {p, q}).Nonempty := by
  obtain ⟨f, -, hEq⟩ := h.diff_eq_openArc
  rw [hEq]
  exact ⟨f (1 / 2), 1 / 2, by norm_num, rfl⟩

 
theorem IsArcBetween.isConnected_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    IsConnected (A \ {p, q}) :=
  ⟨h.nonempty_diff, h.isPreconnected_diff⟩

 


theorem IsArcBetween.left_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : p ∈ closure (A \ {p, q}) := by
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := h
  have hEq : A \ {p, q} = f '' Ioo 0 1 := by
    rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi, openArc]
  
  rw [hEq, ← h0]
  refine ((hc 0 zero_mem_I).mono Ioo_subset_I).mem_closure_image ?_
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  exact zero_mem_I

theorem IsArcBetween.right_mem_closure_diff {A : Set Plane} {p q : Plane}
    (h : IsArcBetween A p q) : q ∈ closure (A \ {p, q}) := by
  rw [Set.pair_comm]
  exact h.reverse.left_mem_closure_diff

 

 







theorem image_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) {U : Set ℝ} (hU : IsOpen U) :
    ∃ V : Set Plane, IsOpen V ∧ f '' (U ∩ I) = V ∩ f '' I := by
  refine ⟨(f '' (I \ U))ᶜ, ?_, ?_⟩
  · 
    exact (isCompact_image_of_subset_I hc sdiff_subset
      (isClosed_Icc.sdiff hU)).isClosed.isOpen_compl
  · 
    have hdiff : f '' (I \ (I \ U)) = f '' I \ f '' (I \ U) :=
      hi.image_sdiff_subset sdiff_subset
    rw [sdiff_sdiff_right_self, inter_comm I U] at hdiff
    rw [hdiff, sdiff_eq, inter_comm]

 


theorem exists_ball_inter_subset_image (hc : ContinuousOn f I) (hi : InjOn f I)
    {U : Set ℝ} (hU : IsOpen U) {x : Plane} (hx : x ∈ f '' (U ∩ I)) :
    ∃ ε > 0, Metric.ball x ε ∩ f '' I ⊆ f '' (U ∩ I) := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi hU
  have hxV : x ∈ V := (hV ▸ hx).1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen x hxV
  exact ⟨ε, hε, fun y hy => hV ▸ ⟨hball hy.1, hy.2⟩⟩

 

theorem openArc_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I) :
    ∃ V : Set Plane, IsOpen V ∧ openArc f = V ∩ f '' I := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi (isOpen_Ioo (a := (0 : ℝ)) (b := 1))
  exact ⟨V, hVopen, by rwa [inter_eq_self_of_subset_left Ioo_subset_I] at hV⟩

 

theorem openArc_subarc_isRelOpen (hc : ContinuousOn f I) (hi : InjOn f I)
    (ha : a ∈ I) (hb : b ∈ I) :
    ∃ V : Set Plane, IsOpen V ∧ f '' uIoo a b = V ∩ f '' I := by
  obtain ⟨V, hVopen, hV⟩ := image_isRelOpen hc hi (U := uIoo a b) isOpen_Ioo
  refine ⟨V, hVopen, ?_⟩
  rwa [inter_eq_self_of_subset_left
    (uIoo_subset_uIcc_self.trans (uIcc_subset_I ha hb))] at hV

 

 





theorem basic_piece_inside_ball (hc : ContinuousOn f I) {x : Plane} (hx : x ∈ f '' I)
    {r : ℝ} (hr : 0 < r) :
    ∃ c d : ℝ, x ∈ f '' (Ioo c d ∩ I) ∧ f '' (Ioo c d ∩ I) ⊆ Metric.ball x r := by
  obtain ⟨s, hs, rfl⟩ := hx
  
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hc s hs) r hr
  refine ⟨s - δ, s + δ, ⟨s, ⟨⟨by linarith, by linarith⟩, hs⟩, rfl⟩, ?_⟩
  rintro y ⟨t, ⟨ht, htI⟩, rfl⟩
  have : dist t s < δ := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact Metric.mem_ball.mpr (hclose htI this)

end Schoenflies
