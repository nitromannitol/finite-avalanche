/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/ArcMonotone.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Subarc

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




























































open Set unitInterval

namespace Schoenflies

 

open scoped Classical in
 



noncomputable def arcParam (f : ℝ → Plane) (p : Plane) : ℝ :=
  if h : ∃ s, s ∈ I ∧ f s = p then h.choose else 0

variable {f f' : ℝ → Plane} {g : Plane → Plane} {p : Plane} {s u : ℝ}

theorem arcParam_spec (hp : p ∈ f '' I) : arcParam f p ∈ I ∧ f (arcParam f p) = p := by
  have h : ∃ s, s ∈ I ∧ f s = p := by
    obtain ⟨s, hs, rfl⟩ := hp
    exact ⟨s, hs, rfl⟩
  rw [arcParam, dif_pos h]
  exact h.choose_spec

theorem arcParam_mem_I (hp : p ∈ f '' I) : arcParam f p ∈ I := (arcParam_spec hp).1

theorem apply_arcParam (hp : p ∈ f '' I) : f (arcParam f p) = p := (arcParam_spec hp).2

 
theorem arcParam_eq_of_apply (hi : InjOn f I) (hs : s ∈ I) (hfs : f s = p) : arcParam f p = s :=
  hi (arcParam_mem_I ⟨s, hs, hfs⟩) hs ((apply_arcParam ⟨s, hs, hfs⟩).trans hfs.symm)

 

 



structure ArcMatch (f f' : ℝ → Plane) (g : Plane → Plane) : Prop where
   
  continuousOn_src : ContinuousOn f I
   
  injOn_src : InjOn f I
   
  continuousOn_tgt : ContinuousOn f' I
   
  injOn_tgt : InjOn f' I
   
  continuousOn_map : ContinuousOn g (f '' I)
   
  injOn_map : InjOn g (f '' I)
   
  image_eq : g '' (f '' I) = f' '' I

 





noncomputable def transferParam (f f' : ℝ → Plane) (g : Plane → Plane) : ℝ → ℝ :=
  fun s => arcParam f' (g (f s))

namespace ArcMatch

variable (h : ArcMatch f f' g)
include h

theorem mem_image_map (hs : s ∈ I) : g (f s) ∈ f' '' I := by
  rw [← h.image_eq]
  exact ⟨f s, ⟨s, hs, rfl⟩, rfl⟩

theorem param_mem_I (hs : s ∈ I) : transferParam f f' g s ∈ I :=
  arcParam_mem_I (h.mem_image_map hs)

 

theorem apply_param (hs : s ∈ I) : f' (transferParam f f' g s) = g (f s) :=
  apply_arcParam (h.mem_image_map hs)

 
theorem param_eq (hu : u ∈ I) (heq : f' u = g (f s)) : transferParam f f' g s = u :=
  arcParam_eq_of_apply h.injOn_tgt hu heq

theorem injOn_param : InjOn (transferParam f f' g) I := by
  intro s hs u hu hsu
  
  have : g (f s) = g (f u) := by
    rw [← h.apply_param hs, ← h.apply_param hu, hsu]
  exact h.injOn_src hs hu (h.injOn_map ⟨s, hs, rfl⟩ ⟨u, hu, rfl⟩ this)

 



theorem continuousOn_param : ContinuousOn (transferParam f f' g) I := by
  intro s hs
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set u₀ := transferParam f f' g s with hu₀
  have hu₀I : u₀ ∈ I := h.param_mem_I hs
  have hval : f' u₀ = g (f s) := h.apply_param hs
  
  have hx : g (f s) ∈ f' '' (Ioo (u₀ - ε) (u₀ + ε) ∩ I) :=
    ⟨u₀, ⟨⟨by linarith, by linarith⟩, hu₀I⟩, hval⟩
  obtain ⟨r, hr, hball⟩ :=
    exists_ball_inter_subset_image h.continuousOn_tgt h.injOn_tgt isOpen_Ioo hx
  
  have hcomp : ContinuousWithinAt (fun x => g (f x)) I s :=
    (h.continuousOn_map (f s) ⟨s, hs, rfl⟩).comp (h.continuousOn_src s hs) (mapsTo_image f I)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp hcomp r hr
  refine ⟨δ, hδ, fun {x} hxI hxs => ?_⟩
  have hin : g (f x) ∈ Metric.ball (g (f s)) r ∩ f' '' I :=
    ⟨Metric.mem_ball.mpr (hclose hxI hxs), h.mem_image_map hxI⟩
  obtain ⟨v, ⟨hvw, hvI⟩, hveq⟩ := hball hin
  
  have : transferParam f f' g x = v :=
    h.injOn_tgt (h.param_mem_I hxI) hvI ((h.apply_param hxI).trans hveq.symm)
  rw [Real.dist_eq, this, abs_lt]
  exact ⟨by linarith [hvw.1], by linarith [hvw.2]⟩

 


theorem strictMonoOn_or_strictAntiOn_param :
    StrictMonoOn (transferParam f f' g) I ∨ StrictAntiOn (transferParam f f' g) I :=
  ContinuousOn.strictMonoOn_of_injOn_Icc' zero_le_one h.continuousOn_param h.injOn_param

 

theorem surjOn_param : I ⊆ transferParam f f' g '' I := by
  intro v hv
  have hmem : f' v ∈ g '' (f '' I) := by rw [h.image_eq]; exact ⟨v, hv, rfl⟩
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hmem
  exact ⟨x, hx, h.param_eq hv hy.symm⟩

 
theorem image_param_I : transferParam f f' g '' I = I :=
  subset_antisymm (by rintro _ ⟨x, hx, rfl⟩; exact h.param_mem_I hx) h.surjOn_param

 

theorem param_mem_uIcc (hs : s ∈ I) (hu : u ∈ I) {x : ℝ} (hx : x ∈ uIcc s u) :
    transferParam f f' g x ∈ uIcc (transferParam f f' g s) (transferParam f f' g u) := by
  have hxI : x ∈ I := uIcc_subset_I hs hu hx
  rw [mem_uIcc] at hx ⊢
  rcases h.strictMonoOn_or_strictAntiOn_param with hm | hm
  · rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨hm.monotoneOn hs hxI h₁, hm.monotoneOn hxI hu h₂⟩
    · exact Or.inr ⟨hm.monotoneOn hu hxI h₁, hm.monotoneOn hxI hs h₂⟩
  · rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨hm.antitoneOn hxI hu h₂, hm.antitoneOn hs hxI h₁⟩
    · exact Or.inl ⟨hm.antitoneOn hxI hs h₂, hm.antitoneOn hu hxI h₁⟩

 

theorem image_param_uIcc (hs : s ∈ I) (hu : u ∈ I) :
    transferParam f f' g '' uIcc s u =
      uIcc (transferParam f f' g s) (transferParam f f' g u) := by
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h.param_mem_uIcc hs hu hx
  · 
    exact intermediate_value_uIcc (h.continuousOn_param.mono (uIcc_subset_I hs hu))

 

theorem image_image_uIcc (hs : s ∈ I) (hu : u ∈ I) :
    g '' (f '' uIcc s u) =
      f' '' uIcc (transferParam f f' g s) (transferParam f f' g u) := by
  rw [← h.image_param_uIcc hs hu, ← image_comp, ← image_comp]
  refine image_congr fun x hx => ?_
  exact (h.apply_param (uIcc_subset_I hs hu hx)).symm

 
theorem image_subarc (hs : s ∈ I) (hu : u ∈ I) :
    g '' (subarc f s u '' I) =
      subarc f' (transferParam f f' g s) (transferParam f f' g u) '' I := by
  rw [subarc_image, subarc_image, h.image_image_uIcc hs hu]

 

section Endpoints

variable (h0 : g (f 0) = f' 0)
include h0

theorem param_zero : transferParam f f' g 0 = 0 := h.param_eq zero_mem_I h0.symm

 


theorem strictMonoOn_param : StrictMonoOn (transferParam f f' g) I := by
  rcases h.strictMonoOn_or_strictAntiOn_param with hm | hm
  · exact hm
  · exact absurd (hm zero_mem_I one_mem_I zero_lt_one)
      (by rw [h.param_zero h0]; exact not_lt.2 (h.param_mem_I one_mem_I).1)

theorem param_one : transferParam f f' g 1 = 1 := by
  
  obtain ⟨x, hx, hxv⟩ := h.surjOn_param one_mem_I
  have hge := (h.strictMonoOn_param h0).monotoneOn hx one_mem_I hx.2
  rw [hxv] at hge
  exact le_antisymm (h.param_mem_I one_mem_I).2 hge

 
theorem image_initial (hu : u ∈ I) :
    g '' (f '' Icc 0 u) = f' '' Icc 0 (transferParam f f' g u) := by
  have := h.image_image_uIcc zero_mem_I hu
  rwa [uIcc_of_le hu.1, h.param_zero h0, uIcc_of_le (h.param_mem_I hu).1] at this

 
theorem image_terminal (hu : u ∈ I) :
    g '' (f '' Icc u 1) = f' '' Icc (transferParam f f' g u) 1 := by
  have := h.image_image_uIcc hu one_mem_I
  rwa [uIcc_of_le hu.2, h.param_one h0, uIcc_of_le (h.param_mem_I hu).2] at this

 
theorem param_mem_Ioo (hu : u ∈ Ioo (0 : ℝ) 1) : transferParam f f' g u ∈ Ioo (0 : ℝ) 1 := by
  have hm := h.strictMonoOn_param h0
  refine ⟨?_, ?_⟩
  · rw [← h.param_zero h0]
    exact hm zero_mem_I (Ioo_subset_Icc_self hu) hu.1
  · rw [← h.param_one h0]
    exact hm (Ioo_subset_Icc_self hu) one_mem_I hu.2

end Endpoints

 


theorem param_mem_Ioo_of_ends (hends : (transferParam f f' g 0 = 0 ∧ transferParam f f' g 1 = 1) ∨
    (transferParam f f' g 0 = 1 ∧ transferParam f f' g 1 = 0)) (hu : u ∈ Ioo (0 : ℝ) 1) :
    transferParam f f' g u ∈ Ioo (0 : ℝ) 1 := by
  have huI : u ∈ I := Ioo_subset_Icc_self hu
  rcases h.strictMonoOn_or_strictAntiOn_param with hm | hm
  · rcases hends with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have hlo := hm zero_mem_I huI hu.1
      have hhi := hm huI one_mem_I hu.2
      rw [e0] at hlo
      rw [e1] at hhi
      exact ⟨hlo, hhi⟩
    · 
      have := hm zero_mem_I one_mem_I zero_lt_one
      rw [e0, e1] at this
      linarith
  · rcases hends with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have := hm zero_mem_I one_mem_I zero_lt_one
      rw [e0, e1] at this
      linarith
    · have hlo := hm huI one_mem_I hu.2
      have hhi := hm zero_mem_I huI hu.1
      rw [e1] at hlo
      rw [e0] at hhi
      exact ⟨hlo, hhi⟩

end ArcMatch

end Schoenflies
