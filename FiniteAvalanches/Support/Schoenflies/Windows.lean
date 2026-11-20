/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Windows.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.SquareMesh
import FiniteAvalanches.Support.Schoenflies.JordanClosed

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





































































open Filter Metric Set

namespace Schoenflies

variable {C U : Set Plane} {p q x b : Plane} {r ε δ : ℝ}

 






 
theorem Plane.eq_of_supDist_eq_zero (h : Plane.supDist p q = 0) : p = q := by
  have hle : ‖p - q‖ ≤ Real.sqrt 2 * Plane.supNorm (p - q) := Plane.norm_le_sqrt_two_mul_supNorm _
  rw [show Plane.supNorm (p - q) = Plane.supDist p q from rfl, h, mul_zero] at hle
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hle (norm_nonneg _)))

 

 





noncomputable def supRadius (C : Set Plane) (p : Plane) : ℝ := sInf (Plane.supDist p '' C)

theorem supDist_continuousOn (p : Plane) : Continuous (Plane.supDist p) :=
  continuous_supNorm.comp (continuous_const.sub continuous_id)

 
theorem exists_supRadius_eq (hC : IsCompact C) (hCne : C.Nonempty) (p : Plane) :
    ∃ q ∈ C, supRadius C p = Plane.supDist p q ∧
      ∀ z ∈ C, Plane.supDist p q ≤ Plane.supDist p z := by
  obtain ⟨q, hqC, hmin⟩ := hC.exists_isMinOn hCne (supDist_continuousOn p).continuousOn
  have hle : ∀ z ∈ C, Plane.supDist p q ≤ Plane.supDist p z := fun z hz => isMinOn_iff.1 hmin z hz
  refine ⟨q, hqC, ?_, hle⟩
  refine IsLeast.csInf_eq ⟨⟨q, hqC, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hle z hz

 
theorem supRadius_le (hC : IsCompact C) (hCne : C.Nonempty) (p : Plane) (hq : q ∈ C) :
    supRadius C p ≤ Plane.supDist p q := by
  obtain ⟨z, -, heq, hmin⟩ := exists_supRadius_eq hC hCne p
  rw [heq]; exact hmin q hq

theorem supRadius_nonneg (hC : IsCompact C) (hCne : C.Nonempty) (p : Plane) :
    0 ≤ supRadius C p := by
  obtain ⟨z, -, heq, -⟩ := exists_supRadius_eq hC hCne p
  rw [heq]; exact Plane.supDist_nonneg _ _

 
theorem supRadius_pos (hC : IsCompact C) (hCne : C.Nonempty) (hp : p ∉ C) :
    0 < supRadius C p := by
  obtain ⟨q, hqC, heq, -⟩ := exists_supRadius_eq hC hCne p
  rw [heq]
  rcases (Plane.supDist_nonneg p q).lt_or_eq with h | h
  · exact h
  · exact absurd (Plane.eq_of_supDist_eq_zero h.symm ▸ hqC) hp

 

theorem notMem_of_supDist_lt_supRadius (hC : IsCompact C) (hCne : C.Nonempty)
    (h : Plane.supDist x p < supRadius C p) : x ∉ C := by
  intro hx
  exact absurd (supRadius_le hC hCne p hx) (not_le.2 (by rwa [Plane.supDist_comm p x]))

 




 
theorem supRadius_le_add (hC : IsCompact C) (hCne : C.Nonempty) (p q : Plane) :
    supRadius C p ≤ supRadius C q + Plane.supDist p q := by
  obtain ⟨z, hzC, heq, -⟩ := exists_supRadius_eq hC hCne q
  refine (supRadius_le hC hCne p hzC).trans ?_
  rw [heq, add_comm]
  exact Plane.supDist_triangle p q z

 
theorem abs_supRadius_sub_le (hC : IsCompact C) (hCne : C.Nonempty) (p q : Plane) :
    |supRadius C p - supRadius C q| ≤ Plane.supDist p q := by
  rw [abs_sub_le_iff]
  refine ⟨by linarith [supRadius_le_add hC hCne p q], ?_⟩
  have := supRadius_le_add hC hCne q p
  rw [Plane.supDist_comm q p] at this
  linarith

 

 



theorem openSquare_supRadius_subset_inside (hC : IsCompact C) (hCne : C.Nonempty)
    (hsep : IsSeparating C) (hp : p ∈ inside C) :
    Plane.openSquare p (supRadius C p) ⊆ inside C := by
  have hmiss : Plane.openSquare p (supRadius C p) ⊆ Cᶜ := fun x hx =>
    notMem_of_supDist_lt_supRadius hC hCne hx
  have hmem : p ∈ Plane.openSquare p (supRadius C p) := by
    have hpC : p ∉ C := fun h => (inside_subset_compl hp) h
    simpa [Plane.openSquare, Plane.supDist_self] using supRadius_pos hC hCne hpC
  have := (Plane.convex_openSquare p (supRadius C p)).isPreconnected.subset_connectedComponentIn
    hmem hmiss
  rwa [hsep.connectedComponentIn_eq_inside hp] at this

 




 
noncomputable def windowRadius (C : Set Plane) (ε : ℝ) (p : Plane) : ℝ :=
  supRadius C p - min (supRadius C p / 2) ε

 
noncomputable def window (C : Set Plane) (ε : ℝ) (p : Plane) : Set Plane :=
  Plane.closedSquare p (windowRadius C ε p)

 
noncomputable def openWindow (C : Set Plane) (ε : ℝ) (p : Plane) : Set Plane :=
  Plane.openSquare p (windowRadius C ε p)

 
theorem windowRadius_pos (hC : IsCompact C) (hCne : C.Nonempty) (hp : p ∉ C) :
    0 < windowRadius C ε p := by
  have hr := supRadius_pos hC hCne hp
  have : min (supRadius C p / 2) ε ≤ supRadius C p / 2 := min_le_left _ _
  rw [windowRadius]; linarith

 
theorem windowRadius_lt_supRadius (hC : IsCompact C) (hCne : C.Nonempty) (hp : p ∉ C)
    (hε : 0 < ε) : windowRadius C ε p < supRadius C p := by
  have hr := supRadius_pos hC hCne hp
  have : 0 < min (supRadius C p / 2) ε := lt_min (by linarith) hε
  rw [windowRadius]; linarith

 
theorem sub_windowRadius_le (C : Set Plane) (ε : ℝ) (p : Plane) :
    supRadius C p - windowRadius C ε p ≤ ε := by
  rw [windowRadius]
  simp

 
theorem le_windowRadius (C : Set Plane) (ε : ℝ) (p : Plane) :
    supRadius C p - ε ≤ windowRadius C ε p := by
  have := sub_windowRadius_le C ε p; linarith

 
theorem window_subset_inside (hC : IsCompact C) (hCne : C.Nonempty) (hsep : IsSeparating C)
    (hp : p ∈ inside C) (hε : 0 < ε) : window C ε p ⊆ inside C := by
  have hpC : p ∉ C := fun h => (inside_subset_compl hp) h
  refine subset_trans (fun x hx => ?_) (openSquare_supRadius_subset_inside hC hCne hsep hp)
  exact lt_of_le_of_lt hx (windowRadius_lt_supRadius hC hCne hpC hε)

 

 





theorem mem_openWindow_of_supDist_lt (hC : IsCompact C) (hCne : C.Nonempty)
    (hbx : Plane.supDist b x < supRadius C x / 8) (hε : ε < supRadius C x / 8) :
    x ∈ openWindow C ε b := by
  set d := supRadius C x with hd
  
  have hlip : d ≤ supRadius C b + Plane.supDist x b := supRadius_le_add hC hCne x b
  rw [Plane.supDist_comm x b] at hlip
  have hrb : 7 * d / 8 < supRadius C b := by linarith
  
  have hsb : 3 * d / 4 < windowRadius C ε b :=
    lt_of_lt_of_le (by linarith) (le_windowRadius C ε b)
  
  have hxb : Plane.supDist x b < d / 8 := by rwa [Plane.supDist_comm x b]
  have hdpos : 0 < d := by linarith [Plane.supDist_nonneg b x]
  exact lt_trans hxb (by linarith)

 





 

def recur {α : Type*} (f : ℕ → α) (n : ℕ) : α := f (Nat.unpair n).1

 


theorem exists_le_recur_eq {α : Type*} (f : ℕ → α) (k N : ℕ) :
    ∃ n, N ≤ n ∧ recur f n = f k :=
  ⟨Nat.pair k N, Nat.right_le_pair k N, by rw [recur, Nat.unpair_pair]⟩

 
theorem tendsto_two_pow_neg :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))

theorem two_pow_neg_pos (n : ℕ) : 0 < ((2 : ℝ) ^ n)⁻¹ := by positivity

 

theorem exists_mem_rat_supDist_lt {B : Set Plane} (hB : Dense B) (hU : IsOpen U)
    (hx : x ∈ U) (hδ : 0 < δ) : ∃ b ∈ B, b ∈ U ∧ Plane.supDist b x < δ := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨b, hbB, hbmem⟩ :=
    hB.exists_mem_open Metric.isOpen_ball ⟨x, mem_ball_self (lt_min hρ hδ)⟩
  refine ⟨b, hbB, hball (ball_subset_ball (min_le_left _ _) hbmem), ?_⟩
  refine lt_of_le_of_lt (Plane.supNorm_le_norm _) ?_
  rw [← dist_eq_norm]
  exact lt_of_lt_of_le (mem_ball.1 hbmem) (min_le_right _ _)

end Schoenflies
