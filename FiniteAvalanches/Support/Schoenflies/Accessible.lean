/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Accessible.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Plane

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





























open Metric Set

namespace Schoenflies

variable {C D E : Set Plane} {p q v w : Plane} {r s s' t : ℝ}

 

 


def StronglyAccessible (D : Set Plane) (p : Plane) : Prop :=
  ∃ (q : Plane) (r : ℝ), 0 < r ∧ dist q p = r ∧ ball q r ⊆ D

theorem StronglyAccessible.mono (h : StronglyAccessible D p) (hDE : D ⊆ E) :
    StronglyAccessible E p := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  exact ⟨q, r, hr, hd, hball.trans hDE⟩

 
theorem StronglyAccessible.exists_ne (h : StronglyAccessible D p) :
    ∃ q ∈ D, p ≠ q := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  refine ⟨q, hball (mem_ball_self hr), fun hpq => ?_⟩
  rw [← hpq, dist_self] at hd
  exact absurd hd.symm hr.ne'

 







theorem stronglyAccessible_of_isMinOn {a : Plane} (hq : q ∉ C) (ha : a ∈ C)
    (hmin : ∀ b ∈ C, dist q a ≤ dist q b) (hD : connectedComponentIn Cᶜ q ⊆ D) :
    StronglyAccessible D a := by
  have hpos : 0 < dist q a := dist_pos.2 fun h => hq (h ▸ ha)
  refine ⟨q, dist q a, hpos, rfl, ?_⟩
  
  have hball : ball q (dist q a) ⊆ Cᶜ := by
    intro z hz hzC
    rw [mem_ball, dist_comm] at hz
    exact absurd (hmin z hzC) (not_le.2 hz)
  
  exact ((convex_ball q (dist q a)).isPreconnected.subset_connectedComponentIn
    (mem_ball_self hpos) hball).trans hD

 

 



def accessCone (p v : Plane) (s : ℝ) : Set Plane :=
  {x | ‖x - p‖ < s ∧ ‖x - p‖ / 2 < inner ℝ v (x - p)}

theorem mem_accessCone_iff {x : Plane} :
    x ∈ accessCone p v s ↔ ‖x - p‖ < s ∧ ‖x - p‖ / 2 < inner ℝ v (x - p) := Iff.rfl

theorem accessCone_subset_ball_self : accessCone p v s ⊆ ball p s := fun x hx => by
  rw [mem_ball, dist_eq_norm]; exact hx.1

 
theorem notMem_accessCone : p ∉ accessCone p v s := by
  intro h
  have := h.2
  simp at this

theorem accessCone_mono (hs : s ≤ s') : accessCone p v s ⊆ accessCone p v s' :=
  fun _ hx => ⟨hx.1.trans_le hs, hx.2⟩

 
theorem isOpen_accessCone : IsOpen (accessCone p v s) := by
  have h1 : Continuous fun x : Plane => ‖x - p‖ := (continuous_id.sub continuous_const).norm
  have h2 : Continuous fun x : Plane => inner ℝ v (x - p) :=
    continuous_const.inner (continuous_id.sub continuous_const)
  rw [accessCone, setOf_and]
  exact (isOpen_lt h1 continuous_const).inter (isOpen_lt (h1.div_const 2) h2)

 

theorem mem_accessCone (hw : ‖w‖ = 1) (hcone : 1 / 2 < inner ℝ v w) (ht : 0 < t) (hts : t < s) :
    p + t • w ∈ accessCone p v s := by
  have hsub : p + t • w - p = t • w := by module
  have hnorm : ‖p + t • w - p‖ = t := by
    rw [hsub, norm_smul, hw, Real.norm_eq_abs, abs_of_pos ht, mul_one]
  refine ⟨by rw [hnorm]; exact hts, ?_⟩
  rw [hnorm, hsub, real_inner_smul_right]
  nlinarith

 

theorem accessCone_nonempty (hv : ‖v‖ = 1) (hs : 0 < s) : (accessCone p v s).Nonempty := by
  refine ⟨p + (s / 2) • v, mem_accessCone hv ?_ (by linarith) (by linarith)⟩
  rw [real_inner_self_eq_norm_sq, hv]
  norm_num

 
theorem openSegment_subset_accessCone (hw : ‖w‖ = 1) (hcone : 1 / 2 < inner ℝ v w) (hs : 0 < s) :
    openSegment ℝ p (p + s • w) ⊆ accessCone p v s := by
  rintro x ⟨α, β, hα, hβ, hαβ, rfl⟩
  have hα' : α = 1 - β := by linarith
  subst hα'
  have hx : (1 - β) • p + β • (p + s • w) = p + (β * s) • w := by module
  rw [hx]
  exact mem_accessCone hw hcone (by positivity) (by nlinarith)

 

 





theorem accessCone_subset_ball (hr : 0 < r) (hpq : ‖q - p‖ = r) (hs : s ≤ r) :
    accessCone p (r⁻¹ • (q - p)) s ⊆ ball q r := by
  rintro x ⟨hlt, hcone⟩
  set d := ‖x - p‖ with hd
  set I := inner ℝ (q - p) (x - p) with hI
  
  rw [real_inner_smul_left] at hcone
  have hmul : r * (d / 2) < r * (r⁻¹ * I) := by
    exact mul_lt_mul_of_pos_left hcone hr
  have hcancel : r * (r⁻¹ * I) = I := by
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [hcancel] at hmul
  
  have hcs : I ≤ r * d := by
    have := real_inner_le_norm (q - p) (x - p)
    rwa [hpq] at this
  have hd0 : 0 < d := by nlinarith [norm_nonneg (x - p)]
  have hdr : d < r := hlt.trans_le hs
  
  have hxq : x - q = (x - p) - (q - p) := by module
  have key : ‖x - q‖ ^ 2 < r ^ 2 := by
    rw [hxq, norm_sub_sq_real, hpq, real_inner_comm]
    nlinarith
  rw [mem_ball, dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hr.le key

 


theorem tangent_cone (hr : 0 < r) (hpq : ‖q - p‖ = r) (hw : ‖w‖ = 1)
    (hcone : 1 / 2 < inner ℝ (r⁻¹ • (q - p)) w) (ht : 0 < t) (htr : t < r) :
    p + t • w ∈ ball q r :=
  accessCone_subset_ball hr hpq le_rfl (mem_accessCone hw hcone ht htr)

 


theorem StronglyAccessible.exists_cone (h : StronglyAccessible D p) :
    ∃ v : Plane, ‖v‖ = 1 ∧ ∃ r > 0, ∀ s ≤ r, accessCone p v s ⊆ D := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  have hpq : ‖q - p‖ = r := by rw [← dist_eq_norm]; exact hd
  refine ⟨r⁻¹ • (q - p), ?_, r, hr, fun s hs => (accessCone_subset_ball hr hpq hs).trans hball⟩
  rw [norm_smul, hpq, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_cancel₀ hr.ne']

 

theorem StronglyAccessible.openSegment_subset (h : StronglyAccessible D p) :
    ∃ z ∈ D, p ≠ z ∧ openSegment ℝ p z ⊆ D := by
  obtain ⟨q, r, hr, hd, hball⟩ := h
  refine ⟨q, hball (mem_ball_self hr), ?_, ?_⟩
  · intro hpq
    rw [← hpq, dist_self] at hd
    exact absurd hd.symm hr.ne'
  · rintro x ⟨α, β, hα, hβ, hαβ, rfl⟩
    have hα' : α = 1 - β := by linarith
    subst hα'
    refine hball ?_
    have hx : (1 - β) • p + β • q - q = (1 - β) • (p - q) := by module
    rw [mem_ball, dist_eq_norm, hx, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
      ← dist_eq_norm, dist_comm, hd]
    nlinarith

 

 







theorem exists_countable_dense_stronglyAccessible (hC : IsCompact C) (hCne : C.Nonempty)
    (hDopen : IsOpen D) (hDC : D ⊆ Cᶜ) (hDmax : ∀ q ∈ D, connectedComponentIn Cᶜ q ⊆ D)
    (hCD : C ⊆ closure D) :
    ∃ A ⊆ C, A.Countable ∧ (∀ a ∈ A, StronglyAccessible D a) ∧ C ⊆ closure A := by
  
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense Plane
  
  have hnear : ∀ x : Plane, ∃ a, a ∈ C ∧ ∀ b ∈ C, dist x a ≤ dist x b := by
    intro x
    obtain ⟨a, haC, hmin⟩ :=
      hC.exists_isMinOn hCne (Continuous.continuousOn (continuous_const.dist continuous_id))
    exact ⟨a, haC, fun b hb => isMinOn_iff.1 hmin b hb⟩
  choose f hfC hfmin using hnear
  refine ⟨f '' (S ∩ D), ?_, (hScount.mono inter_subset_left).image f, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hfC x
  · rintro _ ⟨x, hx, rfl⟩
    exact stronglyAccessible_of_isMinOn (hDC hx.2) (hfC x) (hfmin x) (hDmax x hx.2)
  · 
    intro p hp
    rw [Metric.mem_closure_iff]
    intro ε hε
    
    obtain ⟨y, hyD, hy⟩ := Metric.mem_closure_iff.1 (hCD hp) (ε / 2) (by linarith)
    
    obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.1 hDopen y hyD
    obtain ⟨z, hzS, hz⟩ := hSdense.exists_dist_lt y (lt_min hδ (by linarith : 0 < ε / 2 - dist p y))
    have hzD : z ∈ D := hδD (by rw [mem_ball, dist_comm]; exact hz.trans_le (min_le_left _ _))
    have hpz : dist p z < ε / 2 := by
      have := (dist_triangle p y z).trans_lt
        (by linarith [hz.trans_le (min_le_right δ (ε / 2 - dist p y))] :
          dist p y + dist y z < ε / 2)
      exact this
    
    refine ⟨f z, ⟨z, ⟨hzS, hzD⟩, rfl⟩, ?_⟩
    have h1 : dist z (f z) ≤ dist z p := hfmin z p hp
    have h2 : dist p (f z) ≤ dist p z + dist z (f z) := dist_triangle _ _ _
    rw [dist_comm z p] at h1
    linarith

end Schoenflies
