/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/FreshAccess.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Accessible
import FiniteAvalanches.Support.Schoenflies.AccessibleJoin
import FiniteAvalanches.Support.Schoenflies.SkeletonAccess

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





































































open Metric Set

namespace Schoenflies

variable {D K F N : Set Plane} {cells : Set (Set Plane)} {p v a z : Plane} {r s t ε : ℝ}

 





 
theorem convex_accessCone (p v : Plane) (s : ℝ) : Convex ℝ (accessCone p v s) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ α β hα hβ hαβ
  have hβ' : β = 1 - α := by linarith
  subst hβ'
  
  set A := ‖x - p‖ with hA
  set B := ‖y - p‖ with hB
  set Ix := inner ℝ v (x - p) with hIx
  set Iy := inner ℝ v (y - p) with hIy
  
  have hshift : α • x + (1 - α) • y - p = α • (x - p) + (1 - α) • (y - p) := by module
  have hnorm : ‖α • x + (1 - α) • y - p‖ ≤ α * A + (1 - α) * B := by
    rw [hshift]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα,
      abs_of_nonneg hβ]
  have hinner : inner ℝ v (α • x + (1 - α) • y - p) = α * Ix + (1 - α) * Iy := by
    rw [hshift, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  
  have hcomb : ∀ c d : ℝ, min c d ≤ α * c + (1 - α) * d ∧ α * c + (1 - α) * d ≤ max c d := by
    intro c d
    have h1 : α * min c d ≤ α * c := mul_le_mul_of_nonneg_left (min_le_left _ _) hα
    have h2 : (1 - α) * min c d ≤ (1 - α) * d := mul_le_mul_of_nonneg_left (min_le_right _ _) hβ
    have h3 : α * c ≤ α * max c d := mul_le_mul_of_nonneg_left (le_max_left _ _) hα
    have h4 : (1 - α) * d ≤ (1 - α) * max c d := mul_le_mul_of_nonneg_left (le_max_right _ _) hβ
    constructor <;> nlinarith
  refine ⟨hnorm.trans_lt (lt_of_le_of_lt (hcomb A B).2 (max_lt hx1 hy1)), ?_⟩
  
  rw [hinner]
  have hdef : min (Ix - A / 2) (Iy - B / 2) ≤ α * (Ix - A / 2) + (1 - α) * (Iy - B / 2) :=
    (hcomb (Ix - A / 2) (Iy - B / 2)).1
  have hminpos : 0 < min (Ix - A / 2) (Iy - B / 2) :=
    lt_min (by linarith) (by linarith)
  nlinarith

 
theorem isPreconnected_accessCone (p v : Plane) (s : ℝ) :
    IsPreconnected (accessCone p v s) := (convex_accessCone p v s).isPreconnected

 





 

private theorem half_lt_inner_self (hv : ‖v‖ = 1) : 1 / 2 < inner ℝ v v := by
  rw [real_inner_self_eq_norm_sq, hv]
  norm_num

 
private theorem dist_apex_axis (hv : ‖v‖ = 1) (ht : 0 < t) : dist p (p + t • v) = t := by
  have hshift : p + t • v - p = t • v := by module
  rw [dist_comm, dist_eq_norm, hshift, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one]

 
theorem mem_closure_accessCone (hv : ‖v‖ = 1) (hs : 0 < s) : p ∈ closure (accessCone p v s) := by
  refine Metric.mem_closure_iff.2 fun ε hε => ⟨p + (min ε s / 2) • v, ?_, ?_⟩
  · have hpos : 0 < min ε s / 2 := by positivity
    have hlt : min ε s / 2 < s := by
      have := min_le_right ε s
      linarith
    exact mem_accessCone hv (half_lt_inner_self hv) hpos hlt
  · have hpos : 0 < min ε s / 2 := by positivity
    rw [dist_apex_axis hv hpos]
    have := min_le_left ε s
    linarith

 


theorem polyAccessible_accessCone (hv : ‖v‖ = 1) (hs : 0 < s) (hsub : accessCone p v s ⊆ N) :
    PolyAccessible N p := by
  have hhalf : (0:ℝ) < s / 2 := by linarith
  have hmono : accessCone p v (s / 2) ⊆ accessCone p v s := accessCone_mono (by linarith)
  have hz : p + (s / 2) • v ∈ accessCone p v s :=
    mem_accessCone hv (half_lt_inner_self hv) hhalf (by linarith)
  refine PolyAccessible.of_openSegment (hsub hz) ?_
  exact ((openSegment_subset_accessCone hv (half_lt_inner_self hv) hhalf).trans hmono).trans hsub

 

 


theorem exists_accessCone_disjoint (h : StronglyAccessible D a) (hK : IsCompact K) (ha : a ∉ K) :
    ∃ (v : Plane) (s : ℝ), ‖v‖ = 1 ∧ 0 < s ∧ accessCone a v s ⊆ D ∧
      Disjoint (accessCone a v s) K := by
  obtain ⟨v, hv, r, hr, hcone⟩ := h.exists_cone
  obtain ⟨ρ, hρ, hball⟩ := Plane.exists_ball_subset_diff isOpen_univ hK ⟨mem_univ a, ha⟩
  refine ⟨v, min r ρ, hv, lt_min hr hρ, hcone _ (min_le_left _ _), ?_⟩
  refine Set.disjoint_left.2 fun x hx hxK => ?_
  exact (hball (accessCone_subset_ball_self (accessCone_mono (min_le_right r ρ) hx))).2 hxK

 

 


def CellsAbsorbIn (D K : Set Plane) (cells : Set (Set Plane)) : Prop :=
  ∀ N : Set Plane, N ⊆ D → IsPreconnected N → Disjoint N K →
    ∀ R ∈ cells, (N ∩ R).Nonempty → N ⊆ R

 
theorem CellsAbsorb.cellsAbsorbIn (h : CellsAbsorb K cells) : CellsAbsorbIn D K cells :=
  fun N _ hN hdisj R hR hmeet => h N hN hdisj R hR hmeet

 







theorem accessCone_subset_cell (habs : CellsAbsorb K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F)
    (hv : ‖v‖ = 1) (hs : 0 < s) (hD : accessCone a v s ⊆ D)
    (hdisj : Disjoint (accessCone a v s) K) :
    accessCone a v s ⊆ F := by
  
  obtain ⟨x, hx⟩ := accessCone_nonempty hv hs
  obtain ⟨R, hR, hxR⟩ := hcover x (hD hx) (Set.disjoint_left.1 hdisj hx)
  have hsub : accessCone a v s ⊆ R :=
    habs _ (isPreconnected_accessCone a v s) hdisj R hR ⟨x, hx, hxR⟩
  
  rw [← hunique R hR (closure_mono hsub (mem_closure_accessCone hv hs))]
  exact hsub

 
theorem accessCone_subset_cell_in (habs : CellsAbsorbIn D K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F)
    (hv : ‖v‖ = 1) (hs : 0 < s) (hD : accessCone a v s ⊆ D)
    (hdisj : Disjoint (accessCone a v s) K) :
    accessCone a v s ⊆ F := by
  obtain ⟨x, hx⟩ := accessCone_nonempty hv hs
  obtain ⟨R, hR, hxR⟩ := hcover x (hD hx) (Set.disjoint_left.1 hdisj hx)
  have hsub : accessCone a v s ⊆ R :=
    habs _ hD (isPreconnected_accessCone a v s) hdisj R hR ⟨x, hx, hxR⟩
  rw [← hunique R hR (closure_mono hsub (mem_closure_accessCone hv hs))]
  exact hsub

 

 









theorem polyAccessible_of_stronglyAccessible (h : StronglyAccessible D a) (hK : IsCompact K)
    (ha : a ∉ K) (habs : CellsAbsorb K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F) :
    PolyAccessible F a := by
  obtain ⟨v, s, hv, hs, hD, hdisj⟩ := exists_accessCone_disjoint h hK ha
  exact polyAccessible_accessCone hv hs
    (accessCone_subset_cell habs hcover hunique hv hs hD hdisj)

 

theorem polyAccessible_of_stronglyAccessible_in (h : StronglyAccessible D a)
    (hK : IsCompact K) (ha : a ∉ K) (habs : CellsAbsorbIn D K cells)
    (hcover : ∀ x ∈ D, x ∉ K → ∃ R ∈ cells, x ∈ R)
    (hunique : ∀ R ∈ cells, a ∈ closure R → R = F) :
    PolyAccessible F a := by
  obtain ⟨v, s, hv, hs, hD, hdisj⟩ := exists_accessCone_disjoint h hK ha
  exact polyAccessible_accessCone hv hs
    (accessCone_subset_cell_in habs hcover hunique hv hs hD hdisj)

end Schoenflies
