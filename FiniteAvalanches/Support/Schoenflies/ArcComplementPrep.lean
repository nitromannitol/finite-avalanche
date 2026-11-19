/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/ArcComplementPrep.lean.
-/
import FiniteAvalanches.Support.Schoenflies.PolygonalJordan
import FiniteAvalanches.Support.Schoenflies.ModelCurve
import FiniteAvalanches.Support.Schoenflies.SimpleArc
import FiniteAvalanches.Support.Schoenflies.SquareMover
import FiniteAvalanches.Support.Schoenflies.Graph.OuterFace
import FiniteAvalanches.Support.Schoenflies.UniformBound

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




























































open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

 






namespace Plane

variable {c z : Plane} {r : ℝ}

 
theorem supDist_eq_max (z c : Plane) : supDist z c = max |z 0 - c 0| |z 1 - c 1| := rfl

theorem mem_frontier_closedSquare :
    z ∈ frontier (closedSquare c r) ↔ max |z 0 - c 0| |z 1 - c 1| = r := by
  rw [frontier_closedSquare]
  exact Iff.rfl

 

theorem mem_frontier_closedSquare_of_fst (h0 : |z 0 - c 0| = r) (h1 : |z 1 - c 1| ≤ r) :
    z ∈ frontier (closedSquare c r) :=
  mem_frontier_closedSquare.2 (by rw [max_eq_left (h0 ▸ h1), h0])

 
theorem mem_frontier_closedSquare_of_snd (h1 : |z 1 - c 1| = r) (h0 : |z 0 - c 0| ≤ r) :
    z ∈ frontier (closedSquare c r) :=
  mem_frontier_closedSquare.2 (by rw [max_eq_right (h1 ▸ h0), h1])

 
def sqNE (c : Plane) (r : ℝ) : Plane := mk (c 0 + r) (c 1 + r)

 
def sqNW (c : Plane) (r : ℝ) : Plane := mk (c 0 - r) (c 1 + r)

 
def sqSW (c : Plane) (r : ℝ) : Plane := mk (c 0 - r) (c 1 - r)

 
def sqSE (c : Plane) (r : ℝ) : Plane := mk (c 0 + r) (c 1 - r)

@[simp] theorem sqNE_zero : sqNE c r 0 = c 0 + r := rfl
@[simp] theorem sqNE_one : sqNE c r 1 = c 1 + r := rfl
@[simp] theorem sqNW_zero : sqNW c r 0 = c 0 - r := rfl
@[simp] theorem sqNW_one : sqNW c r 1 = c 1 + r := rfl
@[simp] theorem sqSW_zero : sqSW c r 0 = c 0 - r := rfl
@[simp] theorem sqSW_one : sqSW c r 1 = c 1 - r := rfl
@[simp] theorem sqSE_zero : sqSE c r 0 = c 0 + r := rfl
@[simp] theorem sqSE_one : sqSE c r 1 = c 1 - r := rfl

 

theorem mem_segment_abs {a r x : ℝ} (hr : 0 ≤ r) :
    x ∈ segment ℝ (a - r) (a + r) ↔ |x - a| ≤ r := by
  rw [segment_eq_Icc (by linarith), mem_Icc, abs_le]
  constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem mem_segment_abs' {a r x : ℝ} (hr : 0 ≤ r) :
    x ∈ segment ℝ (a + r) (a - r) ↔ |x - a| ≤ r := by
  rw [segment_symm]; exact mem_segment_abs hr

 
theorem mem_seg_top (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqNE c r) (sqNW c r) ↔ z 1 = c 1 + r ∧ |z 0 - c 0| ≤ r := by
  rw [sqNE, sqNW, mem_segment_horiz, mem_segment_abs' hr]

 
theorem mem_seg_left (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqNW c r) (sqSW c r) ↔ z 0 = c 0 - r ∧ |z 1 - c 1| ≤ r := by
  rw [sqNW, sqSW, mem_segment_vert, mem_segment_abs' hr]

 
theorem mem_seg_bottom (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqSW c r) (sqSE c r) ↔ z 1 = c 1 - r ∧ |z 0 - c 0| ≤ r := by
  rw [sqSW, sqSE, mem_segment_horiz, mem_segment_abs hr]

 
theorem mem_seg_right (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqSE c r) (sqNE c r) ↔ z 0 = c 0 + r ∧ |z 1 - c 1| ≤ r := by
  rw [sqSE, sqNE, mem_segment_vert, mem_segment_abs hr]

 
theorem mem_frontier_closedSquare_iff_sides (hr : 0 ≤ r) :
    z ∈ frontier (closedSquare c r) ↔
      z ∈ segment ℝ (sqNE c r) (sqNW c r) ∨ z ∈ segment ℝ (sqNW c r) (sqSW c r) ∨
      z ∈ segment ℝ (sqSW c r) (sqSE c r) ∨ z ∈ segment ℝ (sqSE c r) (sqNE c r) := by
  rw [mem_seg_top hr, mem_seg_left hr, mem_seg_bottom hr, mem_seg_right hr,
    mem_frontier_closedSquare]
  constructor
  · intro h
    have h0 : |z 0 - c 0| ≤ r := h ▸ le_max_left _ _
    have h1 : |z 1 - c 1| ≤ r := h ▸ le_max_right _ _
    rcases max_choice |z 0 - c 0| |z 1 - c 1| with hm | hm
    · rcases (abs_eq hr).1 (hm ▸ h) with h' | h'
      · exact Or.inr (Or.inr (Or.inr ⟨by linarith, h1⟩))
      · exact Or.inr (Or.inl ⟨by linarith, h1⟩)
    · rcases (abs_eq hr).1 (hm ▸ h) with h' | h'
      · exact Or.inl ⟨by linarith, h0⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h0⟩))
  · rintro (⟨h1, h0⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h0, h1⟩)
    · have hz : |z 1 - c 1| = r := by rw [h1, add_sub_cancel_left, abs_of_nonneg hr]
      rw [hz, max_eq_right h0]
    · have hz : |z 0 - c 0| = r := by
        rw [h0, sub_sub_cancel_left, abs_neg, abs_of_nonneg hr]
      rw [hz, max_eq_left h1]
    · have hz : |z 1 - c 1| = r := by
        rw [h1, sub_sub_cancel_left, abs_neg, abs_of_nonneg hr]
      rw [hz, max_eq_right h0]
    · have hz : |z 0 - c 0| = r := by rw [h0, add_sub_cancel_left, abs_of_nonneg hr]
      rw [hz, max_eq_left h1]

end Plane

open Plane

 






variable {c : Plane} {r : ℝ}

 


def squarePolygon (c : Plane) {r : ℝ} (hr : 0 < r) : ClosedPolygon 1 where
  vertex := ![sqNE c r, sqNW c r, sqSW c r, sqSE c r]
  vertex_inj := by
    
    have hfst : ∀ p q : Plane, p 0 ≠ q 0 → p ≠ q := fun _ _ h e => h (by rw [e])
    have hsnd : ∀ p q : Plane, p 1 ≠ q 1 → p ≠ q := fun _ _ h e => h (by rw [e])
    have h01 : sqNE c r ≠ sqNW c r := hfst _ _ (by simp; linarith)
    have h02 : sqNE c r ≠ sqSW c r := hfst _ _ (by simp; linarith)
    have h03 : sqNE c r ≠ sqSE c r := hsnd _ _ (by simp; linarith)
    have h12 : sqNW c r ≠ sqSW c r := hsnd _ _ (by simp; linarith)
    have h13 : sqNW c r ≠ sqSE c r := hfst _ _ (by simp; linarith)
    have h23 : sqSW c r ≠ sqSE c r := hfst _ _ (by simp; linarith)
    intro i j hij
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij h03
    · exact absurd hij.symm h01
    · rfl
    · exact absurd hij h12
    · exact absurd hij h13
    · exact absurd hij.symm h02
    · exact absurd hij.symm h12
    · rfl
    · exact absurd hij h23
    · exact absurd hij.symm h03
    · exact absurd hij.symm h13
    · exact absurd hij.symm h23
    · rfl
  edges_meet := by
    
    have mTL : segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqNW c r) (sqSW c r)
        ⊆ {sqNW c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqNE_zero, sqNE_one, sqNW_zero,
          sqNW_one, sqSW_zero, sqSW_one] at h; nlinarith)
    have mLB : segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqSW c r) (sqSE c r)
        ⊆ {sqSW c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqNW_zero, sqNW_one, sqSW_zero,
          sqSW_one, sqSE_zero, sqSE_one] at h; nlinarith)
    have mBR : segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqSE c r) (sqNE c r)
        ⊆ {sqSE c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqSW_zero, sqSW_one, sqSE_zero,
          sqSE_one, sqNE_zero, sqNE_one] at h; nlinarith)
    have mRT : segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqNE c r) (sqNW c r)
        ⊆ {sqNE c r} :=
      segment_inter_shared (by
        intro h; simp only [Plane.det, Plane.sub_apply, sqSE_zero, sqSE_one, sqNE_zero,
          sqNE_one, sqNW_zero, sqNW_one] at h; nlinarith)
    
    have mTB : ∀ z, z ∈ segment ℝ (sqNE c r) (sqNW c r) →
        z ∈ segment ℝ (sqSW c r) (sqSE c r) → False := by
      intro z h1 h2
      rw [mem_seg_top hr.le] at h1
      rw [mem_seg_bottom hr.le] at h2
      have := h1.1.symm.trans h2.1
      linarith
    have mLR : ∀ z, z ∈ segment ℝ (sqNW c r) (sqSW c r) →
        z ∈ segment ℝ (sqSE c r) (sqNE c r) → False := by
      intro z h1 h2
      rw [mem_seg_left hr.le] at h1
      rw [mem_seg_right hr.le] at h2
      have := h1.1.symm.trans h2.1
      linarith
    intro i j hij
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl | rfl
    · exact absurd rfl hij
    · change segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqNW c r) (sqSW c r) ⊆
        {sqNE c r, sqNW c r}
      exact subset_trans mTL (by simp)
    · change segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqSW c r) (sqSE c r) ⊆
        {sqNE c r, sqNW c r}
      exact fun z hz => absurd hz.2 (fun h => mTB z hz.1 h)
    · change segment ℝ (sqNE c r) (sqNW c r) ∩ segment ℝ (sqSE c r) (sqNE c r) ⊆
        {sqNE c r, sqNW c r}
      rw [Set.inter_comm]
      exact subset_trans mRT (by simp)
    · change segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqNE c r) (sqNW c r) ⊆
        {sqNW c r, sqSW c r}
      rw [Set.inter_comm]
      exact subset_trans mTL (by simp)
    · exact absurd rfl hij
    · change segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqSW c r) (sqSE c r) ⊆
        {sqNW c r, sqSW c r}
      exact subset_trans mLB (by simp)
    · change segment ℝ (sqNW c r) (sqSW c r) ∩ segment ℝ (sqSE c r) (sqNE c r) ⊆
        {sqNW c r, sqSW c r}
      exact fun z hz => absurd hz.2 (fun h => mLR z hz.1 h)
    · change segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqNE c r) (sqNW c r) ⊆
        {sqSW c r, sqSE c r}
      exact fun z hz => absurd hz.1 (fun h => mTB z hz.2 h)
    · change segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqNW c r) (sqSW c r) ⊆
        {sqSW c r, sqSE c r}
      rw [Set.inter_comm]
      exact subset_trans mLB (by simp)
    · exact absurd rfl hij
    · change segment ℝ (sqSW c r) (sqSE c r) ∩ segment ℝ (sqSE c r) (sqNE c r) ⊆
        {sqSW c r, sqSE c r}
      exact subset_trans mBR (by simp)
    · change segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqNE c r) (sqNW c r) ⊆
        {sqSE c r, sqNE c r}
      exact subset_trans mRT (by simp)
    · change segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqNW c r) (sqSW c r) ⊆
        {sqSE c r, sqNE c r}
      exact fun z hz => absurd hz.1 (fun h => mLR z hz.2 h)
    · change segment ℝ (sqSE c r) (sqNE c r) ∩ segment ℝ (sqSW c r) (sqSE c r) ⊆
        {sqSE c r, sqNE c r}
      rw [Set.inter_comm]
      exact subset_trans mBR (by simp)
    · exact absurd rfl hij
  corner := by
    intro i
    
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl
    · change det (sqSE c r - sqNE c r) (sqNW c r - sqNE c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqNE_zero, sqNE_one, sqNW_zero, sqNW_one,
        sqSE_zero, sqSE_one] at h
      nlinarith
    · change det (sqNE c r - sqNW c r) (sqSW c r - sqNW c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqNE_zero, sqNE_one, sqNW_zero, sqNW_one,
        sqSW_zero, sqSW_one] at h
      nlinarith
    · change det (sqNW c r - sqSW c r) (sqSE c r - sqSW c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqNW_zero, sqNW_one, sqSW_zero, sqSW_one,
        sqSE_zero, sqSE_one] at h
      nlinarith
    · change det (sqSW c r - sqSE c r) (sqNE c r - sqSE c r) ≠ 0
      intro h
      simp only [Plane.det, Plane.sub_apply, sqSW_zero, sqSW_one, sqSE_zero, sqSE_one,
        sqNE_zero, sqNE_one] at h
      nlinarith

@[simp] theorem squarePolygon_vertex_zero (hr : 0 < r) :
    (squarePolygon c hr).vertex 0 = sqNE c r := rfl

@[simp] theorem squarePolygon_vertex_one (hr : 0 < r) :
    (squarePolygon c hr).vertex 1 = sqNW c r := rfl

@[simp] theorem squarePolygon_vertex_two (hr : 0 < r) :
    (squarePolygon c hr).vertex 2 = sqSW c r := rfl

@[simp] theorem squarePolygon_vertex_three (hr : 0 < r) :
    (squarePolygon c hr).vertex 3 = sqSE c r := rfl

theorem edge_squarePolygon_zero (hr : 0 < r) :
    (squarePolygon c hr).edge 0 = segment ℝ (sqNE c r) (sqNW c r) := rfl

theorem edge_squarePolygon_one (hr : 0 < r) :
    (squarePolygon c hr).edge 1 = segment ℝ (sqNW c r) (sqSW c r) := rfl

theorem edge_squarePolygon_two (hr : 0 < r) :
    (squarePolygon c hr).edge 2 = segment ℝ (sqSW c r) (sqSE c r) := rfl

theorem edge_squarePolygon_three (hr : 0 < r) :
    (squarePolygon c hr).edge 3 = segment ℝ (sqSE c r) (sqNE c r) := rfl

 


theorem carrier_squarePolygon (hr : 0 < r) :
    (squarePolygon c hr).carrier = frontier (closedSquare c r) := by
  ext z
  rw [Plane.mem_frontier_closedSquare_iff_sides hr.le]
  simp only [ClosedPolygon.carrier, mem_iUnion]
  constructor
  · rintro ⟨i, hz⟩
    have hi : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    rcases hi i with rfl | rfl | rfl | rfl
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))
  · rintro (h | h | h | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]

 





theorem isJordanCurve_frontier_closedSquare (c : Plane) (hr : 0 < r) :
    IsJordanCurve (frontier (closedSquare c r)) :=
  carrier_squarePolygon hr ▸ (squarePolygon c hr).isJordanCurve_carrier

theorem isPolygonal_frontier_closedSquare (c : Plane) (hr : 0 < r) :
    IsPolygonal (frontier (closedSquare c r)) :=
  carrier_squarePolygon hr ▸ (squarePolygon c hr).isPolygonal_carrier

theorem isSeparating_frontier_closedSquare (c : Plane) (hr : 0 < r) :
    IsSeparating (frontier (closedSquare c r)) :=
  carrier_squarePolygon hr ▸ (squarePolygon c hr).isSeparating_carrier

namespace Plane

 

theorem isBounded_closedSquare (c : Plane) (r : ℝ) :
    Bornology.IsBounded (closedSquare c r) := by
  refine (Metric.isBounded_closedBall (x := c) (r := Real.sqrt 2 * r)).subset fun z hz => ?_
  have hsup : supNorm (z - c) ≤ r := hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact le_trans (norm_le_sqrt_two_mul_supNorm _)
    (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))

 

theorem beyondSquare_subset_compl_closedSquare (c : Plane) (r : ℝ) :
    beyondSquare (r + supNorm c) ⊆ (closedSquare c r)ᶜ := by
  intro x hx
  rw [beyondSquare_eq_compl] at hx
  have hx' : ¬ supNorm x ≤ r + supNorm c := by
    simpa [closedSquare] using hx
  intro hmem
  have hmem' : supDist x c ≤ r := hmem
  
  have h1 : supNorm x ≤ supDist x c + supNorm c := by simpa using supDist_triangle x c 0
  exact hx' (by linarith)

theorem not_isBounded_compl_closedSquare (c : Plane) (r : ℝ) :
    ¬ Bornology.IsBounded (closedSquare c r)ᶜ := fun h =>
  Graph.not_isBounded_beyondSquare (r + supNorm c)
    (h.subset (beyondSquare_subset_compl_closedSquare c r))

 
theorem mem_compl_closedSquare_iff (c : Plane) (r : ℝ) (x : Plane) :
    x ∈ (closedSquare c r)ᶜ ↔ x - c ∈ beyondSquare r := by
  rw [beyondSquare_eq_compl]
  simp only [mem_compl_iff, closedSquare, mem_setOf_eq, supDist_zero]
  exact Iff.rfl

theorem compl_closedSquare_eq_image (c : Plane) (r : ℝ) :
    (closedSquare c r)ᶜ = (fun x => x + c) '' beyondSquare r := by
  ext z
  rw [mem_compl_closedSquare_iff]
  constructor
  · intro hz
    exact ⟨z - c, hz, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    simpa using hw

 
theorem isConnected_compl_closedSquare (c : Plane) (r : ℝ) :
    IsConnected (closedSquare c r)ᶜ := by
  rw [compl_closedSquare_eq_image]
  exact (isConnected_beyondSquare r).image _ (by fun_prop)

 
theorem compl_frontier_closedSquare (c : Plane) (r : ℝ) :
    (frontier (closedSquare c r))ᶜ = openSquare c r ∪ (closedSquare c r)ᶜ := by
  ext z
  rw [frontier_closedSquare]
  simp only [mem_compl_iff, mem_setOf_eq, mem_union, openSquare, closedSquare, not_le]
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rintro (h | h)
    · exact ne_of_lt h
    · exact ne_of_gt h

 



private theorem openSquare_subset_closedSquare' (c : Plane) (r : ℝ) :
    openSquare c r ⊆ closedSquare c r :=
  fun z hz => show supDist z c ≤ r from le_of_lt hz

 

theorem frontier_openSquare_subset (c : Plane) (r : ℝ) :
    frontier (openSquare c r) ⊆ frontier (closedSquare c r) := by
  rw [(isOpen_openSquare c r).frontier_eq, frontier_closedSquare]
  rintro z ⟨hz1, hz2⟩
  have h1 : supDist z c ≤ r :=
    (isClosed_closedSquare c r).closure_subset_iff.2 (openSquare_subset_closedSquare' c r) hz1
  exact le_antisymm h1 (not_lt.1 hz2)

end Plane

 
theorem inside_frontier_closedSquare (c : Plane) (r : ℝ) :
    inside (frontier (closedSquare c r)) = openSquare c r := by
  have hcompl := Plane.compl_frontier_closedSquare c r
  
  have hcomp₁ : ∀ x ∈ openSquare c r,
      connectedComponentIn (frontier (closedSquare c r))ᶜ x = openSquare c r := by
    intro x hx
    refine Plane.connectedComponentIn_eq_of_frontier_disjoint (Plane.isOpen_openSquare c r)
      (Plane.convex_openSquare c r).isPreconnected ?_ ?_ hx
    · rw [hcompl]; exact subset_union_left
    · rw [eq_empty_iff_forall_notMem]
      exact fun z hz => hz.2 (Plane.frontier_openSquare_subset c r hz.1)
  have hcomp₂ : ∀ x ∈ (closedSquare c r)ᶜ,
      connectedComponentIn (frontier (closedSquare c r))ᶜ x = (closedSquare c r)ᶜ := by
    intro x hx
    refine Plane.connectedComponentIn_eq_of_frontier_disjoint
      (Plane.isClosed_closedSquare c r).isOpen_compl
      (Plane.isConnected_compl_closedSquare c r).isPreconnected ?_ ?_ hx
    · rw [hcompl]; exact subset_union_right
    · rw [eq_empty_iff_forall_notMem]
      intro z hz
      rw [frontier_compl] at hz
      exact hz.2 hz.1
  ext x
  constructor
  · rintro ⟨hx, hb⟩
    have hx : x ∈ openSquare c r ∪ (closedSquare c r)ᶜ := by
      rw [← hcompl]; exact hx
    rcases hx with hx | hx
    · exact hx
    · rw [hcomp₂ x hx] at hb
      exact absurd hb (Plane.not_isBounded_compl_closedSquare c r)
  · intro hx
    have hxc : x ∈ (frontier (closedSquare c r))ᶜ := by rw [hcompl]; exact Or.inl hx
    refine ⟨hxc, ?_⟩
    rw [hcomp₁ x hx]
    exact (Plane.isBounded_closedSquare c r).subset (Plane.openSquare_subset_closedSquare' c r)

 
theorem outside_frontier_closedSquare (c : Plane) (r : ℝ) :
    outside (frontier (closedSquare c r)) = (closedSquare c r)ᶜ := by
  have hin := inside_frontier_closedSquare c r
  have hcompl := Plane.compl_frontier_closedSquare c r
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (frontier (closedSquare c r))ᶜ := hx.1
    rw [hcompl] at hx'
    rcases hx' with h | h
    · exact absurd (hin.symm.subset h) (Set.disjoint_right.1 disjoint_inside_outside hx)
    · exact h
  · intro hx
    have hx' : x ∈ (frontier (closedSquare c r))ᶜ := by rw [hcompl]; exact Or.inr hx
    have hmem : x ∈ inside (frontier (closedSquare c r)) ∪
        outside (frontier (closedSquare c r)) := by
      rw [inside_union_outside]; exact hx'
    rcases hmem with h | h
    · exact absurd (show supDist x c ≤ r from le_of_lt (hin.subset h)) hx
    · exact h


 




















 

def squarePieces (c : Plane) (r : ℝ) : List Piece :=
  [(sqNE c r, sqNW c r), (sqNW c r, sqSW c r), (sqSW c r, sqSE c r), (sqSE c r, sqNE c r)]

theorem cover_squarePieces (c : Plane) (hr : 0 ≤ r) :
    cover (squarePieces c r) = frontier (closedSquare c r) := by
  ext z
  rw [Plane.mem_frontier_closedSquare_iff_sides hr]
  simp only [squarePieces, cover_cons, cover_nil, Piece.seg, mem_union, mem_empty_iff_false,
    or_false]

theorem squarePieces_nondeg (c : Plane) (hr : 0 < r) :
    ∀ P ∈ squarePieces c r, P.Nondeg := by
  have hfst : ∀ p q : Plane, p 0 ≠ q 0 → p ≠ q := fun _ _ h e => h (by rw [e])
  have hsnd : ∀ p q : Plane, p 1 ≠ q 1 → p ≠ q := fun _ _ h e => h (by rw [e])
  intro P hP
  simp only [squarePieces, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact hfst _ _ (by simp; linarith)
  · exact hsnd _ _ (by simp; linarith)
  · exact hfst _ _ (by simp; linarith)
  · exact hsnd _ _ (by simp; linarith)

 

 
theorem mem_segment_of_bounds {u v y : ℝ} (h : u ≤ y ∧ y ≤ v ∨ v ≤ y ∧ y ≤ u) :
    y ∈ segment ℝ u v := by
  rw [segment_eq_uIcc, Set.mem_uIcc]
  exact h

 

theorem meetOf_vert_horiz {x₀ y₀ u v s t : ℝ}
    (hy : y₀ ∈ segment ℝ u v) (hx : x₀ ∈ segment ℝ s t) :
    meetOf (Plane.mk x₀ u, Plane.mk x₀ v) (Plane.mk s y₀, Plane.mk t y₀) =
      {Plane.mk x₀ y₀} := by
  ext z
  simp only [meetOf, Piece.seg, mem_inter_iff, mem_singleton_iff]
  rw [mem_segment_vert, mem_segment_horiz]
  constructor
  · rintro ⟨⟨hz0, -⟩, ⟨hz1, -⟩⟩
    ext i
    fin_cases i
    · simpa using hz0
    · simpa using hz1
  · rintro rfl
    exact ⟨⟨rfl, hy⟩, ⟨rfl, hx⟩⟩

 
theorem meetOf_horiz_vert {x₀ y₀ u v s t : ℝ}
    (hx : x₀ ∈ segment ℝ s t) (hy : y₀ ∈ segment ℝ u v) :
    meetOf (Plane.mk s y₀, Plane.mk t y₀) (Plane.mk x₀ u, Plane.mk x₀ v) =
      {Plane.mk x₀ y₀} := by
  rw [meetOf_comm]
  exact meetOf_vert_horiz hy hx

 






theorem exists_two_meets {c₁ c₂ : Plane} {r : ℝ} (hr : 0 < r)
    (hd : Plane.supDist c₁ c₂ < r) :
    ∃ p q : Plane, p ≠ q ∧
      (∃ P ∈ squarePieces c₁ r, ∃ Q ∈ squarePieces c₂ r, meetOf P Q = {p}) ∧
      (∃ P ∈ squarePieces c₁ r, ∃ Q ∈ squarePieces c₂ r, meetOf P Q = {q}) := by
  rw [Plane.supDist_eq_max, max_lt_iff, abs_lt, abs_lt] at hd
  obtain ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩ := hd
  
  
  have hfst : ∀ (x y u v : ℝ), x ≠ y → Plane.mk x u ≠ Plane.mk y v := by
    intro x y u v hxy hcon
    exact hxy (by simpa using congrArg (fun p : Plane => p 0) hcon)
  rcases le_or_gt (c₁ 0) (c₂ 0) with hA | hA <;> rcases le_or_gt (c₁ 1) (c₂ 1) with hB | hB
  · 
    
    refine ⟨Plane.mk (c₁ 0 + r) (c₂ 1 - r), Plane.mk (c₂ 0 - r) (c₁ 1 + r),
      hfst _ _ _ _ (by intro h; linarith), ?_, ?_⟩
    · refine ⟨(Plane.mk (c₁ 0 + r) (c₁ 1 - r), Plane.mk (c₁ 0 + r) (c₁ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 - r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₂ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_vert_horiz (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
    · refine ⟨(Plane.mk (c₁ 0 + r) (c₁ 1 + r), Plane.mk (c₁ 0 - r) (c₁ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 - r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₂ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_horiz_vert (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
  · 
    refine ⟨Plane.mk (c₁ 0 + r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₁ 1 - r),
      hfst _ _ _ _ (by intro h; linarith), ?_, ?_⟩
    · refine ⟨(Plane.mk (c₁ 0 + r) (c₁ 1 - r), Plane.mk (c₁ 0 + r) (c₁ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 + r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₂ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_vert_horiz (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
    · refine ⟨(Plane.mk (c₁ 0 - r) (c₁ 1 - r), Plane.mk (c₁ 0 + r) (c₁ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 - r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₂ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_horiz_vert (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
  · 
    refine ⟨Plane.mk (c₁ 0 - r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₁ 1 + r),
      hfst _ _ _ _ (by intro h; linarith), ?_, ?_⟩
    · refine ⟨(Plane.mk (c₁ 0 - r) (c₁ 1 + r), Plane.mk (c₁ 0 - r) (c₁ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 - r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₂ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_vert_horiz (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
    · refine ⟨(Plane.mk (c₁ 0 + r) (c₁ 1 + r), Plane.mk (c₁ 0 - r) (c₁ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 + r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₂ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_horiz_vert (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
  · 
    refine ⟨Plane.mk (c₁ 0 - r) (c₂ 1 + r), Plane.mk (c₂ 0 + r) (c₁ 1 - r),
      hfst _ _ _ _ (by intro h; linarith), ?_, ?_⟩
    · refine ⟨(Plane.mk (c₁ 0 - r) (c₁ 1 + r), Plane.mk (c₁ 0 - r) (c₁ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 + r) (c₂ 1 + r), Plane.mk (c₂ 0 - r) (c₂ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_vert_horiz (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inr ⟨by linarith, by linarith⟩))
    · refine ⟨(Plane.mk (c₁ 0 - r) (c₁ 1 - r), Plane.mk (c₁ 0 + r) (c₁ 1 - r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE],
        (Plane.mk (c₂ 0 + r) (c₂ 1 - r), Plane.mk (c₂ 0 + r) (c₂ 1 + r)), by
        simp [squarePieces, Plane.sqNE, Plane.sqNW, Plane.sqSW, Plane.sqSE], ?_⟩
      exact meetOf_horiz_vert (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))
        (mem_segment_of_bounds (Or.inl ⟨by linarith, by linarith⟩))

 








 

theorem overlayGraph_mem_vertexSet_of_meetOf_eq_singleton {pieces : List Piece}
    {points : List Plane} (hnd : ∀ P ∈ pieces, P.Nondeg) (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ pieces) (hQ : Q ∈ pieces) {p : Plane}
    (hmeet : meetOf P Q = {p}) : p ∈ V(overlayGraph pieces points) := by
  have hp : p ∈ meetOf P Q := by rw [hmeet]; exact rfl
  
  have hPQ : P ≠ Q := by
    rintro rfl
    have hseg : P.seg = {p} := by
      rw [← hmeet]
      exact (Set.inter_self _).symm
    have h1 : P.1 ∈ P.seg := left_mem_segment ℝ _ _
    have h2 : P.2 ∈ P.seg := right_mem_segment ℝ _ _
    rw [hseg, mem_singleton_iff] at h1 h2
    exact hnd P hP (h1.trans h2.symm)
  obtain ⟨u, v, huv, hu, -⟩ := hMeets P hP Q hQ hPQ ⟨p, hp⟩
  have hup : u = p := by
    have hmem : u ∈ segment ℝ u v := left_mem_segment ℝ _ _
    rw [← huv, hmeet, mem_singleton_iff] at hmem
    exact hmem
  exact overlayGraph_mem_vertexSet_of_mem_cover hnd (hup ▸ hu)
    (Set.mem_iUnion₂.2 ⟨P, hP, hp.1⟩)

 
theorem mem_frontier_of_meetOf_eq_singleton {c₁ c₂ : Plane} {r : ℝ} (hr : 0 ≤ r)
    {P Q : Piece} {p : Plane} (hP : P ∈ squarePieces c₁ r) (hQ : Q ∈ squarePieces c₂ r)
    (h : meetOf P Q = {p}) :
    p ∈ frontier (closedSquare c₁ r) ∧ p ∈ frontier (closedSquare c₂ r) := by
  have hp : p ∈ meetOf P Q := by rw [h]; exact rfl
  constructor
  · rw [← cover_squarePieces c₁ hr]
    exact Set.mem_iUnion₂.2 ⟨P, hP, hp.1⟩
  · rw [← cover_squarePieces c₂ hr]
    exact Set.mem_iUnion₂.2 ⟨Q, hQ, hp.2⟩

 
theorem exists_two_frontier_inter {c₁ c₂ : Plane} {r : ℝ} (hr : 0 < r)
    (hd : Plane.supDist c₁ c₂ < r) :
    ∃ p q : Plane, p ≠ q ∧
      p ∈ frontier (closedSquare c₁ r) ∩ frontier (closedSquare c₂ r) ∧
      q ∈ frontier (closedSquare c₁ r) ∩ frontier (closedSquare c₂ r) := by
  obtain ⟨p, q, hpq, ⟨P, hP, Q, hQ, hp⟩, ⟨P', hP', Q', hQ', hq⟩⟩ := exists_two_meets hr hd
  exact ⟨p, q, hpq, mem_frontier_of_meetOf_eq_singleton hr.le hP hQ hp,
    mem_frontier_of_meetOf_eq_singleton hr.le hP' hQ' hq⟩

 








theorem exists_two_common_vertices {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hMeets : MeetsAreCut pieces points)
    {c₁ c₂ : Plane} {r : ℝ} (hr : 0 < r) (hd : Plane.supDist c₁ c₂ < r)
    (h₁ : ∀ P ∈ squarePieces c₁ r, P ∈ pieces) (h₂ : ∀ P ∈ squarePieces c₂ r, P ∈ pieces) :
    ∃ p q : Plane, p ≠ q ∧ p ∈ V(overlayGraph pieces points) ∧
      q ∈ V(overlayGraph pieces points) := by
  obtain ⟨p, q, hpq, ⟨P, hP, Q, hQ, hp⟩, ⟨P', hP', Q', hQ', hq⟩⟩ := exists_two_meets hr hd
  exact ⟨p, q, hpq,
    overlayGraph_mem_vertexSet_of_meetOf_eq_singleton hnd hMeets (h₁ P hP) (h₂ Q hQ) hp,
    overlayGraph_mem_vertexSet_of_meetOf_eq_singleton hnd hMeets (h₁ P' hP') (h₂ Q' hQ') hq⟩

 







 
theorem subdivide_mono : ∀ (points : List Plane) {l pieces : List Piece},
    (∀ P ∈ l, P ∈ pieces) → ∀ Q ∈ subdivide l points, Q ∈ subdivide pieces points := by
  intro points
  induction points with
  | nil => intro l pieces h Q hQ; exact h Q hQ
  | cons p ps ih =>
    intro l pieces h Q hQ
    rw [subdivide_cons] at hQ ⊢
    refine ih ?_ Q hQ
    intro R hR
    simp only [splitAllAt, List.mem_flatMap] at hR ⊢
    obtain ⟨P, hP, hRP⟩ := hR
    exact ⟨P, h P hP, hRP⟩

 



theorem exists_overlayPiece_end_subset {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) {x : Plane} (hxp : x ∈ points)
    {P₀ : Piece} (hP₀ : P₀ ∈ pieces) (hx : x ∈ P₀.seg) :
    ∃ Q ∈ overlayPieces pieces points, (x = Q.1 ∨ x = Q.2) ∧ Q.seg ⊆ P₀.seg := by
  
  have hcov : x ∈ cover (subdivide [P₀] points) := by
    rw [subdivide_cover, cover_cons, cover_nil, union_empty]
    exact hx
  simp only [cover, mem_iUnion, exists_prop] at hcov
  obtain ⟨Q, hQ, hxQ⟩ := hcov
  have hQpieces : Q ∈ subdivide pieces points :=
    subdivide_mono points (by simpa using hP₀) Q hQ
  have hQsub : Q.seg ⊆ P₀.seg := by
    obtain ⟨R, hR, hseg, -⟩ := subdivide_subset [P₀] points Q hQ
    rw [List.mem_singleton] at hR
    exact hR ▸ hseg
  have hint : x ∉ Q.interior := subdivide_avoids points hnd x hxp Q hQpieces
  have hend : x = Q.1 ∨ x = Q.2 := by
    by_contra hcon
    push Not at hcon
    exact hint (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxQ)
  refine ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQpieces, rfl⟩, ?_, ?_⟩
  · exact (orientPiece_ends Q x).2 hend
  · rw [orientPiece_seg]
    exact hQsub

 


theorem exists_two_cut_points {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hMeets : MeetsAreCut pieces points)
    {c₁ c₂ : Plane} {r : ℝ} (hr : 0 < r) (hd : Plane.supDist c₁ c₂ < r)
    (h₁ : ∀ P ∈ squarePieces c₁ r, P ∈ pieces) (h₂ : ∀ P ∈ squarePieces c₂ r, P ∈ pieces) :
    ∃ p q : Plane, p ≠ q ∧ p ∈ points ∧ q ∈ points ∧
      p ∈ frontier (closedSquare c₁ r) ∩ frontier (closedSquare c₂ r) ∧
      q ∈ frontier (closedSquare c₁ r) ∩ frontier (closedSquare c₂ r) := by
  
  have key : ∀ {P Q : Piece} {z : Plane}, P ∈ pieces → Q ∈ pieces → meetOf P Q = {z} →
      z ∈ points := by
    intro P Q z hP hQ hmeet
    have hp : z ∈ meetOf P Q := by rw [hmeet]; exact rfl
    have hPQ : P ≠ Q := by
      rintro rfl
      have hseg : P.seg = {z} := by rw [← hmeet]; exact (Set.inter_self _).symm
      have h1 : P.1 ∈ P.seg := left_mem_segment ℝ _ _
      have h2 : P.2 ∈ P.seg := right_mem_segment ℝ _ _
      rw [hseg, mem_singleton_iff] at h1 h2
      exact hnd P hP (h1.trans h2.symm)
    obtain ⟨u, v, huv, hu, -⟩ := hMeets P hP Q hQ hPQ ⟨z, hp⟩
    have hmem : u ∈ segment ℝ u v := left_mem_segment ℝ _ _
    rw [← huv, hmeet, mem_singleton_iff] at hmem
    exact hmem ▸ hu
  obtain ⟨p, q, hpq, ⟨P, hP, Q, hQ, hp⟩, ⟨P', hP', Q', hQ', hq⟩⟩ := exists_two_meets hr hd
  exact ⟨p, q, hpq, key (h₁ P hP) (h₂ Q hQ) hp, key (h₁ P' hP') (h₂ Q' hQ') hq,
    mem_frontier_of_meetOf_eq_singleton hr.le hP hQ hp,
    mem_frontier_of_meetOf_eq_singleton hr.le hP' hQ' hq⟩

 










 
noncomputable def sample (n i : ℕ) : ℝ := (i : ℝ) / n

@[simp] theorem sample_zero (n : ℕ) : sample n 0 = 0 := by simp [sample]

theorem sample_last {n : ℕ} (hn : 0 < n) : sample n n = 1 := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [sample, div_self hne]

theorem sample_nonneg (n i : ℕ) : 0 ≤ sample n i :=
  div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg n)

theorem sample_mono {n i j : ℕ} (h : i ≤ j) : sample n i ≤ sample n j := by
  have hij : (i : ℝ) ≤ j := by exact_mod_cast h
  have key : sample n j - sample n i = ((j : ℝ) - i) / n := by simp only [sample]; ring
  have hpos : 0 ≤ ((j : ℝ) - i) / n := div_nonneg (by linarith) (Nat.cast_nonneg n)
  linarith [key, hpos]

theorem sample_strictMono {n i j : ℕ} (hn : 0 < n) (h : i < j) :
    sample n i < sample n j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hij : (i : ℝ) < j := by exact_mod_cast h
  have key : sample n j - sample n i = ((j : ℝ) - i) / n := by simp only [sample]; ring
  have hpos : 0 < ((j : ℝ) - i) / n := div_pos (by linarith) hnR
  linarith [key, hpos]

theorem sample_le_one {n i : ℕ} (h : i ≤ n) : sample n i ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sample, Nat.le_zero.1 h]
  · rw [← sample_last hn]; exact sample_mono h

theorem sample_mem_I {n i : ℕ} (h : i ≤ n) : sample n i ∈ I :=
  ⟨sample_nonneg n i, sample_le_one h⟩

 
theorem sample_succ_sub (n i : ℕ) :
    sample n (i + 1) - sample n i = 1 / n := by
  simp only [sample, Nat.cast_add, Nat.cast_one]
  rw [div_sub_div_same]
  norm_num

 

theorem sample_mul {k m i : ℕ} (hm : 0 < m) : sample (k * m) (i * m) = sample k i := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  simp only [sample, Nat.cast_mul]
  rw [mul_comm (i : ℝ) (m : ℝ), mul_comm (k : ℝ) (m : ℝ), mul_div_mul_left _ _ hmR]

theorem Icc_sample_subset_I {n i : ℕ} (h : i + 1 ≤ n) :
    Icc (sample n i) (sample n (i + 1)) ⊆ I := fun _ hs =>
  ⟨le_trans (sample_nonneg n i) hs.1, le_trans hs.2 (sample_le_one h)⟩

 
theorem exists_mem_Icc_sample {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : s ∈ I) :
    ∃ i < n, s ∈ Icc (sample n i) (sample n (i + 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set j : ℕ := ⌊s * n⌋₊ with hj
  have hs0 : 0 ≤ s := hs.1
  have hjle : (j : ℝ) ≤ s * n := Nat.floor_le (mul_nonneg hs0 hnR.le)
  have hjlt : s * n < j + 1 := Nat.lt_floor_add_one _
  by_cases hjn : j < n
  · refine ⟨j, hjn, ?_, ?_⟩
    · rw [sample, div_le_iff₀ hnR]; exact hjle
    · rw [sample, le_div_iff₀ hnR]; push_cast; linarith
  · 
    have hjn' : n ≤ j := Nat.not_lt.1 hjn
    have hsn : s * n ≤ n := by nlinarith [hs.2, hnR.le]
    have hjeq : (j : ℝ) ≤ n := le_trans hjle hsn
    have hjn'' : j = n := le_antisymm (by exact_mod_cast hjeq) hjn'
    have hge : (n : ℝ) ≤ s * n := hjn'' ▸ hjle
    have hs1 : s = 1 := le_antisymm hs.2 (by nlinarith [hge, hnR])
    refine ⟨n - 1, by omega, ?_, ?_⟩
    · rw [hs1]; exact sample_le_one (by omega)
    · rw [show n - 1 + 1 = n from by omega, sample_last hn]; exact hs.2

 



theorem exists_mesh {α : ℝ → Plane} (hα : ContinuousOn α I) {ε : ℝ} (hε : 0 < ε)
    (k : ℕ) (hk : 0 < k) :
    ∃ m : ℕ, 0 < m ∧ ∀ i < k * m, ∀ s ∈ Icc (sample (k * m) i) (sample (k * m) (i + 1)),
      dist (α s) (α (sample (k * m) i)) < ε := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_I.uniformContinuousOn_of_continuous hα) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N + 1, Nat.succ_pos N, fun i hi s hs => ?_⟩
  set n : ℕ := k * (N + 1) with hn
  have hnpos : 0 < n := Nat.mul_pos hk (Nat.succ_pos N)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  
  have hstep : 1 / (n : ℝ) < δ := by
    have h1 : (1 : ℝ) / δ < n := by
      refine lt_of_lt_of_le hN ?_
      have : N + 1 ≤ n := by
        calc N + 1 = 1 * (N + 1) := (one_mul _).symm
          _ ≤ k * (N + 1) := Nat.mul_le_mul_right _ hk
      exact_mod_cast le_trans (Nat.le_succ N) this
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ hnR]
    linarith
  have hiI : sample n i ∈ I := sample_mem_I (by omega)
  have hsI : s ∈ I := Icc_sample_subset_I (n := n) (by omega) hs
  refine hδ' s hsI (sample n i) hiI ?_
  rw [Real.dist_eq, abs_sub_lt_iff]
  have hd := sample_succ_sub n i
  constructor <;> [linarith [hs.1, hs.2]; linarith [hs.1, hs.2]]

 

 
def subarcCell (α : ℝ → Plane) (n i : ℕ) : Set Plane :=
  α '' Icc (sample n i) (sample n (i + 1))

theorem isCompact_subarcCell {α : ℝ → Plane} (hα : ContinuousOn α I) {n i : ℕ}
    (h : i + 1 ≤ n) : IsCompact (subarcCell α n i) :=
  isCompact_image_of_subset_I hα (Icc_sample_subset_I h) isClosed_Icc

theorem subarcCell_nonempty {α : ℝ → Plane} {n i : ℕ} : (subarcCell α n i).Nonempty :=
  ⟨α (sample n i), ⟨sample n i, ⟨le_refl _, sample_mono (Nat.le_succ i)⟩, rfl⟩⟩

 

theorem disjoint_subarcCell {α : ℝ → Plane} (hinj : InjOn α I) {n i j : ℕ}
    (hi : i + 1 ≤ n) (hj : j + 1 ≤ n) (hij : i + 2 ≤ j) :
    Disjoint (subarcCell α n i) (subarcCell α n j) := by
  have hn : 0 < n := by omega
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
  have huI : u ∈ I := Icc_sample_subset_I hi hu
  have hvI : v ∈ I := Icc_sample_subset_I hj hv
  have : v = u := hinj hvI huI hvu
  subst this
  have h1 : v ≤ sample n (i + 1) := hu.2
  have h2 : sample n j ≤ v := hv.1
  have hlt : sample n (i + 1) < sample n j := sample_strictMono hn (by omega)
  exact absurd (lt_of_le_of_lt h2 (lt_of_le_of_lt h1 hlt)) (lt_irrefl _)

 

theorem exists_pos_dist_nonadjacent {α : ℝ → Plane} (hα : ContinuousOn α I) (hinj : InjOn α I)
    {n : ℕ} :
    ∃ ρ > 0, ∀ i < n, ∀ j < n, i + 2 ≤ j →
      ∀ x ∈ subarcCell α n i, ∀ y ∈ subarcCell α n j, ρ ≤ dist x y := by
  classical
  set S : Set (ℕ × ℕ) := {p | p.1 < n ∧ p.2 < n} with hS
  have hSfin : S.Finite := by
    refine Set.Finite.subset (Set.finite_Iio n |>.prod (Set.finite_Iio n)) ?_
    rintro ⟨i, j⟩ ⟨hi, hj⟩
    exact ⟨hi, hj⟩
  have hmono : ∀ p : ℕ × ℕ, ∀ ⦃δ ε : ℝ⦄, 0 < δ → δ ≤ ε →
      (p.1 + 2 ≤ p.2 → ∀ x ∈ subarcCell α n p.1, ∀ y ∈ subarcCell α n p.2, ε ≤ dist x y) →
      (p.1 + 2 ≤ p.2 → ∀ x ∈ subarcCell α n p.1, ∀ y ∈ subarcCell α n p.2, δ ≤ dist x y) :=
    fun _ _ _ _ hle h had x hx y hy => le_trans hle (h had x hx y hy)
  have hex : ∀ p ∈ S, ∃ ε > 0,
      (p.1 + 2 ≤ p.2 → ∀ x ∈ subarcCell α n p.1, ∀ y ∈ subarcCell α n p.2, ε ≤ dist x y) := by
    rintro ⟨i, j⟩ ⟨hi, hj⟩
    by_cases had : i + 2 ≤ j
    · have hcK : IsCompact (subarcCell α n i) := isCompact_subarcCell hα (by omega)
      have hcL : IsCompact (subarcCell α n j) := isCompact_subarcCell hα (by omega)
      obtain ⟨ρ, hρ, hbound⟩ := Plane.exists_dist_pos hcK hcL
        (disjoint_subarcCell hinj (by omega) (by omega) had)
      exact ⟨ρ, hρ, fun _ => hbound⟩
    · exact ⟨1, one_pos, fun h => absurd h had⟩
  obtain ⟨ρ, hρ, hall⟩ := exists_pos_forall_of_finite hSfin hmono hex
  exact ⟨ρ, hρ, fun i hi j hj had => hall (i, j) ⟨hi, hj⟩ had⟩

 

 



theorem image_subset_iUnion_closedSquare {α : ℝ → Plane} {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hmesh : ∀ i < n, ∀ s ∈ Icc (sample n i) (sample n (i + 1)),
      dist (α s) (α (sample n i)) < ε) :
    α '' I ⊆ ⋃ i ∈ Finset.range n, closedSquare (α (sample n i)) ε := by
  rintro x ⟨s, hs, rfl⟩
  obtain ⟨i, hi, hmem⟩ := exists_mem_Icc_sample hn hs
  refine Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, ?_⟩
  have hd : dist (α s) (α (sample n i)) < ε := hmesh i hi s hmem
  change Plane.supDist (α s) (α (sample n i)) ≤ ε
  calc Plane.supDist (α s) (α (sample n i)) = Plane.supNorm (α s - α (sample n i)) := rfl
    _ ≤ ‖α s - α (sample n i)‖ := Plane.supNorm_le_norm _
    _ = dist (α s) (α (sample n i)) := (dist_eq_norm _ _).symm
    _ ≤ ε := le_of_lt hd

 









































end Schoenflies
