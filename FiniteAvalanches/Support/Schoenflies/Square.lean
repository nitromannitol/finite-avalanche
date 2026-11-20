/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Square.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Plane

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 






















open Metric Set

namespace Schoenflies

namespace Plane

 

theorem sub_apply (x y : Plane) (i : Fin 2) : (x - y) i = x i - y i := rfl

theorem smul_add_apply (a b : ℝ) (x y : Plane) (i : Fin 2) :
    (a • x + b • y) i = a * x i + b * y i := by simp

theorem continuous_coord (i : Fin 2) : Continuous fun x : Plane => x i :=
  PiLp.continuous_apply _ _ i

 

 
noncomputable def supNorm (x : Plane) : ℝ := max |x 0| |x 1|

 
noncomputable def supDist (x y : Plane) : ℝ := supNorm (x - y)

theorem supNorm_nonneg (x : Plane) : 0 ≤ supNorm x :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem supDist_nonneg (x y : Plane) : 0 ≤ supDist x y := supNorm_nonneg _

@[simp] theorem supDist_self (x : Plane) : supDist x x = 0 := by
  simp [supDist, supNorm]

theorem supDist_comm (x y : Plane) : supDist x y = supDist y x := by
  simp only [supDist, supNorm, sub_apply]
  rw [abs_sub_comm (x 0) (y 0), abs_sub_comm (x 1) (y 1)]

theorem abs_sub_zero_le_supDist (x y : Plane) : |x 0 - y 0| ≤ supDist x y :=
  le_max_left _ _

theorem abs_sub_one_le_supDist (x y : Plane) : |x 1 - y 1| ≤ supDist x y :=
  le_max_right _ _

theorem abs_zero_le_supNorm (x : Plane) : |x 0| ≤ supNorm x := le_max_left _ _

theorem abs_one_le_supNorm (x : Plane) : |x 1| ≤ supNorm x := le_max_right _ _

 
theorem supDist_triangle (x y z : Plane) : supDist x z ≤ supDist x y + supDist y z := by
  simp only [supDist, supNorm, sub_apply]
  refine max_le ?_ ?_
  · calc |x 0 - z 0| ≤ |x 0 - y 0| + |y 0 - z 0| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_zero_le_supDist x y) (abs_sub_zero_le_supDist y z)
  · calc |x 1 - z 1| ≤ |x 1 - y 1| + |y 1 - z 1| := abs_sub_le _ _ _
      _ ≤ supDist x y + supDist y z :=
          add_le_add (abs_sub_one_le_supDist x y) (abs_sub_one_le_supDist y z)

theorem norm_sq_eq (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]

 
theorem supNorm_le_norm (x : Plane) : supNorm x ≤ ‖x‖ := by
  have h0 : |x 0| ≤ ‖x‖ := by
    have : |x 0| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 1)]
    nlinarith [abs_nonneg (x 0), norm_nonneg x]
  have h1 : |x 1| ≤ ‖x‖ := by
    have : |x 1| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 0)]
    nlinarith [abs_nonneg (x 1), norm_nonneg x]
  exact max_le h0 h1

 
theorem norm_le_sqrt_two_mul_supNorm (x : Plane) : ‖x‖ ≤ Real.sqrt 2 * supNorm x := by
  have h0 : x 0 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_zero_le_supNorm x, abs_nonneg (x 0)]
  have h1 : x 1 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_one_le_supNorm x, abs_nonneg (x 1)]
  have hbound : ‖x‖ ^ 2 ≤ (Real.sqrt 2 * supNorm x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_sq_eq]
    linarith
  nlinarith [norm_nonneg x, mul_nonneg (Real.sqrt_nonneg 2) (supNorm_nonneg x)]

 




theorem convex_coord_le (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i ≤ r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_coord_ge (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r ≤ x i} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem convex_coord_lt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | x i < r} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem convex_coord_gt (i : Fin 2) (r : ℝ) : Convex ℝ {x : Plane | r < x i} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at *
  rw [smul_add_apply]
  have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left hx ha', mul_le_mul_of_nonneg_left hy.le hb]

theorem isOpen_coord_lt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | x i < r} :=
  isOpen_lt (continuous_coord i) continuous_const

theorem isOpen_coord_gt (i : Fin 2) (r : ℝ) : IsOpen {x : Plane | r < x i} :=
  isOpen_lt continuous_const (continuous_coord i)

 

 
def closedSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c ≤ r}

 
def openSquare (c : Plane) (r : ℝ) : Set Plane := {x | supDist x c < r}

theorem closedSquare_eq_inter (c : Plane) (r : ℝ) :
    closedSquare c r =
      ({x : Plane | c 0 - r ≤ x 0} ∩ {x : Plane | x 0 ≤ c 0 + r}) ∩
      ({x : Plane | c 1 - r ≤ x 1} ∩ {x : Plane | x 1 ≤ c 1 + r}) := by
  ext x
  simp only [closedSquare, supDist, supNorm, sub_apply, mem_setOf_eq, mem_inter_iff,
    max_le_iff, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem openSquare_eq_inter (c : Plane) (r : ℝ) :
    openSquare c r =
      ({x : Plane | c 0 - r < x 0} ∩ {x : Plane | x 0 < c 0 + r}) ∩
      ({x : Plane | c 1 - r < x 1} ∩ {x : Plane | x 1 < c 1 + r}) := by
  ext x
  simp only [openSquare, supDist, supNorm, sub_apply, mem_setOf_eq, mem_inter_iff,
    max_lt_iff, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem convex_closedSquare (c : Plane) (r : ℝ) : Convex ℝ (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((convex_coord_ge 0 _).inter (convex_coord_le 0 _)).inter
    ((convex_coord_ge 1 _).inter (convex_coord_le 1 _))

theorem convex_openSquare (c : Plane) (r : ℝ) : Convex ℝ (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((convex_coord_gt 0 _).inter (convex_coord_lt 0 _)).inter
    ((convex_coord_gt 1 _).inter (convex_coord_lt 1 _))

theorem isOpen_openSquare (c : Plane) (r : ℝ) : IsOpen (openSquare c r) := by
  rw [openSquare_eq_inter]
  exact ((isOpen_coord_gt 0 _).inter (isOpen_coord_lt 0 _)).inter
    ((isOpen_coord_gt 1 _).inter (isOpen_coord_lt 1 _))

theorem isClosed_closedSquare (c : Plane) (r : ℝ) : IsClosed (closedSquare c r) := by
  rw [closedSquare_eq_inter]
  exact ((isClosed_le continuous_const (continuous_coord 0)).inter
      (isClosed_le (continuous_coord 0) continuous_const)).inter
    ((isClosed_le continuous_const (continuous_coord 1)).inter
      (isClosed_le (continuous_coord 1) continuous_const))

 

 
def beyondSquare (r : ℝ) : Set Plane := {x | r < |x 0| ∨ r < |x 1|}

 




theorem isConnected_beyondSquare (r : ℝ) : IsConnected (beyondSquare r) := by
  set R : Set Plane := {x : Plane | r < x 0} with hR
  set L : Set Plane := {x : Plane | x 0 < -r} with hL
  set T : Set Plane := {x : Plane | r < x 1} with hT
  set B : Set Plane := {x : Plane | x 1 < -r} with hB
  have hcover : beyondSquare r = R ∪ T ∪ L ∪ B := by
    ext x
    simp only [beyondSquare, hR, hL, hT, hB, mem_setOf_eq, mem_union, lt_abs]
    constructor
    · rintro (h | h) <;> rcases h with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr (by linarith)
    · rintro (((h | h) | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr (by linarith))
      · exact Or.inr (Or.inr (by linarith))
  
  
  have hRT : mk (r + 1) (r + 1) ∈ R ∩ T :=
    ⟨show r < r + 1 by linarith, show r < r + 1 by linarith⟩
  have hTL : mk (-r - 1) (r + 1) ∈ T ∩ L :=
    ⟨show r < r + 1 by linarith, show -r - 1 < -r by linarith⟩
  have hLB : mk (-r - 1) (-r - 1) ∈ L ∩ B :=
    ⟨show -r - 1 < -r by linarith, show -r - 1 < -r by linarith⟩
  have cR : IsConnected R :=
    (convex_coord_gt 0 r).isConnected ⟨mk (r + 1) 0, show r < r + 1 by linarith⟩
  have cL : IsConnected L :=
    (convex_coord_lt 0 (-r)).isConnected ⟨mk (-r - 1) 0, show -r - 1 < -r by linarith⟩
  have cT : IsConnected T :=
    (convex_coord_gt 1 r).isConnected ⟨mk 0 (r + 1), show r < r + 1 by linarith⟩
  have cB : IsConnected B :=
    (convex_coord_lt 1 (-r)).isConnected ⟨mk 0 (-r - 1), show -r - 1 < -r by linarith⟩
  have c1 : IsConnected (R ∪ T) := cR.union ⟨mk (r + 1) (r + 1), hRT.1, hRT.2⟩ cT
  have c2 : IsConnected (R ∪ T ∪ L) :=
    c1.union ⟨mk (-r - 1) (r + 1), Or.inr hTL.1, hTL.2⟩ cL
  have c3 : IsConnected (R ∪ T ∪ L ∪ B) :=
    c2.union ⟨mk (-r - 1) (-r - 1), Or.inr hLB.1, hLB.2⟩ cB
  rw [hcover]
  exact c3

end Plane

end Schoenflies
