/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Strip.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`;
explicit binders added for this project's Lean option `autoImplicit false`.
-/
import FiniteAvalanches.Support.Schoenflies.Direction
import FiniteAvalanches.Support.Schoenflies.UniformBound
import Mathlib.Data.ZMod.Basic

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




































































open Metric Set

namespace Schoenflies

namespace Plane

variable {u w d r₁ r₂ a x : Plane} {r t s c ρ : ℝ}

 







 




theorem germs_split' (h : det r₁ r₂ ≠ 0) (hs : 0 < s)
    (hsmall : s * |inner ℝ r₁ r₂| < t * |det r₁ r₂|) :
    (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
      (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) := by
  have hle : inner ℝ r₁ r₂ ≤ |inner ℝ r₁ r₂| := le_abs_self _
  have hle' : inner ℝ r₂ r₁ ≤ |inner ℝ r₁ r₂| := by
    rw [real_inner_comm]; exact hle
  rcases lt_or_gt_of_ne h with hneg | hpos
  · 
    have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    have habs : |det r₁ r₂| = det r₂ r₁ := by rw [abs_of_neg hneg, det_comm r₁ r₂]; ring
    have hsmall' : s * inner ℝ r₂ r₁ < t * det r₂ r₁ := by
      rw [habs] at hsmall
      nlinarith
    have H := germs_split h' hs hsmall'
    exact ⟨⟨H.2.2, H.2.1⟩, ⟨H.1.2, H.1.1⟩⟩
  · have habs : |det r₁ r₂| = det r₁ r₂ := abs_of_pos hpos
    have hsmall' : s * inner ℝ r₁ r₂ < t * det r₁ r₂ := by
      rw [habs] at hsmall
      nlinarith
    exact germs_split hpos hs hsmall'

 

 
theorem arcCCW_disjoint' (h : det r₁ r₂ ≠ 0) : Disjoint (arcCCW r₁ r₂) (arcCCW r₂ r₁) := by
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    exact (arcCCW_disjoint h').symm
  · exact arcCCW_disjoint hpos

 

theorem mem_ray_or_mem_arcCCW' (h : det r₁ r₂ ≠ 0) (hd : d ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ d = c • r₁) ∨ (∃ c : ℝ, 0 < c ∧ d = c • r₂) ∨
      d ∈ arcCCW r₁ r₂ ∨ d ∈ arcCCW r₂ r₁ := by
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have h' : 0 < det r₂ r₁ := by rw [det_comm r₂ r₁]; linarith
    rcases mem_ray_or_mem_arcCCW h' hd with h1 | h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact Or.inr (Or.inr (Or.inl h1))
  · exact mem_ray_or_mem_arcCCW hpos hd

 

theorem notMem_arcCCW_smul (u w : Plane) (hc : 0 ≤ c) :
    c • u ∉ arcCCW u w ∧ c • u ∉ arcCCW w u := by
  have e1 : det u (c • u) = 0 := by rw [det_smul_right, det_self, mul_zero]
  have e2 : det (c • u) u = 0 := by rw [det_smul_left, det_self, mul_zero]
  have e3 : det (c • u) w = c * det u w := det_smul_left _ _ _
  have e4 : det w (c • u) = c * det w u := det_smul_right _ _ _
  have e5 : det w u = -det u w := det_comm w u
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨_, h2⟩)
    · rw [e1] at h1; exact lt_irrefl 0 h1
    · rw [e3] at h1; rw [e5] at h2; nlinarith
    · rw [e1] at h2; exact lt_irrefl 0 h2
  · rintro (⟨_, h2⟩ | ⟨h2, _⟩ | ⟨h1, h2⟩)
    · rw [e2] at h2; exact lt_irrefl 0 h2
    · rw [e2] at h2; exact lt_irrefl 0 h2
    · rw [e4, e5] at h2; nlinarith

 
theorem isLinearMap_det_right (u : Plane) : IsLinearMap ℝ fun d : Plane => det u d :=
  ⟨fun x y => det_add_right u x y, fun c x => by rw [det_smul_right, smul_eq_mul]⟩

theorem isLinearMap_det_left (w : Plane) : IsLinearMap ℝ fun d : Plane => det d w :=
  ⟨fun x y => det_add_left x y w, fun c x => by rw [det_smul_left, smul_eq_mul]⟩

theorem convex_det_right_pos (u : Plane) : Convex ℝ {d : Plane | 0 < det u d} :=
  convex_halfSpace_gt (isLinearMap_det_right u) 0

theorem convex_det_right_neg (u : Plane) : Convex ℝ {d : Plane | det u d < 0} :=
  convex_halfSpace_lt (isLinearMap_det_right u) 0

theorem convex_det_left_pos (w : Plane) : Convex ℝ {d : Plane | 0 < det d w} :=
  convex_halfSpace_gt (isLinearMap_det_left w) 0

theorem convex_det_left_neg (w : Plane) : Convex ℝ {d : Plane | det d w < 0} :=
  convex_halfSpace_lt (isLinearMap_det_left w) 0

 


theorem isConnected_arcCCW_ball (h : det u w ≠ 0) (hρ : 0 < ρ) :
    IsConnected (arcCCW u w ∩ ball (0 : Plane) ρ) := by
  
  have hne : u + w ≠ 0 := by
    intro hz
    have hw : w = -u := by linear_combination (norm := module) hz
    rw [hw, show (-u : Plane) = (-1 : ℝ) • u by module, det_smul_right, det_self,
      mul_zero] at h
    exact h rfl
  have hnpos : 0 < ‖u + w‖ := norm_pos_iff.2 hne
  obtain ⟨ε, hε, hεball⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * ‖u + w‖ < ρ := by
    refine ⟨ρ / (2 * ‖u + w‖), by positivity, ?_⟩
    have : ρ / (2 * ‖u + w‖) * ‖u + w‖ = ρ / 2 := by field_simp
    rw [this]; linarith
  have hball : ∀ σ : ℝ, |σ| = ε → σ • (u + w) ∈ ball (0 : Plane) ρ := by
    intro σ hσ
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, hσ]
    exact hεball
  rcases lt_or_gt_of_ne h with hneg | hpos
  · 
    have h' : 0 < det w u := by rw [det_comm w u]; linarith
    have harc : arcCCW u w = {d : Plane | det w d < 0} ∪ {d : Plane | det d u < 0} := by
      ext d
      rw [mem_arcCCW_rev_iff h']
      simp only [mem_union, mem_setOf_eq]
    have hd0 : (-ε) • (u + w) ∈ ball (0 : Plane) ρ :=
      hball _ (by rw [abs_of_neg (neg_neg_iff_pos.2 hε), neg_neg])
    have hA : (-ε) • (u + w) ∈ {d : Plane | det w d < 0} := by
      change det w ((-ε) • (u + w)) < 0
      rw [det_smul_right, det_add_right, det_self, add_zero]
      nlinarith
    have hB : (-ε) • (u + w) ∈ {d : Plane | det d u < 0} := by
      change det ((-ε) • (u + w)) u < 0
      rw [det_smul_left, det_add_left, det_self, zero_add]
      nlinarith
    refine ⟨⟨_, by rw [harc]; exact ⟨Or.inl hA, hd0⟩⟩, ?_⟩
    rw [harc, union_inter_distrib_right]
    exact IsPreconnected.union _ ⟨hA, hd0⟩ ⟨hB, hd0⟩
      ((convex_det_right_neg w).inter (convex_ball _ _)).isPreconnected
      ((convex_det_left_neg u).inter (convex_ball _ _)).isPreconnected
  · 
    have harc : arcCCW u w = {d : Plane | 0 < det u d} ∩ {d : Plane | 0 < det d w} := by
      ext d
      rw [mem_arcCCW_iff hpos]
      simp only [mem_inter_iff, mem_setOf_eq]
    have hmem : ε • (u + w) ∈ arcCCW u w ∩ ball (0 : Plane) ρ := by
      refine ⟨?_, hball _ (abs_of_pos hε)⟩
      rw [harc]
      constructor
      · change 0 < det u (ε • (u + w))
        rw [det_smul_right, det_add_right, det_self, zero_add]
        positivity
      · change 0 < det (ε • (u + w)) w
        rw [det_smul_left, det_add_left, det_self, add_zero]
        positivity
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [harc]
    exact (((convex_det_right_pos u).inter (convex_det_left_pos w)).inter
      (convex_ball _ _)).isPreconnected

 






 
def cone (v : Plane) (A : Set Plane) (ρ : ℝ) : Set Plane := {x | x - v ∈ A} ∩ ball v ρ

theorem mem_cone_iff {v : Plane} {A : Set Plane} :
    x ∈ cone v A ρ ↔ x - v ∈ A ∧ dist x v < ρ := Iff.rfl

theorem cone_subset_ball {v : Plane} {A : Set Plane} : cone v A ρ ⊆ ball v ρ := inter_subset_right

theorem isOpen_cone {v : Plane} {A : Set Plane} (hA : IsOpen A) : IsOpen (cone v A ρ) :=
  (hA.preimage (continuous_id.sub continuous_const)).inter isOpen_ball

 

theorem cone_eq_image (v : Plane) (A : Set Plane) (ρ : ℝ) :
    cone v A ρ = (fun d => v + d) '' (A ∩ ball (0 : Plane) ρ) := by
  ext y
  constructor
  · rintro ⟨hy, hb⟩
    refine ⟨y - v, ⟨hy, ?_⟩, ?_⟩
    · rw [mem_ball, dist_zero_right, ← dist_eq_norm]
      exact hb
    · change v + (y - v) = y
      module
  · rintro ⟨d, ⟨hd, hb⟩, rfl⟩
    have he : v + d - v = d := by module
    refine ⟨by rw [mem_setOf_eq, he]; exact hd, ?_⟩
    rw [mem_ball, dist_eq_norm, he]
    rw [mem_ball, dist_zero_right] at hb
    exact hb

theorem isConnected_cone_arcCCW (v : Plane) (h : det u w ≠ 0) (hρ : 0 < ρ) :
    IsConnected (cone v (arcCCW u w) ρ) := by
  rw [cone_eq_image]
  have hc : Continuous fun d : Plane => v + d := continuous_const.add continuous_id
  exact (isConnected_arcCCW_ball h hρ).image _ hc.continuousOn

 





 
noncomputable def coordAlong (a u x : Plane) : ℝ := inner ℝ u (x - a)

 

def coordAcross (a u x : Plane) : ℝ := det u (x - a)

 
theorem det_eq_inner_perp (u v : Plane) : det u v = inner ℝ (perp u) v := by
  rw [inner_eq, det]
  simp [perp]
  ring

theorem abs_det_le (u v : Plane) : |det u v| ≤ ‖u‖ * ‖v‖ := by
  rw [det_eq_inner_perp]
  calc |inner ℝ (perp u) v| ≤ ‖perp u‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ := by rw [norm_perp]

@[simp] theorem coordAlong_param (hu : IsDirection u) (a : Plane) (t s : ℝ) :
    coordAlong a u (a + t • u + s • perp u) = t := by
  have h : a + t • u + s • perp u - a = t • u + s • perp u := by module
  rw [coordAlong, h, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, inner_perp_self, hu.norm]
  ring

@[simp] theorem coordAcross_param (hu : IsDirection u) (a : Plane) (t s : ℝ) :
    coordAcross a u (a + t • u + s • perp u) = s := by
  have h : a + t • u + s • perp u - a = t • u + s • perp u := by module
  rw [coordAcross, h, det_germ_self, hu.norm]
  ring

 
theorem frame_decomp (hu : IsDirection u) (a x : Plane) :
    x = a + (coordAlong a u x) • u + (coordAcross a u x) • perp u := by
  have hnorm : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have := hu.norm
    rw [EuclideanSpace.norm_eq] at this
    have h2 : Real.sqrt (∑ i, ‖u i‖ ^ 2) ^ 2 = 1 ^ 2 := by rw [this]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)] at h2
    simpa [Fin.sum_univ_two, sq_abs] using h2
  have hal : coordAlong a u x = u 0 * (x 0 - a 0) + u 1 * (x 1 - a 1) := by
    rw [coordAlong, inner_eq]; simp
  have hac : coordAcross a u x = u 0 * (x 1 - a 1) - u 1 * (x 0 - a 0) := by
    rw [coordAcross, det]; simp
  ext i
  fin_cases i
  · simp only [hal, hac]
    simp [perp]
    linear_combination (a 0 - x 0) * hnorm
  · simp only [hal, hac]
    simp [perp]
    linear_combination (a 1 - x 1) * hnorm

 

theorem abs_coordAlong_sub_le (hu : IsDirection u) (a x y : Plane) :
    |coordAlong a u x - coordAlong a u y| ≤ dist x y := by
  have h : coordAlong a u x - coordAlong a u y = inner ℝ u (x - y) := by
    rw [coordAlong, coordAlong, ← inner_sub_right]
    congr 1
    module
  rw [h, dist_eq_norm]
  calc |inner ℝ u (x - y)| ≤ ‖u‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    _ = ‖x - y‖ := by rw [hu.norm, one_mul]

theorem abs_coordAcross_sub_le (hu : IsDirection u) (a x y : Plane) :
    |coordAcross a u x - coordAcross a u y| ≤ dist x y := by
  have h : coordAcross a u x - coordAcross a u y = det u (x - y) := by
    simp only [coordAcross, det]
    simp
    ring
  rw [h, dist_eq_norm]
  calc |det u (x - y)| ≤ ‖u‖ * ‖x - y‖ := abs_det_le _ _
    _ = ‖x - y‖ := by rw [hu.norm, one_mul]

 

def strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : Set Plane :=
  {x | t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ ∧
    s₁ < coordAcross a u x ∧ coordAcross a u x < s₂}

theorem mem_strip_iff {t₁ t₂ s₁ s₂ : ℝ} :
    x ∈ strip a u t₁ t₂ s₁ s₂ ↔ t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ ∧
      s₁ < coordAcross a u x ∧ coordAcross a u x < s₂ := Iff.rfl

theorem continuous_coordAlong (a u : Plane) : Continuous (coordAlong a u) :=
  (continuous_const.inner (continuous_id.sub continuous_const))

theorem continuous_coordAcross (a u : Plane) : Continuous (coordAcross a u) :=
  (continuous_det_right u).comp (continuous_id.sub continuous_const)

theorem isOpen_strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : IsOpen (strip a u t₁ t₂ s₁ s₂) := by
  have key : strip a u t₁ t₂ s₁ s₂ =
      ({x : Plane | t₁ < coordAlong a u x} ∩ {x : Plane | coordAlong a u x < t₂}) ∩
        ({x : Plane | s₁ < coordAcross a u x} ∩ {x : Plane | coordAcross a u x < s₂}) := by
    ext y
    simp only [mem_strip_iff, mem_inter_iff, mem_setOf_eq]
    tauto
  rw [key]
  exact ((isOpen_lt continuous_const (continuous_coordAlong a u)).inter
      (isOpen_lt (continuous_coordAlong a u) continuous_const)).inter
    ((isOpen_lt continuous_const (continuous_coordAcross a u)).inter
      (isOpen_lt (continuous_coordAcross a u) continuous_const))

theorem convex_strip (a u : Plane) (t₁ t₂ s₁ s₂ : ℝ) : Convex ℝ (strip a u t₁ t₂ s₁ s₂) := by
  have key : strip a u t₁ t₂ s₁ s₂ =
      ({x : Plane | t₁ + inner ℝ u a < inner ℝ u x} ∩ {x : Plane | inner ℝ u x < t₂ + inner ℝ u a})
        ∩ ({x : Plane | s₁ + det u a < det u x} ∩ {x : Plane | det u x < s₂ + det u a}) := by
    ext y
    have h1 : coordAlong a u y = inner ℝ u y - inner ℝ u a := by
      rw [coordAlong, inner_sub_right]
    have h2 : coordAcross a u y = det u y - det u a := by
      simp only [coordAcross, det]
      simp
      ring
    simp only [mem_strip_iff, mem_inter_iff, mem_setOf_eq, h1, h2]
    constructor
    · rintro ⟨a1, a2, a3, a4⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩; exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [key]
  have hlin : IsLinearMap ℝ fun x : Plane => inner ℝ u x :=
    ⟨fun x y => inner_add_right _ _ _, fun c x => by rw [real_inner_smul_right, smul_eq_mul]⟩
  exact ((convex_halfSpace_gt hlin _).inter (convex_halfSpace_lt hlin _)).inter
    ((convex_halfSpace_gt (isLinearMap_det_right u) _).inter
      (convex_halfSpace_lt (isLinearMap_det_right u) _))

theorem mem_strip_param (hu : IsDirection u) (a : Plane) {t s t₁ t₂ s₁ s₂ : ℝ} :
    a + t • u + s • perp u ∈ strip a u t₁ t₂ s₁ s₂ ↔ t₁ < t ∧ t < t₂ ∧ s₁ < s ∧ s < s₂ := by
  rw [mem_strip_iff, coordAlong_param hu, coordAcross_param hu]

 

theorem dist_foot (hu : IsDirection u) (a x : Plane) :
    dist x (a + (coordAlong a u x) • u) = |coordAcross a u x| := by
  have h := frame_decomp hu a x
  rw [dist_eq_norm]
  have hx : x - (a + (coordAlong a u x) • u) = (coordAcross a u x) • perp u := by
    nth_rewrite 1 [h]
    module
  rw [hx, norm_smul, Real.norm_eq_abs, norm_perp, hu.norm, mul_one]

end Plane

 





open Plane

variable {m : ℕ}

 
structure ClosedPolygon (m : ℕ) where
   
  vertex : ZMod (m + 3) → Plane
   
  vertex_inj : Function.Injective vertex
   
  edges_meet : ∀ i j : ZMod (m + 3), i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}
   

  corner : ∀ i : ZMod (m + 3), det (vertex (i - 1) - vertex i) (vertex (i + 1) - vertex i) ≠ 0

namespace ClosedPolygon

variable (P : ClosedPolygon m) (i j : ZMod (m + 3)) (c t s : ℝ)

theorem one_ne_zero' : (1 : ZMod (m + 3)) ≠ 0 := by
  intro h
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by norm_num,
    ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd one_pos h
  omega

theorem succ_ne_self : i + 1 ≠ i := fun h => one_ne_zero' (m := m) (by linear_combination h)

theorem vertex_ne : P.vertex i ≠ P.vertex (i + 1) := fun h =>
  succ_ne_self i (P.vertex_inj h).symm

 

 
noncomputable def len : ℝ := ‖P.vertex (i + 1) - P.vertex i‖

 
noncomputable def tang : Plane := dir (P.vertex (i + 1) - P.vertex i)

 
noncomputable def rayIn : Plane := dir (P.vertex (i - 1) - P.vertex i)

 
noncomputable def off : Plane := P.vertex i + t • P.tang i + s • perp (P.tang i)

 
noncomputable def pt : Plane := P.off i c 0

 
def edge : Set Plane := segment ℝ (P.vertex i) (P.vertex (i + 1))

 
def carrier : Set Plane := ⋃ i, P.edge i

variable {P i j c t s}

theorem sub_ne_zero_of_edge : P.vertex (i + 1) - P.vertex i ≠ 0 :=
  sub_ne_zero.2 (P.vertex_ne i).symm

theorem len_pos : 0 < P.len i := norm_pos_iff.2 sub_ne_zero_of_edge

theorem isDirection_tang : IsDirection (P.tang i) := isDirection_dir sub_ne_zero_of_edge

theorem len_smul_tang : (P.len i) • P.tang i = P.vertex (i + 1) - P.vertex i := by
  rw [tang, dir, smul_smul, len, mul_inv_cancel₀ (norm_ne_zero_iff.2 sub_ne_zero_of_edge),
    one_smul]

theorem off_zero_zero : P.off i 0 0 = P.vertex i := by rw [off]; module

theorem pt_zero : P.pt i 0 = P.vertex i := off_zero_zero

theorem pt_len : P.pt i (P.len i) = P.vertex (i + 1) := by
  rw [pt, off, zero_smul, add_zero, len_smul_tang]
  module

theorem off_sub_vertex : P.off i t s - P.vertex i = t • P.tang i + s • perp (P.tang i) := by
  rw [off]; module

theorem pt_sub_vertex : P.pt i c - P.vertex i = c • P.tang i := by
  rw [pt, off_sub_vertex, zero_smul, add_zero]

theorem dist_pt_vertex : dist (P.pt i c) (P.vertex i) = |c| := by
  rw [dist_eq_norm, pt_sub_vertex, norm_smul, Real.norm_eq_abs, isDirection_tang.norm, mul_one]

theorem dist_off_vertex_le : dist (P.off i t s) (P.vertex i) ≤ |t| + |s| := by
  rw [dist_eq_norm, off_sub_vertex]
  calc ‖t • P.tang i + s • perp (P.tang i)‖ ≤ ‖t • P.tang i‖ + ‖s • perp (P.tang i)‖ :=
        norm_add_le _ _
    _ = |t| + |s| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_perp,
          isDirection_tang.norm, mul_one, mul_one]

@[simp] theorem coordAlong_off : coordAlong (P.vertex i) (P.tang i) (P.off i t s) = t :=
  coordAlong_param isDirection_tang _ _ _

@[simp] theorem coordAcross_off : coordAcross (P.vertex i) (P.tang i) (P.off i t s) = s :=
  coordAcross_param isDirection_tang _ _ _

 
theorem off_coord (P : ClosedPolygon m) (i : ZMod (m + 3)) (x : Plane) :
    x = P.off i (coordAlong (P.vertex i) (P.tang i) x) (coordAcross (P.vertex i) (P.tang i) x) :=
  frame_decomp isDirection_tang _ _

theorem off_injective {t' s' : ℝ} (h : P.off i t s = P.off i t' s') : t = t' ∧ s = s' := by
  constructor
  · have := congrArg (coordAlong (P.vertex i) (P.tang i)) h
    simpa using this
  · have := congrArg (coordAcross (P.vertex i) (P.tang i)) h
    simpa using this

theorem mem_edge_iff {x : Plane} :
    x ∈ P.edge i ↔ ∃ c ∈ Set.Icc (0 : ℝ) (P.len i), x = P.pt i c := by
  rw [edge, segment_eq_image' ℝ]
  constructor
  · rintro ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    refine ⟨θ * P.len i, ⟨mul_nonneg hθ0 len_pos.le, ?_⟩, ?_⟩
    · nlinarith [len_pos (P := P) (i := i)]
    · rw [pt, off, zero_smul, add_zero, ← len_smul_tang]
      simp [smul_smul]
  · rintro ⟨c, ⟨hc0, hc1⟩, rfl⟩
    refine ⟨c / P.len i, ⟨div_nonneg hc0 len_pos.le, ?_⟩, ?_⟩
    · rw [div_le_one len_pos]; exact hc1
    · rw [pt, off, zero_smul, add_zero, ← len_smul_tang]
      simp [smul_smul, div_mul_cancel₀ _ (len_pos (P := P) (i := i)).ne']

theorem pt_mem_edge (hc : c ∈ Set.Icc (0 : ℝ) (P.len i)) : P.pt i c ∈ P.edge i :=
  mem_edge_iff.2 ⟨c, hc, rfl⟩

theorem vertex_mem_edge : P.vertex i ∈ P.edge i := by
  rw [← pt_zero]; exact pt_mem_edge ⟨le_refl _, len_pos.le⟩

theorem vertex_mem_carrier : P.vertex i ∈ P.carrier := Set.mem_iUnion.2 ⟨i, vertex_mem_edge⟩

theorem edge_subset_carrier : P.edge i ⊆ P.carrier := Set.subset_iUnion _ i

 

theorem rayIn_succ : P.rayIn (i + 1) = -P.tang i := by
  rw [rayIn, tang, add_sub_cancel_right, dir, dir, norm_sub_rev]
  module

theorem vertex_pred_ne : P.vertex (i - 1) - P.vertex i ≠ 0 := by
  have h := P.vertex_ne (i - 1)
  rw [sub_add_cancel] at h
  exact sub_ne_zero.2 h

theorem det_rays_ne_zero : det (P.rayIn i) (P.tang i) ≠ 0 := by
  obtain ⟨c₁, hc₁, h₁⟩ := dir_eq_smul (vertex_pred_ne (P := P) (i := i))
  obtain ⟨c₂, hc₂, h₂⟩ := dir_eq_smul (sub_ne_zero_of_edge (P := P) (i := i))
  rw [rayIn, tang, h₁, h₂, det_smul_left, det_smul_right]
  exact mul_ne_zero hc₁.ne' (mul_ne_zero hc₂.ne' (P.corner i))

 


theorem mem_edge_pred_sub {x : Plane} (hx : x ∈ P.edge (i - 1)) :
    ∃ c : ℝ, 0 ≤ c ∧ x - P.vertex i = c • P.rayIn i := by
  rw [mem_edge_iff] at hx
  obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hx
  refine ⟨P.len (i - 1) - c, by linarith, ?_⟩
  have hsucc : i - 1 + 1 = i := sub_add_cancel i 1
  have hr : P.rayIn i = -P.tang (i - 1) := by
    have := rayIn_succ (P := P) (i := i - 1)
    rwa [hsucc] at this
  have hv : P.vertex i = P.vertex (i - 1 + 1) := by rw [hsucc]
  have hlen : P.vertex (i - 1 + 1) = P.vertex (i - 1) + (P.len (i - 1)) • P.tang (i - 1) := by
    rw [len_smul_tang]; module
  rw [pt, off, zero_smul, add_zero, hr, hv, hlen]
  module

theorem mem_edge_sub {x : Plane} (hx : x ∈ P.edge i) :
    ∃ c : ℝ, 0 ≤ c ∧ x - P.vertex i = c • P.tang i := by
  rw [mem_edge_iff] at hx
  obtain ⟨c, ⟨hc0, _⟩, rfl⟩ := hx
  exact ⟨c, hc0, pt_sub_vertex⟩

theorem pt_eq : P.pt i c = P.vertex i + c • P.tang i := by rw [pt, off, zero_smul, add_zero]

end ClosedPolygon

 







 
structure StripData (P : ClosedPolygon m) where
   
  R : ℝ
   
  lam : ℝ
   
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_lam : rho < lam
   
  two_lam_lt_R : 2 * lam < R
   
  four_lam_lt_len : ∀ i, 4 * lam < P.len i
   
  R_le_len : ∀ i, R ≤ P.len i
   
  sep_vertex : ∀ i j, i ≠ j → 2 * R ≤ dist (P.vertex i) (P.vertex j)
   

  sep_vertex_edge : ∀ i j, j ≠ i - 1 → j ≠ i → ∀ y ∈ P.edge j, 2 * R ≤ dist (P.vertex i) y
   
  sep_trim_edge : ∀ i j, j ≠ i → ∀ c ∈ Set.Icc lam (P.len i - lam), ∀ y ∈ P.edge j,
    2 * rho ≤ dist (P.pt i c) y
   


  germ : ∀ i, rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) ≤ lam * |det (P.rayIn i) (P.tang i)|

namespace StripData

variable {P : ClosedPolygon m} (D : StripData P) {i j : ZMod (m + 3)} {x : Plane}

theorem lam_pos : 0 < D.lam := lt_trans D.rho_pos D.rho_lt_lam

theorem R_pos : 0 < D.R := by have := D.lam_pos; linarith [D.two_lam_lt_R]

theorem rho_lt_R : D.rho < D.R := by
  have := D.lam_pos; have := D.rho_lt_lam; linarith [D.two_lam_lt_R]

 

 
def blockL (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) 0 D.rho

 
def blockR (i : ZMod (m + 3)) : Set Plane :=
  strip (P.vertex i) (P.tang i) D.lam (P.len i - D.lam) (-D.rho) 0

 

def sectorL (i : ZMod (m + 3)) : Set Plane :=
  cone (P.vertex i) (arcCCW (P.tang i) (P.rayIn i)) D.R

 
def sectorR (i : ZMod (m + 3)) : Set Plane :=
  cone (P.vertex i) (arcCCW (P.rayIn i) (P.tang i)) D.R

 
def sideL : Set Plane := ⋃ i, (D.sectorL i ∪ D.blockL i)

 
def sideR : Set Plane := ⋃ i, (D.sectorR i ∪ D.blockR i)

 
def nbhd : Set Plane := D.sideL ∪ D.sideR ∪ P.carrier

theorem mem_blockL_iff : x ∈ D.blockL i ↔
    D.lam < coordAlong (P.vertex i) (P.tang i) x ∧
      coordAlong (P.vertex i) (P.tang i) x < P.len i - D.lam ∧
      0 < coordAcross (P.vertex i) (P.tang i) x ∧
      coordAcross (P.vertex i) (P.tang i) x < D.rho := Iff.rfl

theorem mem_blockR_iff : x ∈ D.blockR i ↔
    D.lam < coordAlong (P.vertex i) (P.tang i) x ∧
      coordAlong (P.vertex i) (P.tang i) x < P.len i - D.lam ∧
      -D.rho < coordAcross (P.vertex i) (P.tang i) x ∧
      coordAcross (P.vertex i) (P.tang i) x < 0 := Iff.rfl

theorem mem_blockL_off {t s : ℝ} : P.off i t s ∈ D.blockL i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ 0 < s ∧ s < D.rho := by
  rw [mem_blockL_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem mem_blockR_off {t s : ℝ} : P.off i t s ∈ D.blockR i ↔
    D.lam < t ∧ t < P.len i - D.lam ∧ -D.rho < s ∧ s < 0 := by
  rw [mem_blockR_iff, ClosedPolygon.coordAlong_off, ClosedPolygon.coordAcross_off]

theorem isOpen_blockL : IsOpen (D.blockL i) := isOpen_strip _ _ _ _ _ _
theorem isOpen_blockR : IsOpen (D.blockR i) := isOpen_strip _ _ _ _ _ _
theorem isOpen_sectorL : IsOpen (D.sectorL i) := isOpen_cone (isOpen_arcCCW _ _)
theorem isOpen_sectorR : IsOpen (D.sectorR i) := isOpen_cone (isOpen_arcCCW _ _)

theorem convex_blockL : Convex ℝ (D.blockL i) := convex_strip _ _ _ _ _ _
theorem convex_blockR : Convex ℝ (D.blockR i) := convex_strip _ _ _ _ _ _

theorem isConnected_sectorL : IsConnected (D.sectorL i) :=
  isConnected_cone_arcCCW _ (by rw [det_comm]; exact neg_ne_zero.2 ClosedPolygon.det_rays_ne_zero)
    D.R_pos

theorem isConnected_sectorR : IsConnected (D.sectorR i) :=
  isConnected_cone_arcCCW _ ClosedPolygon.det_rays_ne_zero D.R_pos

 





 

theorem exists_foot (h : x ∈ D.blockL i ∪ D.blockR i) :
    ∃ c ∈ Set.Icc D.lam (P.len i - D.lam), dist x (P.pt i c) < D.rho := by
  refine ⟨coordAlong (P.vertex i) (P.tang i) x, ?_, ?_⟩
  · rcases h with h | h
    · exact ⟨(D.mem_blockL_iff.1 h).1.le, (D.mem_blockL_iff.1 h).2.1.le⟩
    · exact ⟨(D.mem_blockR_iff.1 h).1.le, (D.mem_blockR_iff.1 h).2.1.le⟩
  · rw [ClosedPolygon.pt_eq, dist_foot ClosedPolygon.isDirection_tang]
    rcases h with h | h
    · obtain ⟨_, _, h1, h2⟩ := D.mem_blockL_iff.1 h
      rw [abs_of_pos h1]; exact h2
    · obtain ⟨_, _, h1, h2⟩ := D.mem_blockR_iff.1 h
      rw [abs_of_neg h2]; linarith

theorem sector_subset_ball : D.sectorL i ⊆ ball (P.vertex i) D.R := cone_subset_ball
theorem sectorR_subset_ball : D.sectorR i ⊆ ball (P.vertex i) D.R := cone_subset_ball

 






 
theorem germ_ineq {t s : ℝ} (ht : D.lam < t) (hs0 : 0 < s) (hs : s < D.rho) :
    s * |inner ℝ (P.rayIn i) (P.tang i)| < t * |det (P.rayIn i) (P.tang i)| := by
  have hd : 0 < |det (P.rayIn i) (P.tang i)| := abs_pos.2 ClosedPolygon.det_rays_ne_zero
  have habs : (0 : ℝ) ≤ |inner ℝ (P.rayIn i) (P.tang i)| := abs_nonneg _
  have h1 : s * |inner ℝ (P.rayIn i) (P.tang i)| ≤ s * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) := by
    nlinarith
  have h2 : s * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) <
      D.rho * (1 + |inner ℝ (P.rayIn i) (P.tang i)|) := by nlinarith
  have h3 := D.germ i
  nlinarith

 

theorem blockL_sub_mem_arcL_start (h : x ∈ D.blockL i) :
    x - P.vertex i ∈ arcCCW (P.tang i) (P.rayIn i) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 h
  have hx := ClosedPolygon.off_coord P i x
  rw [hx, ClosedPolygon.off_sub_vertex]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero h3 (D.germ_ineq h1 h3 h4)).1.2

 
theorem blockL_sub_mem_arcL_finish (h : x ∈ D.blockL i) :
    x - P.vertex (i + 1) ∈ arcCCW (P.tang (i + 1)) (P.rayIn (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockL_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hr : P.rayIn (i + 1) = -P.tang i := ClosedPolygon.rayIn_succ
  have hkey : x - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) - s • perp (P.rayIn (i + 1)) := by
    have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
      rw [ClosedPolygon.len_smul_tang]; module
    rw [hx, ClosedPolygon.off, hv, hr]
    have hp : perp (-P.tang i) = -perp (P.tang i) := by
      ext k; fin_cases k <;> simp [perp]
    rw [hp]
    module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero h3
    (D.germ_ineq (i := i + 1) (by linarith) h3 h4)).1.1

 

theorem blockR_sub_mem_arcR_start (h : x ∈ D.blockR i) :
    x - P.vertex i ∈ arcCCW (P.rayIn i) (P.tang i) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hkey : x - P.vertex i = t • P.tang i - (-s) • perp (P.tang i) := by
    rw [hx, ClosedPolygon.off_sub_vertex]; module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero (by linarith)
    (D.germ_ineq h1 (by linarith) (by linarith))).2.2

 
theorem blockR_sub_mem_arcR_finish (h : x ∈ D.blockR i) :
    x - P.vertex (i + 1) ∈ arcCCW (P.rayIn (i + 1)) (P.tang (i + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.mem_blockR_iff.1 h
  set t := coordAlong (P.vertex i) (P.tang i) x with ht
  set s := coordAcross (P.vertex i) (P.tang i) x with hs
  have hx : x = P.off i t s := ClosedPolygon.off_coord P i x
  have hr : P.rayIn (i + 1) = -P.tang i := ClosedPolygon.rayIn_succ
  have hkey : x - P.vertex (i + 1) =
      (P.len i - t) • P.rayIn (i + 1) + (-s) • perp (P.rayIn (i + 1)) := by
    have hv : P.vertex (i + 1) = P.vertex i + (P.len i) • P.tang i := by
      rw [ClosedPolygon.len_smul_tang]; module
    rw [hx, ClosedPolygon.off, hv, hr]
    have hp : perp (-P.tang i) = -perp (P.tang i) := by
      ext k; fin_cases k <;> simp [perp]
    rw [hp]
    module
  rw [hkey]
  exact (germs_split' ClosedPolygon.det_rays_ne_zero (by linarith)
    (D.germ_ineq (i := i + 1) (by linarith) (by linarith) (by linarith))).2.1

 




theorem pt_mem_edge_of_trim {c : ℝ} (hc : c ∈ Set.Icc D.lam (P.len i - D.lam)) :
    P.pt i c ∈ P.edge i :=
  ClosedPolygon.pt_mem_edge ⟨le_trans D.lam_pos.le hc.1, le_trans hc.2 (by linarith [D.lam_pos])⟩

 
theorem block_notMem_edge (h : x ∈ D.blockL i ∪ D.blockR i) (hj : j ≠ i) : x ∉ P.edge j := by
  intro hx
  obtain ⟨c, hc, hd⟩ := D.exists_foot h
  have := D.sep_trim_edge i j hj c hc x hx
  rw [dist_comm] at hd
  linarith [D.rho_pos]

 
theorem block_notMem_own_edge (h : x ∈ D.blockL i ∪ D.blockR i) : x ∉ P.edge i := by
  intro hx
  rw [ClosedPolygon.mem_edge_iff] at hx
  obtain ⟨c, _, rfl⟩ := hx
  have hzero : coordAcross (P.vertex i) (P.tang i) (P.pt i c) = 0 := by
    rw [ClosedPolygon.pt]; exact ClosedPolygon.coordAcross_off
  rcases h with h | h
  · have hpos := (D.mem_blockL_iff.1 h).2.2.1
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · have hneg := (D.mem_blockR_iff.1 h).2.2.2
    rw [hzero] at hneg
    exact lt_irrefl 0 hneg

theorem block_notMem_carrier (h : x ∈ D.blockL i ∪ D.blockR i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hij : j = i
  · exact D.block_notMem_own_edge h (hij ▸ hj)
  · exact D.block_notMem_edge h hij hj

 
theorem block_notMem_ball_vertex (h : x ∈ D.blockL i ∪ D.blockR i) (hj1 : j ≠ i)
    (hj2 : j ≠ i + 1) : x ∉ ball (P.vertex j) D.R := by
  intro hx
  obtain ⟨c, hc, hd⟩ := D.exists_foot h
  have hne1 : i ≠ j - 1 := fun he => hj2 (by rw [he]; ring)
  have := D.sep_vertex_edge j i hne1 (Ne.symm hj1) _ (D.pt_mem_edge_of_trim hc)
  have h1 : dist (P.vertex j) (P.pt i c) ≤ dist (P.vertex j) x + dist x (P.pt i c) :=
    dist_triangle _ _ _
  rw [mem_ball] at hx
  rw [dist_comm] at hx
  linarith [D.rho_lt_R]

 
theorem sector_notMem_far_edge (h : x ∈ ball (P.vertex i) D.R) (hj1 : j ≠ i - 1) (hj2 : j ≠ i) :
    x ∉ P.edge j := by
  intro hx
  have := D.sep_vertex_edge i j hj1 hj2 x hx
  rw [mem_ball, dist_comm] at h
  linarith [D.R_pos]

 

theorem sectorL_notMem_carrier (h : x ∈ D.sectorL i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · rw [hji] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_sub hj
    exact ((notMem_arcCCW_smul (P.tang i) (P.rayIn i) hc).1) (he ▸ h.1)
  by_cases hjp : j = i - 1
  · rw [hjp] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_pred_sub (i := i) hj
    exact ((notMem_arcCCW_smul (P.rayIn i) (P.tang i) hc).2) (he ▸ h.1)
  · exact D.sector_notMem_far_edge (i := i) h.2 hjp hji hj

theorem sectorR_notMem_carrier (h : x ∈ D.sectorR i) : x ∉ P.carrier := by
  rintro hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · rw [hji] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_sub hj
    exact ((notMem_arcCCW_smul (P.tang i) (P.rayIn i) hc).2) (he ▸ h.1)
  by_cases hjp : j = i - 1
  · rw [hjp] at hj
    obtain ⟨c, hc, he⟩ := ClosedPolygon.mem_edge_pred_sub (i := i) hj
    exact ((notMem_arcCCW_smul (P.rayIn i) (P.tang i) hc).1) (he ▸ h.1)
  · exact D.sector_notMem_far_edge (i := i) h.2 hjp hji hj

theorem sideL_disjoint_carrier : Disjoint D.sideL P.carrier := by
  rw [Set.disjoint_left]
  rintro y hy hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rcases hi with hi | hi
  · exact D.sectorL_notMem_carrier hi hc
  · exact D.block_notMem_carrier (Or.inl hi) hc

theorem sideR_disjoint_carrier : Disjoint D.sideR P.carrier := by
  rw [Set.disjoint_left]
  rintro y hy hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  rcases hi with hi | hi
  · exact D.sectorR_notMem_carrier hi hc
  · exact D.block_notMem_carrier (Or.inr hi) hc

 




theorem blockL_disjoint_blockR (hL : x ∈ D.blockL i) (hR : x ∈ D.blockR j) : False := by
  by_cases hij : j = i
  · rw [hij] at hR
    exact absurd (D.mem_blockL_iff.1 hL).2.2.1 (asymm (D.mem_blockR_iff.1 hR).2.2.2)
  · obtain ⟨c, hc, hd⟩ := D.exists_foot (Or.inl hL)
    obtain ⟨c', hc', hd'⟩ := D.exists_foot (Or.inr hR)
    have hsep := D.sep_trim_edge i j hij c hc _ (D.pt_mem_edge_of_trim hc')
    have h1 : dist (P.pt i c) (P.pt j c') ≤ dist (P.pt i c) x + dist x (P.pt j c') :=
      dist_triangle _ _ _
    rw [dist_comm] at hd
    linarith

theorem blockL_disjoint_sectorR (hL : x ∈ D.blockL i) (hR : x ∈ D.sectorR j) : False := by
  by_cases hij : j = i
  · subst hij
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := j))).ne_of_mem
      hR.1 (D.blockL_sub_mem_arcL_start hL) rfl
  by_cases hij2 : j = i + 1
  · subst hij2
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i + 1))).ne_of_mem
      hR.1 (D.blockL_sub_mem_arcL_finish hL) rfl
  · exact D.block_notMem_ball_vertex (Or.inl hL) hij hij2 hR.2

theorem sectorL_disjoint_blockR (hL : x ∈ D.sectorL i) (hR : x ∈ D.blockR j) : False := by
  by_cases hij : i = j
  · subst hij
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i))).ne_of_mem
      (D.blockR_sub_mem_arcR_start hR) hL.1 rfl
  by_cases hij2 : i = j + 1
  · subst hij2
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := j + 1))).ne_of_mem
      (D.blockR_sub_mem_arcR_finish hR) hL.1 rfl
  · exact D.block_notMem_ball_vertex (Or.inr hR) hij hij2 hL.2

theorem sectorL_disjoint_sectorR (hL : x ∈ D.sectorL i) (hR : x ∈ D.sectorR j) : False := by
  by_cases hij : i = j
  · subst hij
    exact (arcCCW_disjoint' (ClosedPolygon.det_rays_ne_zero (P := P) (i := i))).ne_of_mem
      hR.1 hL.1 rfl
  · have hsep := D.sep_vertex i j hij
    have hdL : dist x (P.vertex i) < D.R := hL.2
    have hdR : dist x (P.vertex j) < D.R := hR.2
    have h1 : dist (P.vertex i) (P.vertex j) ≤ dist (P.vertex i) x + dist x (P.vertex j) :=
      dist_triangle _ _ _
    rw [dist_comm (P.vertex i) x] at h1
    linarith

theorem sideL_disjoint_sideR : Disjoint D.sideL D.sideR := by
  rw [Set.disjoint_left]
  rintro y hy hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hz
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact D.sectorL_disjoint_sectorR hi hj
  · exact D.sectorL_disjoint_blockR hi hj
  · exact D.blockL_disjoint_sectorR hi hj
  · exact D.blockL_disjoint_blockR hi hj

end StripData

end Schoenflies
