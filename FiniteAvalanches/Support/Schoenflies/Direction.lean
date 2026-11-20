/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Direction.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Plane

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 
























































open Set

namespace Schoenflies

namespace Plane

variable {u w d d₁ d₂ r₁ r₂ v : Plane} {r t s : ℝ}

 

 

def IsDirection (u : Plane) : Prop := ‖u‖ = 1

theorem IsDirection.ne_zero (hu : IsDirection u) : u ≠ 0 := by
  intro h
  rw [IsDirection, h, norm_zero] at hu
  exact zero_ne_one hu

theorem IsDirection.norm (hu : IsDirection u) : ‖u‖ = 1 := hu

 
noncomputable def dir (u : Plane) : Plane := ‖u‖⁻¹ • u

theorem isDirection_dir (hu : u ≠ 0) : IsDirection (dir u) := by
  have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [IsDirection, dir, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

theorem dir_ne_zero (hu : u ≠ 0) : dir u ≠ 0 := (isDirection_dir hu).ne_zero

 

theorem dir_eq_smul (hu : u ≠ 0) : ∃ c : ℝ, 0 < c ∧ dir u = c • u :=
  ⟨‖u‖⁻¹, inv_pos.2 (norm_pos_iff.2 hu), rfl⟩

 

theorem ne_zero_left_of_det_ne_zero (h : det u w ≠ 0) : u ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

theorem ne_zero_right_of_det_ne_zero (h : det u w ≠ 0) : w ≠ 0 := by
  rintro rfl
  exact h (by simp [det])

 

theorem det_ne_zero_iff (hu : IsDirection u) (hw : IsDirection w) :
    det u w ≠ 0 ↔ w ≠ u ∧ w ≠ -u := by
  constructor
  · intro h
    refine ⟨fun he => h (by rw [he]; simp), fun he => h ?_⟩
    rw [he, show (-u : Plane) = (-1 : ℝ) • u by module, det_smul_right, det_self, mul_zero]
  · rintro ⟨hne, hopp⟩ h
    
    obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul u w hu.ne_zero).1 h
    have hc : |c| = 1 := by
      have := hw.norm
      rwa [norm_smul, Real.norm_eq_abs, hu.norm, mul_one] at this
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hc with rfl | rfl
    · exact hne (one_smul ℝ u)
    · exact hopp (by module)

 

 




def arcCCW (u w : Plane) : Set Plane :=
  {d | (0 < det u d ∧ 0 < det d w) ∨ (0 < det d w ∧ 0 < det w u) ∨ (0 < det w u ∧ 0 < det u d)}

 


theorem mem_arcCCW_iff (h : 0 < det u w) : d ∈ arcCCW u w ↔ 0 < det u d ∧ 0 < det d w := by
  have hwu : det w u < 0 := by rw [det_comm w u]; linarith
  refine ⟨?_, Or.inl⟩
  rintro (h1 | ⟨_, h2⟩ | ⟨h2, _⟩)
  · exact h1
  · linarith
  · linarith

 


theorem mem_arcCCW_rev_iff (h : 0 < det u w) :
    d ∈ arcCCW w u ↔ det u d < 0 ∨ det d w < 0 := by
  have e1 : det w d = -det d w := det_comm w d
  have e2 : det d u = -det u d := det_comm d u
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h2, _⟩ | ⟨_, h1⟩)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inl (by rw [e2] at h2; linarith)
    · exact Or.inr (by rw [e1] at h1; linarith)
  · rintro (h1 | h2)
    · exact Or.inr (Or.inl ⟨by rw [e2]; linarith, h⟩)
    · exact Or.inr (Or.inr ⟨h, by rw [e1]; linarith⟩)

 
theorem arcCCW_disjoint (h : 0 < det u w) : Disjoint (arcCCW u w) (arcCCW w u) := by
  rw [Set.disjoint_left]
  intro d hd hd'
  rw [mem_arcCCW_iff h] at hd
  rw [mem_arcCCW_rev_iff h] at hd'
  rcases hd' with h' | h' <;> linarith [hd.1, hd.2]

 

theorem smul_mem_arcCCW (hr : 0 < r) : r • d ∈ arcCCW u w ↔ d ∈ arcCCW u w := by
  have key : ∀ x : ℝ, 0 < r * x ↔ 0 < x := by
    intro x
    constructor <;> intro hx <;> nlinarith
  simp only [arcCCW, mem_setOf_eq, det_smul_left, det_smul_right, key]

theorem dir_mem_arcCCW_iff (hd : d ≠ 0) : dir d ∈ arcCCW u w ↔ d ∈ arcCCW u w := by
  obtain ⟨c, hc, hcd⟩ := dir_eq_smul hd
  rw [hcd, smul_mem_arcCCW hc]

 


theorem mem_ray_or_mem_arcCCW (h : 0 < det u w) (hd : d ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ d = c • u) ∨ (∃ c : ℝ, 0 < c ∧ d = c • w) ∨
      d ∈ arcCCW u w ∨ d ∈ arcCCW w u := by
  have hu : u ≠ 0 := ne_zero_left_of_det_ne_zero h.ne'
  have hw : w ≠ 0 := ne_zero_right_of_det_ne_zero h.ne'
  by_cases hneg : det u d < 0 ∨ det d w < 0
  · exact Or.inr (Or.inr (Or.inr ((mem_arcCCW_rev_iff h).2 hneg)))
  push Not at hneg
  obtain ⟨h1, h2⟩ := hneg
  rcases lt_or_eq_of_le h1 with h1' | h1'
  · rcases lt_or_eq_of_le h2 with h2' | h2'
    · exact Or.inr (Or.inr (Or.inl ((mem_arcCCW_iff h).2 ⟨h1', h2'⟩)))
    · 
      obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul w d hw).1 (by rw [det_comm w d, ← h2']; ring)
      refine Or.inr (Or.inl ⟨c, ?_, rfl⟩)
      rw [det_smul_right] at h1'
      nlinarith
  · 
    obtain ⟨c, rfl⟩ := (det_eq_zero_iff_smul u d hu).1 h1'.symm
    refine Or.inl ⟨c, ?_, rfl⟩
    rw [det_smul_left] at h2
    rcases lt_or_eq_of_le h2 with h2' | h2'
    · nlinarith
    · exfalso
      have : c = 0 := by
        rcases mul_eq_zero.1 h2'.symm with hc | hd'
        · exact hc
        · exact absurd hd' h.ne'
      exact hd (by rw [this, zero_smul])

 

 

theorem mem_arcCCW_rev_of_det_neg (h : 0 < det u w) (hd : det u d < 0) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inl hd)

 

theorem mem_arcCCW_rev_of_det_pos (h : 0 < det u w) (hd : 0 < det w d) : d ∈ arcCCW w u :=
  (mem_arcCCW_rev_iff h).2 (Or.inr (by rw [det_comm d w]; linarith))

 


theorem same_arc_of_det_neg_of_det_pos (h : 0 < det u w) (h₁ : det u d₁ < 0) (h₂ : 0 < det w d₂) :
    d₁ ∈ arcCCW w u ∧ d₂ ∈ arcCCW w u :=
  ⟨mem_arcCCW_rev_of_det_neg h h₁, mem_arcCCW_rev_of_det_pos h h₂⟩

 


theorem mem_arcCCW_of_det_pos_of_det_neg (h : 0 < det u w) (h₁ : 0 < det u d) (h₂ : det w d < 0) :
    d ∈ arcCCW u w :=
  (mem_arcCCW_iff h).2 ⟨h₁, by rw [det_comm d w]; linarith⟩

 












 

theorem det_germ_self (r : Plane) (t s : ℝ) :
    det r (t • r + s • perp r) = s * ‖r‖ ^ 2 := by
  rw [det_add_right, det_smul_right, det_smul_right, det_self, det_perp_self]
  ring

theorem det_germ_self' (r : Plane) (t s : ℝ) :
    det (t • r + s • perp r) r = -(s * ‖r‖ ^ 2) := by
  rw [det_comm, det_germ_self]

 

theorem det_germ (r₁ r₂ : Plane) (t s : ℝ) :
    det (t • r₁ + s • perp r₁) r₂ = t * det r₁ r₂ - s * inner ℝ r₁ r₂ := by
  rw [det_add_left, det_smul_left, det_smul_left, det_perp_left]
  ring

 
theorem det_germ' (r₁ r₂ : Plane) (t s : ℝ) :
    det r₁ (t • r₂ + s • perp r₂) = t * det r₁ r₂ + s * inner ℝ r₁ r₂ := by
  rw [det_add_right, det_smul_right, det_smul_right, det_perp_right]

private theorem sq_norm_pos_left (h : 0 < det r₁ r₂) : 0 < ‖r₁‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_left_of_det_ne_zero h.ne')) 2

private theorem sq_norm_pos_right (h : 0 < det r₁ r₂) : 0 < ‖r₂‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (ne_zero_right_of_det_ne_zero h.ne')) 2

 


theorem germ_mem_arcCCW_rev_of_left (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_neg h ?_
  have e : t • r₁ - s • perp r₁ = t • r₁ + (-s) • perp r₁ := by module
  rw [e, det_germ_self]
  nlinarith [sq_norm_pos_left h]

 
theorem germ_mem_arcCCW_rev_of_right (h : 0 < det r₁ r₂) (hs : 0 < s) (t : ℝ) :
    t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁ := by
  refine mem_arcCCW_rev_of_det_pos h ?_
  rw [det_germ_self]
  exact mul_pos hs (sq_norm_pos_right h)

 


theorem germ_mem_arcCCW_of_left (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ := by
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [det_germ_self]
    exact mul_pos hs (sq_norm_pos_left h)
  · rw [det_germ]
    linarith

 
theorem germ_mem_arcCCW_of_right (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂ := by
  have e : t • r₂ - s • perp r₂ = t • r₂ + (-s) • perp r₂ := by module
  refine (mem_arcCCW_iff h).2 ⟨?_, ?_⟩
  · rw [e, det_germ']
    linarith
  · rw [e, det_germ_self']
    nlinarith [sq_norm_pos_right h]

 




theorem germs_split (h : 0 < det r₁ r₂) (hs : 0 < s)
    (hsmall : s * inner ℝ r₁ r₂ < t * det r₁ r₂) :
    (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
      (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) :=
  ⟨⟨germ_mem_arcCCW_rev_of_left h hs t, germ_mem_arcCCW_rev_of_right h hs t⟩,
    ⟨germ_mem_arcCCW_of_left h hs hsmall, germ_mem_arcCCW_of_right h hs hsmall⟩⟩

 



theorem exists_germ_threshold (h : 0 < det r₁ r₂) :
    ∃ ε > 0, ∀ t s : ℝ, 0 < t → 0 < s → s < ε * t →
      (t • r₁ - s • perp r₁ ∈ arcCCW r₂ r₁ ∧ t • r₂ + s • perp r₂ ∈ arcCCW r₂ r₁) ∧
        (t • r₁ + s • perp r₁ ∈ arcCCW r₁ r₂ ∧ t • r₂ - s • perp r₂ ∈ arcCCW r₁ r₂) := by
  set A : ℝ := |inner ℝ r₁ r₂| with hA
  have hA0 : (0 : ℝ) < 1 + A := by positivity
  refine ⟨det r₁ r₂ / (1 + A), by positivity, fun t s _ hs hlt => germs_split h hs ?_⟩
  
  have hmul := mul_lt_mul_of_pos_right hlt hA0
  have hclear : det r₁ r₂ / (1 + A) * t * (1 + A) = det r₁ r₂ * t := by
    field_simp
  rw [hclear] at hmul
  have hle : inner ℝ r₁ r₂ ≤ A := le_abs_self _
  nlinarith

 





 
private theorem mk_one_ne_zero (a : ℝ) : mk 1 a ≠ 0 := by
  intro h
  have h0 : mk 1 a 0 = (0 : Plane) 0 := by rw [h]
  simp at h0

private theorem det_mk_one (a : ℝ) (v : Plane) : det (mk 1 a) v = v 1 - a * v 0 := by
  simp [det]

 


theorem exists_isDirection_det_ne_zero {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, IsDirection u ∧ ∀ v ∈ S, v ≠ 0 → det u v ≠ 0 := by
  
  have hbad : {a : ℝ | ∃ v ∈ S, v ≠ 0 ∧ det (mk 1 a) v = 0}.Finite := by
    refine Set.Finite.subset (hS.image fun v => v 1 / v 0) ?_
    rintro a ⟨v, hv, hv0, hdet⟩
    rw [det_mk_one] at hdet
    have h0 : v 0 ≠ 0 := by
      intro h
      refine hv0 ?_
      have h1 : v 1 = 0 := by rw [h] at hdet; linarith
      ext i
      fin_cases i <;> simp [h, h1]
    exact ⟨v, hv, by field_simp; linarith⟩
  obtain ⟨a, ha⟩ := hbad.infinite_compl.nonempty
  refine ⟨dir (mk 1 a), isDirection_dir (mk_one_ne_zero a),
    fun v hv hv0 hdet => ha ⟨v, hv, hv0, ?_⟩⟩
  
  obtain ⟨c, hc, hcd⟩ := dir_eq_smul (mk_one_ne_zero a)
  rw [hcd, det_smul_left] at hdet
  rcases mul_eq_zero.1 hdet with h | h
  · exact absurd h hc.ne'
  · exact h

 


theorem exists_isDirection_det_and_inner_ne_zero {S : Set Plane} (hS : S.Finite) :
    ∃ u : Plane, IsDirection u ∧ ∀ v ∈ S, v ≠ 0 → det u v ≠ 0 ∧ inner ℝ u v ≠ 0 := by
  obtain ⟨u, hu, hdet⟩ := exists_isDirection_det_ne_zero (hS.union (hS.image perp))
  refine ⟨u, hu, fun v hv hv0 => ⟨hdet v (Or.inl hv) hv0, ?_⟩⟩
  
  have hpv : perp v ≠ 0 := by
    intro h
    exact hv0 (by have := norm_perp v; rw [h, norm_zero] at this; exact norm_eq_zero.1 this.symm)
  have := hdet (perp v) (Or.inr ⟨v, hv, rfl⟩) hpv
  rwa [det_perp_right] at this

 




theorem continuous_det_right (u : Plane) : Continuous fun d : Plane => det u d := by
  refine Continuous.sub (Continuous.mul continuous_const ?_) (Continuous.mul continuous_const ?_)
  · exact PiLp.continuous_apply _ _ 1
  · exact PiLp.continuous_apply _ _ 0

theorem continuous_det_left (w : Plane) : Continuous fun d : Plane => det d w := by
  refine Continuous.sub (Continuous.mul ?_ continuous_const) (Continuous.mul ?_ continuous_const)
  · exact PiLp.continuous_apply _ _ 0
  · exact PiLp.continuous_apply _ _ 1

theorem isOpen_arcCCW (u w : Plane) : IsOpen (arcCCW u w) := by
  have h1 : IsOpen {d : Plane | 0 < det u d} := isOpen_lt continuous_const (continuous_det_right u)
  have h2 : IsOpen {d : Plane | 0 < det d w} := isOpen_lt continuous_const (continuous_det_left w)
  by_cases h : 0 < det w u
  · have : arcCCW u w = {d : Plane | 0 < det u d} ∪ {d : Plane | 0 < det d w} := by
      ext d
      simp only [arcCCW, mem_setOf_eq, mem_union]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h2, _⟩ | ⟨_, h1⟩) <;> tauto
      · rintro (hx | hx)
        · exact Or.inr (Or.inr ⟨h, hx⟩)
        · exact Or.inr (Or.inl ⟨hx, h⟩)
    rw [this]
    exact h1.union h2
  · have : arcCCW u w = {d : Plane | 0 < det u d} ∩ {d : Plane | 0 < det d w} := by
      ext d
      simp only [arcCCW, mem_setOf_eq, mem_inter_iff]
      constructor
      · rintro (hx | ⟨_, hx⟩ | ⟨hx, _⟩) <;> [exact hx; exact absurd hx h; exact absurd hx h]
      · exact Or.inl
    rw [this]
    exact h1.inter h2

end Plane

end Schoenflies
