/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/SquareMover.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Square

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 









































open Metric Set

namespace Schoenflies

namespace Plane

 

 


noncomputable def tent (r p u : ℝ) : ℝ := min ((u + r) / (p + r)) ((r - u) / (r - p))

variable {r p q u : ℝ}

theorem continuous_tent (r p : ℝ) : Continuous (tent r p) := by
  unfold tent; fun_prop

theorem pos_of_lt_lt (h₁ : -r < p) (h₂ : p < r) : 0 < r := by linarith

theorem tent_le_one (h₁ : -r < p) (h₂ : p < r) (u : ℝ) : tent r p u ≤ 1 := by
  rcases le_total u p with h | h
  · exact le_trans (min_le_left _ _) (by rw [div_le_one (by linarith)]; linarith)
  · exact le_trans (min_le_right _ _) (by rw [div_le_one (by linarith)]; linarith)

theorem tent_nonneg (h₁ : -r < p) (h₂ : p < r) (hu : -r ≤ u) (hu' : u ≤ r) :
    0 ≤ tent r p u :=
  le_min (div_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith))

@[simp] theorem tent_self (h₁ : -r < p) (h₂ : p < r) : tent r p p = 1 := by
  rw [tent, div_self (by linarith), div_self (by linarith), min_self]

theorem tent_left (h₁ : -r < p) (h₂ : p < r) : tent r p (-r) = 0 := by
  have hr : 0 < r := pos_of_lt_lt h₁ h₂
  rw [tent, show -r + r = 0 by ring, zero_div]
  exact min_eq_left (div_nonneg (by linarith) (by linarith))

theorem tent_right (h₁ : -r < p) (h₂ : p < r) : tent r p r = 0 := by
  have hr : 0 < r := pos_of_lt_lt h₁ h₂
  rw [tent, show r - r = 0 by ring, zero_div]
  exact min_eq_right (div_nonneg (by linarith) (by linarith))

 

 

noncomputable def bend (r p q u : ℝ) : ℝ :=
  if u ≤ p then -r + (u + r) * (q + r) / (p + r) else r - (r - u) * (r - q) / (r - p)

theorem bend_of_le (h : u ≤ p) : bend r p q u = -r + (u + r) * (q + r) / (p + r) := if_pos h

theorem bend_of_gt (h : p < u) : bend r p q u = r - (r - u) * (r - q) / (r - p) :=
  if_neg (not_le.2 h)

theorem bend_left (h : -r ≤ p) : bend r p q (-r) = -r := by
  rw [bend_of_le h]; simp

theorem bend_right (h : p < r) : bend r p q r = r := by
  rw [bend_of_gt h]; simp

theorem bend_self (h : -r < p) : bend r p q p = q := by
  have hp : p + r ≠ 0 := by linarith
  rw [bend_of_le le_rfl, mul_comm, mul_div_assoc, div_self hp, mul_one]; ring

theorem bend_refl (h₁ : -r < p) (h₂ : p < r) (u : ℝ) : bend r p p u = u := by
  rcases le_or_gt u p with h | h
  · rw [bend_of_le h, mul_div_assoc, div_self (by linarith : p + r ≠ 0), mul_one]; ring
  · rw [bend_of_gt h, mul_div_assoc, div_self (by linarith : r - p ≠ 0), mul_one]; ring

 
theorem bend_le_of_le (h₁ : -r < p) (h₂ : -r < q) (h : u ≤ p) : bend r p q u ≤ q := by
  rw [bend_of_le h]
  have : (u + r) * (q + r) / (p + r) ≤ q + r := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

 
theorem lt_bend_of_lt (h₁ : p < r) (h₂ : q < r) (h : p < u) : q < bend r p q u := by
  rw [bend_of_gt h]
  have : (r - u) * (r - q) / (r - p) < r - q := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

 
theorem bend_mem (h₁ : -r < p) (h₂ : p < r) (h₃ : -r < q) (h₄ : q < r) (hu : -r ≤ u)
    (hu' : u ≤ r) : -r ≤ bend r p q u ∧ bend r p q u ≤ r := by
  rcases le_or_gt u p with h | h
  · refine ⟨?_, le_of_lt (lt_of_le_of_lt (bend_le_of_le h₁ h₃ h) h₄)⟩
    rw [bend_of_le h]
    have : 0 ≤ (u + r) * (q + r) / (p + r) := div_nonneg (by nlinarith) (by linarith)
    linarith
  · refine ⟨le_of_lt (lt_trans h₃ (lt_bend_of_lt h₂ h₄ h)), ?_⟩
    rw [bend_of_gt h]
    have : 0 ≤ (r - u) * (r - q) / (r - p) := div_nonneg (by nlinarith) (by linarith)
    linarith

 
theorem bend_bend (h₁ : -r < p) (h₂ : p < r) (h₃ : -r < q) (h₄ : q < r) (u : ℝ) :
    bend r q p (bend r p q u) = u := by
  rcases le_or_gt u p with h | h
  · have hp : p + r ≠ 0 := by linarith
    have hq : q + r ≠ 0 := by linarith
    rw [bend_of_le (bend_le_of_le h₁ h₃ h), bend_of_le h]
    field_simp
    ring
  · have hp : r - p ≠ 0 := by linarith
    have hq : r - q ≠ 0 := by linarith
    rw [bend_of_gt (lt_bend_of_lt h₂ h₄ h), bend_of_gt h]
    field_simp
    ring

 

theorem bend_eq_right (h₁ : p + r ≠ 0) (h₂ : r - p ≠ 0) (h : p ≤ u) :
    bend r p q u = r - (r - u) * (r - q) / (r - p) := by
  rcases eq_or_lt_of_le h with rfl | h'
  · rw [bend_of_le le_rfl]
    field_simp
    ring
  · exact bend_of_gt h'

 


theorem continuousOn_bend (r : ℝ) {s : Set Plane} {P Q U : Plane → ℝ} (hs : IsClosed s)
    (hP : Continuous P) (hQ : Continuous Q) (hU : Continuous U)
    (h1 : ∀ z ∈ s, P z + r ≠ 0) (h2 : ∀ z ∈ s, r - P z ≠ 0) :
    ContinuousOn (fun z => bend r (P z) (Q z) (U z)) s := by
  have hcover : s = (s ∩ {z | U z ≤ P z}) ∪ (s ∩ {z | P z ≤ U z}) := by
    ext z
    constructor
    · intro hz
      rcases le_total (U z) (P z) with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
  rw [hcover]
  refine (continuousOn_union_iff_of_isClosed (hs.inter (isClosed_le hU hP))
    (hs.inter (isClosed_le hP hU))).2 ⟨?_, ?_⟩
  · refine ContinuousOn.congr (f := fun z => -r + (U z + r) * (Q z + r) / (P z + r)) ?_ ?_
    · exact continuousOn_const.add
        (((hU.continuousOn.add continuousOn_const).mul
          (hQ.continuousOn.add continuousOn_const)).div
            (hP.continuousOn.add continuousOn_const) fun z hz => h1 z hz.1)
    · exact fun z hz => bend_of_le hz.2
  · refine ContinuousOn.congr (f := fun z => r - (r - U z) * (r - Q z) / (r - P z)) ?_ ?_
    · exact continuousOn_const.sub
        (((continuousOn_const.sub hU.continuousOn).mul
          (continuousOn_const.sub hQ.continuousOn)).div
            (continuousOn_const.sub hP.continuousOn) fun z hz => h2 z hz.1)
    · exact fun z hz => bend_eq_right (h1 z hz.1) (h2 z hz.1) hz.2

 

 
theorem abs_sub_le_supDist (z c : Plane) (l : Fin 2) : |z l - c l| ≤ supDist z c := by
  fin_cases l
  · exact abs_sub_zero_le_supDist z c
  · exact abs_sub_one_le_supDist z c

 
theorem supDist_le_of_forall {z c : Plane} {r : ℝ} (h : ∀ l : Fin 2, |z l - c l| ≤ r) :
    supDist z c ≤ r :=
  max_le (h 0) (h 1)

 
theorem exists_abs_sub_eq_of_supDist_eq {z c : Plane} {r : ℝ} (h : supDist z c = r) :
    ∃ l : Fin 2, |z l - c l| = r := by
  rcases max_choice |z 0 - c 0| |z 1 - c 1| with hm | hm
  · exact ⟨0, by rw [← h]; exact hm.symm⟩
  · exact ⟨1, by rw [← h]; exact hm.symm⟩

theorem abs_sub_lt_of_mem_openSquare {z c : Plane} {r : ℝ} (hz : z ∈ openSquare c r)
    (l : Fin 2) : |z l - c l| < r :=
  lt_of_le_of_lt (abs_sub_le_supDist z c l) hz

 
theorem mem_Ioo_of_mem_openSquare {z c : Plane} {r : ℝ} (hz : z ∈ openSquare c r) (l : Fin 2) :
    z l - c l ∈ Ioo (-r) r := by
  have := abs_sub_lt_of_mem_openSquare hz l
  rw [abs_lt] at this
  exact ⟨this.1, this.2⟩

 
theorem fin2_eq_of_ne_of_ne {i j l : Fin 2} (h₁ : j ≠ i) (h₂ : l ≠ i) : l = j := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all

 

 

noncomputable def shearWeight (c : Plane) (r b : ℝ) (j : Fin 2) (z : Plane) : ℝ :=
  tent r b (z j - c j)

 





noncomputable def shear (c : Plane) (r a b k k' : ℝ) (i j : Fin 2) (z : Plane) : Plane :=
  z + (bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
    (z i - c i) - (z i - c i)) • EuclideanSpace.single i (1 : ℝ)

 

structure IsShear (r a b k k' : ℝ) : Prop where
   
  peak : b ∈ Ioo (-r) r
   
  base : a ∈ Ioo (-r) r
   
  mid : a + k ∈ Ioo (-r) r
   
  top : a + (k + k') ∈ Ioo (-r) r

variable {c : Plane} {a b k k' : ℝ} {i j l : Fin 2} {z : Plane}

 
theorem IsShear.inv (h : IsShear r a b k k') : IsShear r a b (k + k') (-k') where
  peak := h.peak
  base := h.base
  mid := h.top
  top := by rw [show k + k' + -k' = k by ring]; exact h.mid

theorem shear_apply_same :
    shear c r a b k k' i j z i =
      c i + bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
        (z i - c i) := by
  simp only [shear, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
    if_true, mul_one]
  ring

theorem shear_apply_ne (h : l ≠ i) : shear c r a b k k' i j z l = z l := by
  simp [shear, h]

 
theorem mem_Ioo_of_weight {w : ℝ} (ha : a ∈ Ioo (-r) r) (hak : a + k ∈ Ioo (-r) r)
    (hw : w ∈ Icc (0 : ℝ) 1) : a + k * w ∈ Ioo (-r) r := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hak
  obtain ⟨h5, h6⟩ := hw
  rcases eq_or_lt_of_le h5 with rfl | hw0
  · simpa using ⟨h1, h2⟩
  · constructor
    · nlinarith [mul_pos hw0 (show (0:ℝ) < a + k + r by linarith),
        mul_nonneg (show (0:ℝ) ≤ 1 - w by linarith) (show (0:ℝ) ≤ a + r by linarith)]
    · nlinarith [mul_pos hw0 (show (0:ℝ) < r - a - k by linarith),
        mul_nonneg (show (0:ℝ) ≤ 1 - w by linarith) (show (0:ℝ) ≤ r - a by linarith)]

 
theorem shearWeight_mem (h : IsShear r a b k k') (hz : z ∈ closedSquare c r) :
    shearWeight c r b j z ∈ Icc (0 : ℝ) 1 := by
  have hb := abs_sub_le_supDist z c j
  have : |z j - c j| ≤ r := le_trans hb hz
  rw [abs_le] at this
  exact ⟨tent_nonneg h.peak.1 h.peak.2 this.1 this.2, tent_le_one h.peak.1 h.peak.2 _⟩

 
theorem shear_mid_mem (h : IsShear r a b k k') (hz : z ∈ closedSquare c r) :
    a + k * shearWeight c r b j z ∈ Ioo (-r) r :=
  mem_Ioo_of_weight h.base h.mid (shearWeight_mem h hz)

 
theorem shear_top_mem (h : IsShear r a b k k') (hz : z ∈ closedSquare c r) :
    a + (k + k') * shearWeight c r b j z ∈ Ioo (-r) r :=
  mem_Ioo_of_weight h.base h.top (shearWeight_mem h hz)

 
theorem shear_mapsTo (h : IsShear r a b k k') (i j : Fin 2) :
    MapsTo (shear c r a b k k' i j) (closedSquare c r) (closedSquare c r) := by
  intro z hz
  refine supDist_le_of_forall fun l => ?_
  by_cases hl : l = i
  · subst hl
    rw [shear_apply_same]
    have hu : |z l - c l| ≤ r := le_trans (abs_sub_le_supDist z c l) hz
    rw [abs_le] at hu
    have := bend_mem (shear_mid_mem (j := j) h hz).1 (shear_mid_mem (j := j) h hz).2
      (shear_top_mem (j := j) h hz).1 (shear_top_mem (j := j) h hz).2 hu.1 hu.2
    rw [show c l + bend r (a + k * shearWeight c r b j z)
      (a + (k + k') * shearWeight c r b j z) (z l - c l) - c l
      = bend r (a + k * shearWeight c r b j z)
        (a + (k + k') * shearWeight c r b j z) (z l - c l) by ring, abs_le]
    exact this
  · rw [shear_apply_ne hl]
    exact le_trans (abs_sub_le_supDist z c l) hz

 
theorem shear_shear (h : IsShear r a b k k') (hij : j ≠ i) (hz : z ∈ closedSquare c r) :
    shear c r a b (k + k') (-k') i j (shear c r a b k k' i j z) = z := by
  have hweight : shearWeight c r b j (shear c r a b k k' i j z) = shearWeight c r b j z := by
    rw [shearWeight, shearWeight, shear_apply_ne hij]
  ext l
  by_cases hl : l = i
  · subst hl
    rw [shear_apply_same, hweight, shear_apply_same, show
      c l + bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
        (z l - c l) - c l
      = bend r (a + k * shearWeight c r b j z) (a + (k + k') * shearWeight c r b j z)
        (z l - c l) by ring, show k + k' + -k' = k by ring]
    rw [bend_bend (shear_mid_mem (j := j) h hz).1 (shear_mid_mem (j := j) h hz).2
      (shear_top_mem (j := j) h hz).1 (shear_top_mem (j := j) h hz).2]
    ring
  · rw [shear_apply_ne hl, shear_apply_ne hl]

 
theorem shear_eq_self_of_boundary (h : IsShear r a b k k') (hij : j ≠ i)
    (hz : z ∈ closedSquare c r) (hbd : supDist z c = r) : shear c r a b k k' i j z = z := by
  have hr : 0 < r := pos_of_lt_lt h.peak.1 h.peak.2
  obtain ⟨m, hm⟩ := exists_abs_sub_eq_of_supDist_eq hbd
  ext l
  by_cases hl : l = i
  · subst hl
    rw [shear_apply_same]
    by_cases hml : m = l
    · 
      subst hml
      rcases (abs_eq hr.le).1 hm with he | he
      · rw [he, bend_right (shear_mid_mem (j := j) h hz).2]
        linarith
      · rw [he, bend_left (shear_mid_mem (j := j) h hz).1.le]
        linarith
    · 
      have hmj : m = j := fin2_eq_of_ne_of_ne hij hml
      subst hmj
      have hw : shearWeight c r b m z = 0 := by
        rcases (abs_eq hr.le).1 hm with he | he
        · rw [shearWeight, he]; exact tent_right h.peak.1 h.peak.2
        · rw [shearWeight, show z m - c m = -r by linarith [he]]
          exact tent_left h.peak.1 h.peak.2
      rw [hw]
      simp only [mul_zero, add_zero]
      rw [bend_refl h.base.1 h.base.2]
      ring
  · rw [shear_apply_ne hl]

 
theorem shear_continuousOn (h : IsShear r a b k k') (i j : Fin 2) :
    ContinuousOn (shear c r a b k k' i j) (closedSquare c r) := by
  have hW : Continuous fun z : Plane => shearWeight c r b j z :=
    (continuous_tent r b).comp ((continuous_coord j).sub continuous_const)
  have hU : Continuous fun z : Plane => z i - c i := (continuous_coord i).sub continuous_const
  have hP : Continuous fun z : Plane => a + k * shearWeight c r b j z :=
    continuous_const.add (continuous_const.mul hW)
  have hQ : Continuous fun z : Plane => a + (k + k') * shearWeight c r b j z :=
    continuous_const.add (continuous_const.mul hW)
  have hbend := continuousOn_bend r (s := closedSquare c r) (isClosed_closedSquare c r) hP hQ hU
    (fun z hz => by linarith [(shear_mid_mem (j := j) h hz).1])
    (fun z hz => by linarith [(shear_mid_mem (j := j) h hz).2])
  exact continuous_id.continuousOn.add ((hbend.sub hU.continuousOn).smul continuousOn_const)

 

 



structure IsSquareMover (c : Plane) (r : ℝ) (M N : Plane → Plane) : Prop where
   
  mapsTo : MapsTo M (closedSquare c r) (closedSquare c r)
   
  mapsTo_inv : MapsTo N (closedSquare c r) (closedSquare c r)
   
  continuousOn : ContinuousOn M (closedSquare c r)
   
  continuousOn_inv : ContinuousOn N (closedSquare c r)
   
  invOn : InvOn N M (closedSquare c r) (closedSquare c r)
   
  fixes : ∀ z ∈ closedSquare c r, supDist z c = r → M z = z
   
  fixes_inv : ∀ z ∈ closedSquare c r, supDist z c = r → N z = z

namespace IsSquareMover

variable {M N M' N' : Plane → Plane}

theorem symm (h : IsSquareMover c r M N) : IsSquareMover c r N M where
  mapsTo := h.mapsTo_inv
  mapsTo_inv := h.mapsTo
  continuousOn := h.continuousOn_inv
  continuousOn_inv := h.continuousOn
  invOn := h.invOn.symm
  fixes := h.fixes_inv
  fixes_inv := h.fixes

theorem bijOn (h : IsSquareMover c r M N) :
    BijOn M (closedSquare c r) (closedSquare c r) :=
  h.invOn.bijOn h.mapsTo h.mapsTo_inv

theorem image_eq (h : IsSquareMover c r M N) :
    M '' closedSquare c r = closedSquare c r := h.bijOn.image_eq

 
theorem comp (h : IsSquareMover c r M N) (h' : IsSquareMover c r M' N') :
    IsSquareMover c r (M' ∘ M) (N ∘ N') where
  mapsTo := h'.mapsTo.comp h.mapsTo
  mapsTo_inv := h.mapsTo_inv.comp h'.mapsTo_inv
  continuousOn := h'.continuousOn.comp h.continuousOn h.mapsTo
  continuousOn_inv := h.continuousOn_inv.comp h'.continuousOn_inv h'.mapsTo_inv
  invOn := by
    constructor
    · intro z hz
      simp only [Function.comp_apply]
      rw [h'.invOn.1 (h.mapsTo hz), h.invOn.1 hz]
    · intro z hz
      simp only [Function.comp_apply]
      rw [h.invOn.2 (h'.mapsTo_inv hz), h'.invOn.2 hz]
  fixes := fun z hz hbd => by
    simp only [Function.comp_apply, h.fixes z hz hbd, h'.fixes z hz hbd]
  fixes_inv := fun z hz hbd => by
    simp only [Function.comp_apply, h'.fixes_inv z hz hbd, h.fixes_inv z hz hbd]

end IsSquareMover

 
theorem isSquareMover_shear (h : IsShear r a b k k') (hij : j ≠ i) :
    IsSquareMover c r (shear c r a b k k' i j) (shear c r a b (k + k') (-k') i j) where
  mapsTo := shear_mapsTo h i j
  mapsTo_inv := shear_mapsTo h.inv i j
  continuousOn := shear_continuousOn h i j
  continuousOn_inv := shear_continuousOn h.inv i j
  invOn := by
    refine ⟨fun z hz => shear_shear h hij hz, fun z hz => ?_⟩
    have hz' := shear_shear h.inv hij hz
    rwa [show k + k' + -k' = k by ring, neg_neg] at hz'
  fixes := fun z hz hbd => shear_eq_self_of_boundary h hij hz hbd
  fixes_inv := fun z hz hbd => shear_eq_self_of_boundary h.inv hij hz hbd

 

 








theorem exists_squareMover {c x y : Plane} {r : ℝ} (hx : x ∈ openSquare c r)
    (hy : y ∈ openSquare c r) :
    ∃ M N : Plane → Plane, IsSquareMover c r M N ∧ M x = y ∧ N y = x := by
  have hx0 := mem_Ioo_of_mem_openSquare hx 0
  have hx1 := mem_Ioo_of_mem_openSquare hx 1
  have hy0 := mem_Ioo_of_mem_openSquare hy 0
  have hy1 := mem_Ioo_of_mem_openSquare hy 1
  have hne : (1 : Fin 2) ≠ 0 := by decide
  have hne' : (0 : Fin 2) ≠ 1 := by decide
  
  have h₁ : IsShear r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) := by
    refine ⟨hx1, hx0, by simpa using hx0, ?_⟩
    rw [show x 0 - c 0 + (0 + (y 0 - x 0)) = y 0 - c 0 by ring]
    exact hy0
  
  have h₂ : IsShear r (x 1 - c 1) (y 0 - c 0) 0 (y 1 - x 1) := by
    refine ⟨hy0, hx1, by simpa using hx1, ?_⟩
    rw [show x 1 - c 1 + (0 + (y 1 - x 1)) = y 1 - c 1 by ring]
    exact hy1
  have hmover := (isSquareMover_shear (c := c) h₁ hne).comp (isSquareMover_shear (c := c) h₂ hne')
  have hMx : (shear c r (x 1 - c 1) (y 0 - c 0) 0 (y 1 - x 1) 1 0 ∘
      shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1) x = y := by
    
    have hW₁ : shearWeight c r (x 1 - c 1) 1 x = 1 := by
      rw [shearWeight, tent_self hx1.1 hx1.2]
    have hfirst0 : shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1 x 0 = y 0 := by
      rw [shear_apply_same, hW₁]
      simp only [add_zero, zero_add, mul_one]
      rw [bend_self hx0.1]
      ring
    have hfirst1 : shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1 x 1 = x 1 :=
      shear_apply_ne hne
    have hW₂ : shearWeight c r (y 0 - c 0) 0
        (shear c r (x 0 - c 0) (x 1 - c 1) 0 (y 0 - x 0) 0 1 x) = 1 := by
      rw [shearWeight, hfirst0, tent_self hy0.1 hy0.2]
    simp only [Function.comp_apply]
    ext l
    revert l
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [shear_apply_ne hne', hfirst0]
    · rw [shear_apply_same, hW₂, hfirst1]
      simp only [add_zero, zero_add, mul_one]
      rw [bend_self hx1.1]
      ring
  refine ⟨_, _, hmover, hMx, ?_⟩
  have hinv := hmover.invOn.1 (show supDist x c ≤ r from hx.le)
  rwa [hMx] at hinv

 

theorem add_smul_single_apply (z : Plane) (t : ℝ) (l : Fin 2) :
    (z + t • EuclideanSpace.single l (1 : ℝ)) l = z l + t := by
  simp [PiLp.add_apply, PiLp.smul_apply]

theorem dist_add_smul_single (z : Plane) (t : ℝ) (l : Fin 2) :
    dist (z + t • EuclideanSpace.single l (1 : ℝ)) z = |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, PiLp.norm_single]
  simp

 

theorem interior_closedSquare (c : Plane) (r : ℝ) :
    interior (closedSquare c r) = openSquare c r := by
  have hsub : openSquare c r ⊆ closedSquare c r := fun z hz => show supDist z c ≤ r from hz.le
  refine Subset.antisymm (fun z hz => ?_) (interior_maximal hsub (isOpen_openSquare c r))
  by_contra hzo
  have hzc : z ∈ closedSquare c r := interior_subset hz
  have heq : supDist z c = r := le_antisymm hzc (not_lt.1 hzo)
  obtain ⟨l, hl⟩ := exists_abs_sub_eq_of_supDist_eq heq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  have hr : 0 ≤ r := hl ▸ abs_nonneg _
  have key : ∀ t : ℝ, |t| < ε → |(z l - c l) + t| ≤ r := by
    intro t ht
    have hmem : z + t • EuclideanSpace.single l (1 : ℝ) ∈ closedSquare c r :=
      interior_subset (hball (by rw [Metric.mem_ball, dist_add_smul_single]; exact ht))
    have := le_trans (abs_sub_le_supDist (z + t • EuclideanSpace.single l (1 : ℝ)) c l) hmem
    rwa [add_smul_single_apply, show z l + t - c l = z l - c l + t by ring] at this
  rcases (abs_eq hr).1 hl with he | he
  · have := (abs_le.1 (key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith))).2
    rw [he] at this
    linarith
  · have := (abs_le.1 (key (-(ε / 2)) (by rw [abs_of_neg (by linarith)]; linarith))).1
    rw [he] at this
    linarith

 
theorem frontier_closedSquare (c : Plane) (r : ℝ) :
    frontier (closedSquare c r) = {z | supDist z c = r} := by
  rw [(isClosed_closedSquare c r).frontier_eq, interior_closedSquare]
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 (not_lt.1 h2)
  · intro h
    exact ⟨le_of_eq h, by rw [openSquare, mem_setOf_eq, h]; exact lt_irrefl r⟩

 
theorem IsSquareMover.eqOn_frontier {M N : Plane → Plane} (h : IsSquareMover c r M N) :
    EqOn M id (frontier (closedSquare c r)) := by
  intro z hz
  rw [frontier_closedSquare, mem_setOf_eq] at hz
  exact h.fixes z (le_of_eq hz) hz

 

 
noncomputable def IsSquareMover.homeomorph {M N : Plane → Plane} (h : IsSquareMover c r M N) :
    closedSquare c r ≃ₜ closedSquare c r where
  toFun z := ⟨M z, h.mapsTo z.2⟩
  invFun z := ⟨N z, h.mapsTo_inv z.2⟩
  left_inv z := Subtype.ext (h.invOn.1 z.2)
  right_inv z := Subtype.ext (h.invOn.2 z.2)
  continuous_toFun := h.continuousOn.restrict.subtype_mk _
  continuous_invFun := h.continuousOn_inv.restrict.subtype_mk _

@[simp] theorem IsSquareMover.homeomorph_apply {M N : Plane → Plane}
    (h : IsSquareMover c r M N) (z : closedSquare c r) :
    (h.homeomorph z : Plane) = M z := rfl

@[simp] theorem IsSquareMover.homeomorph_symm_apply {M N : Plane → Plane}
    (h : IsSquareMover c r M N) (z : closedSquare c r) :
    (h.homeomorph.symm z : Plane) = N z := rfl

 













 



theorem iInter_eq_singleton_of_mem_tail {K : ℕ → Set Plane} {v : Plane} {N : ℕ}
    (hne : ∀ n, (K n).Nonempty) (hK : ∀ n, IsCompact (K n)) (hmono : Antitone K)
    (hdiam : Filter.Tendsto (fun n => diam (K n)) Filter.atTop (nhds 0))
    (hv : ∀ n, N ≤ n → v ∈ K n) : ⋂ n, K n = {v} := by
  obtain ⟨p, hp⟩ := eq_singleton_iInter_of_diam_tendsto_zero hne hK hmono hdiam
  have hvmem : v ∈ ⋂ n, K n := by
    refine mem_iInter.2 fun n => ?_
    rcases le_total N n with h | h
    · exact hv n h
    · exact hmono h (hv N le_rfl)
  rw [hp] at hvmem
  rw [hp, mem_singleton_iff.1 hvmem]

end Plane

end Schoenflies
