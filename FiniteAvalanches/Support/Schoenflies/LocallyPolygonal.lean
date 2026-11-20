/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/LocallyPolygonal.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.PolyPath
import FiniteAvalanches.Support.Schoenflies.Square
import FiniteAvalanches.Support.Schoenflies.UniformBound

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 











































open Metric Set

namespace Schoenflies

open Plane

variable {S T : Set Plane} {x y z : Plane}

 





 
theorem poly_reverse : ∀ vs : List Plane, poly vs.reverse = poly vs
  | [] => by simp
  | [v] => by simp
  | u :: v :: tl => by
    rw [List.reverse_cons, poly_concat (by simp) u, poly_reverse (v :: tl),
      List.getLast_reverse (by simp), List.head_cons, poly_cons_cons, segment_symm]
    exact union_comm _ _

 

 



def PolyConnIn (S : Set Plane) (x y : Plane) : Prop :=
  ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ S ∧ vs.head h = x ∧ vs.getLast h = y

theorem PolyConnIn.refl (hx : x ∈ S) : PolyConnIn S x x :=
  ⟨[x], by simp, by simpa using hx, rfl, rfl⟩

 
theorem PolyConnIn.left_mem (h : PolyConnIn S x y) : x ∈ S := by
  obtain ⟨vs, hne, hsub, hhead, -⟩ := h
  exact hhead ▸ hsub (head_mem_poly hne)

theorem PolyConnIn.right_mem (h : PolyConnIn S x y) : y ∈ S := by
  obtain ⟨vs, hne, hsub, -, hlast⟩ := h
  exact hlast ▸ hsub (getLast_mem_poly hne)

theorem PolyConnIn.mono (h : PolyConnIn S x y) (hST : S ⊆ T) : PolyConnIn T x y := by
  obtain ⟨vs, hne, hsub, hhead, hlast⟩ := h
  exact ⟨vs, hne, hsub.trans hST, hhead, hlast⟩

theorem PolyConnIn.trans (hxy : PolyConnIn S x y) (hyz : PolyConnIn S y z) :
    PolyConnIn S x z := by
  obtain ⟨vs, hv, hvS, hvh, hvl⟩ := hxy
  obtain ⟨ws, hw, hwS, hwh, hwl⟩ := hyz
  obtain ⟨w, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [List.head_cons] at hwh
  subst hwh
  refine ⟨vs ++ w :: rest, by simp, ?_, ?_, ?_⟩
  · rw [poly_append hv w rest hvl]; exact union_subset hvS hwS
  · rw [List.head_append_of_ne_nil hv]; exact hvh
  · rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil w rest)]; exact hwl

theorem PolyConnIn.symm (h : PolyConnIn S x y) : PolyConnIn S y x := by
  obtain ⟨vs, hv, hvS, hvh, hvl⟩ := h
  refine ⟨vs.reverse, by simpa using hv, ?_, ?_, ?_⟩
  · rw [poly_reverse]; exact hvS
  · rw [List.head_reverse]; exact hvl
  · rw [List.getLast_reverse]; exact hvh

 
theorem polyConnIn_of_convex {C : Set Plane} (hC : Convex ℝ C) (hCS : C ⊆ S)
    (hx : x ∈ C) (hy : y ∈ C) : PolyConnIn S x y :=
  ⟨[x, y], by simp, by
    rw [poly_cons_cons, poly_singleton]
    exact union_subset ((hC.segment_subset hx hy).trans hCS)
      (singleton_subset_iff.2 (hCS hy)), rfl, rfl⟩

 


theorem polyConnIn_union_of_convex {C D : Set Plane} (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hmeet : (C ∩ D).Nonempty) (hx : x ∈ C ∪ D) (hy : y ∈ C ∪ D) : PolyConnIn (C ∪ D) x y := by
  obtain ⟨w, hwC, hwD⟩ := hmeet
  have hxw : PolyConnIn (C ∪ D) x w := by
    rcases hx with hx | hx
    · exact polyConnIn_of_convex hC subset_union_left hx hwC
    · exact polyConnIn_of_convex hD subset_union_right hx hwD
  have hwy : PolyConnIn (C ∪ D) w y := by
    rcases hy with hy | hy
    · exact polyConnIn_of_convex hC subset_union_left hwC hy
    · exact polyConnIn_of_convex hD subset_union_right hwD hy
  exact hxw.trans hwy

 

 





def IsLocallyPolyConnAt (S : Set Plane) (p : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyConnIn S x y

 
def IsLocallyPolyConn (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt S p

 
theorem isLocallyPolyConnAt_of_convex {U : Set Plane} {p : Plane} (hU : IsOpen U) (hpU : p ∈ U)
    (hUS : U ⊆ S) (hconv : Convex ℝ U) : IsLocallyPolyConnAt S p :=
  ⟨U, hU, hpU, fun _ hx _ hy => polyConnIn_of_convex hconv hUS hx.1 hy.1⟩

 





theorem isLocallyPolyConnAt_of_star {U : Set Plane} {p : Plane} {ι : Type*} {C : ι → Set Plane}
    (hU : IsOpen U) (hpU : p ∈ U) (hcover : U ∩ S ⊆ ⋃ i, C i) (hsub : ∀ i, C i ⊆ S)
    (hconv : ∀ i, Convex ℝ (C i)) (hstar : ∀ i, ∀ z ∈ C i, p ∈ C i) :
    IsLocallyPolyConnAt S p := by
  refine ⟨U, hU, hpU, fun x hx y hy => ?_⟩
  obtain ⟨i, hxi⟩ := mem_iUnion.1 (hcover hx)
  obtain ⟨j, hyj⟩ := mem_iUnion.1 (hcover hy)
  exact (polyConnIn_of_convex (hconv i) (hsub i) hxi (hstar i x hxi)).trans
    (polyConnIn_of_convex (hconv j) (hsub j) (hstar j y hyj) hyj)

 

namespace Plane

 

theorem mem_openSquare_iff (c : Plane) (r : ℝ) (x : Plane) :
    x ∈ openSquare c r ↔ ∀ i, |x i - c i| < r := by
  simp only [openSquare, mem_setOf_eq, supDist, supNorm, sub_apply, max_lt_iff,
    Fin.forall_fin_two]

 
theorem mem_openSquare_self {p : Plane} {s : ℝ} (hs : 0 < s) : p ∈ openSquare p s := by
  simpa [openSquare] using hs

 
theorem openSquare_mono {p : Plane} {s t : ℝ} (h : s ≤ t) : openSquare p s ⊆ openSquare p t :=
  fun _ hx => lt_of_lt_of_le hx h

 


def sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) : Set Plane :=
  cond b {x | c i + r ≤ x i} {x | x i ≤ c i - r}

 


noncomputable def sideGap (c : Plane) (r : ℝ) (p : Plane) (i : Fin 2) (b : Bool) : ℝ :=
  cond b ((c i + r) - p i) (p i - (c i - r))

theorem convex_sideHalfPlane (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    Convex ℝ (sideHalfPlane c r i b) := by
  cases b
  · exact convex_coord_le i _
  · exact convex_coord_ge i _

 
theorem sideHalfPlane_subset_compl (c : Plane) (r : ℝ) (i : Fin 2) (b : Bool) :
    sideHalfPlane c r i b ⊆ (openSquare c r)ᶜ := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff c r x).1 hmem i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hx) (by linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hx) (by linarith [hlt.2])

 
theorem compl_openSquare_subset_iUnion (c : Plane) (r : ℝ) :
    (openSquare c r)ᶜ ⊆ ⋃ ib : Fin 2 × Bool, sideHalfPlane c r ib.1 ib.2 := by
  intro x hx
  rw [mem_compl_iff, mem_openSquare_iff] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  rcases le_abs.1 hi with h | h
  · exact mem_iUnion.2 ⟨(i, true), show c i + r ≤ x i by linarith⟩
  · exact mem_iUnion.2 ⟨(i, false), show x i ≤ c i - r by linarith⟩

 


theorem openSquare_disjoint_sideHalfPlane {c : Plane} {r s : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (hs : s ≤ sideGap c r p i b) :
    ∀ x ∈ openSquare p s, x ∉ sideHalfPlane c r i b := by
  intro x hx hmem
  have hlt := (mem_openSquare_iff p s x).1 hx i
  rw [abs_lt] at hlt
  cases b
  · exact absurd (show x i ≤ c i - r from hmem) (by
      simp only [sideGap, cond_false] at hs; linarith [hlt.1])
  · exact absurd (show c i + r ≤ x i from hmem) (by
      simp only [sideGap, cond_true] at hs; linarith [hlt.2])

 
theorem mem_sideHalfPlane_of_sideGap_nonpos {c : Plane} {r : ℝ} {p : Plane} {i : Fin 2}
    {b : Bool} (h : sideGap c r p i b ≤ 0) : p ∈ sideHalfPlane c r i b := by
  cases b
  · simp only [sideGap, cond_false] at h
    exact show p i ≤ c i - r by linarith
  · simp only [sideGap, cond_true] at h
    exact show c i + r ≤ p i by linarith

 


theorem convex_openSquare_inter_sideHalfPlane (p : Plane) (s : ℝ) (c : Plane) (r : ℝ)
    (i : Fin 2) (b : Bool) : Convex ℝ (openSquare p s ∩ sideHalfPlane c r i b) :=
  (convex_openSquare p s).inter (convex_sideHalfPlane c r i b)

end Plane

 

 


theorem exists_pos_le_of_pos {ι : Type*} [Finite ι] (d : ι → ℝ) :
    ∃ s > 0, ∀ i, 0 < d i → s ≤ d i := by
  obtain ⟨s, hs, hle⟩ :=
    exists_pos_le_of_finite (S := {i : ι | 0 < d i}) (Set.toFinite _) (f := d) fun _ hi => hi
  exact ⟨s, hs, fun i hi => hle i hi⟩

 

theorem Plane.exists_radius_sides (c : Plane) (r : ℝ) (p : Plane) :
    ∃ s > 0, ∀ ib : Fin 2 × Bool,
      ∀ z ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2,
        p ∈ openSquare p s ∩ sideHalfPlane c r ib.1 ib.2 := by
  obtain ⟨s, hs, hle⟩ := exists_pos_le_of_pos fun ib : Fin 2 × Bool => sideGap c r p ib.1 ib.2
  refine ⟨s, hs, fun ib z hz => ⟨?_, ?_⟩⟩
  · 
    exact mem_openSquare_self hs
  · 
    
    by_contra hp
    exact openSquare_disjoint_sideHalfPlane
      (hle ib (lt_of_not_ge fun hcon => hp (mem_sideHalfPlane_of_sideGap_nonpos hcon))) z hz.1 hz.2

 

 






theorem isLocallyPolyConnAt_compl_openSquare (c : Plane) (r : ℝ) (p : Plane) :
    IsLocallyPolyConnAt (openSquare c r)ᶜ p := by
  obtain ⟨s, hs, hstar⟩ := Plane.exists_radius_sides c r p
  refine isLocallyPolyConnAt_of_star (C := fun ib : Fin 2 × Bool =>
      openSquare p s ∩ sideHalfPlane c r ib.1 ib.2)
    (isOpen_openSquare p s) (mem_openSquare_self hs) ?_ ?_ ?_ hstar
  · rintro x ⟨hxU, hxM⟩
    obtain ⟨ib, hib⟩ := mem_iUnion.1 (compl_openSquare_subset_iUnion c r hxM)
    exact mem_iUnion.2 ⟨ib, hxU, hib⟩
  · exact fun ib => inter_subset_right.trans (sideHalfPlane_subset_compl c r ib.1 ib.2)
  · exact fun ib => convex_openSquare_inter_sideHalfPlane p s c r ib.1 ib.2

 

 






theorem isLocallyPolyConn_compl_biUnion {A : Set Plane} (hA : A.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ A, ∀ c' ∈ A, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn ((⋃ c ∈ A, openSquare c (ρ c))ᶜ) := by
  intro p _
  
  have room : ∀ c : Plane, ρ c < supDist p c → ∀ s ≤ supDist p c - ρ c,
      ∀ x ∈ openSquare p s, x ∉ openSquare c (ρ c) := by
    intro c _ s hs x hx hmem
    have h₁ : supDist x p < s := hx
    have h₂ : supDist x c < ρ c := hmem
    have := supDist_triangle p x c
    rw [supDist_comm p x] at this
    linarith
  by_cases hnear : ∃ c₀ ∈ A, p ∈ closedSquare c₀ (ρ c₀)
  · 
    obtain ⟨c₀, hc₀A, hpc₀⟩ := hnear
    have hfar : ∀ c ∈ A \ {c₀}, 0 < supDist p c - ρ c := by
      rintro c ⟨hcA, hcne⟩
      have : p ∉ closedSquare c (ρ c) :=
        Set.disjoint_left.1 (hdisj c₀ hc₀A c hcA fun h => hcne (h ▸ rfl)) hpc₀
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s₁, hs₁, hs₁le⟩ := exists_pos_le_of_finite (hA.sdiff (t := {c₀}))
      (f := fun c => supDist p c - ρ c) hfar
    obtain ⟨s₂, hs₂, hstar⟩ := Plane.exists_radius_sides c₀ (ρ c₀) p
    set s := min s₁ s₂ with hsdef
    have hs : 0 < s := lt_min hs₁ hs₂
    have hpU : p ∈ openSquare p s := mem_openSquare_self hs
    
    have hloc : openSquare p s ∩ (⋃ c ∈ A, openSquare c (ρ c))ᶜ
        ⊆ openSquare p s ∩ (openSquare c₀ (ρ c₀))ᶜ := by
      rintro x ⟨hxU, hxM⟩
      exact ⟨hxU, fun hcon => hxM (mem_biUnion hc₀A hcon)⟩
    have hback : ∀ x ∈ openSquare p s, x ∉ openSquare c₀ (ρ c₀) →
        x ∈ (⋃ c ∈ A, openSquare c (ρ c))ᶜ := by
      intro x hxU hx₀ hcon
      obtain ⟨c, hcA, hxc⟩ := mem_iUnion₂.1 hcon
      rcases eq_or_ne c c₀ with rfl | hcne
      · exact hx₀ hxc
      · exact room c (by linarith [hfar c ⟨hcA, hcne⟩]) s
          (le_trans (min_le_left _ _) (hs₁le c ⟨hcA, hcne⟩)) x hxU hxc
    refine isLocallyPolyConnAt_of_star (C := fun ib : Fin 2 × Bool =>
        openSquare p s ∩ sideHalfPlane c₀ (ρ c₀) ib.1 ib.2)
      (isOpen_openSquare p s) hpU ?_ ?_ ?_ ?_
    · rintro x hx
      obtain ⟨hxU, hx₀⟩ := hloc hx
      obtain ⟨ib, hib⟩ := mem_iUnion.1 (compl_openSquare_subset_iUnion c₀ (ρ c₀) hx₀)
      exact mem_iUnion.2 ⟨ib, hxU, hib⟩
    · rintro ib x ⟨hxU, hxH⟩
      exact hback x hxU (sideHalfPlane_subset_compl c₀ (ρ c₀) ib.1 ib.2 hxH)
    · exact fun ib => convex_openSquare_inter_sideHalfPlane p s c₀ (ρ c₀) ib.1 ib.2
    · 
      rintro ib z ⟨hzU, hzH⟩
      refine ⟨hpU, ?_⟩
      have : z ∈ openSquare p s₂ ∩ sideHalfPlane c₀ (ρ c₀) ib.1 ib.2 :=
        ⟨openSquare_mono (min_le_right s₁ s₂) hzU, hzH⟩
      exact (hstar ib z this).2
  · 
    push Not at hnear
    have hfar : ∀ c ∈ A, 0 < supDist p c - ρ c := by
      intro c hcA
      have := hnear c hcA
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite hA (f := fun c => supDist p c - ρ c) hfar
    refine isLocallyPolyConnAt_of_convex (isOpen_openSquare p s)
      (mem_openSquare_self hs) ?_ (convex_openSquare p s)
    intro x hx hcon
    obtain ⟨c, hcA, hxc⟩ := mem_iUnion₂.1 hcon
    exact room c (by linarith [hfar c hcA]) s (hsle c hcA) x hx hxc

end Schoenflies
