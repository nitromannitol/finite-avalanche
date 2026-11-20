/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/PolyLocal.lean.
-/
import FiniteAvalanches.Support.Schoenflies.LocallyPolygonal
import FiniteAvalanches.Support.Schoenflies.PolygonalCarrier

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 


















































open Metric Set

namespace Schoenflies

open Plane

variable {S T A B C W : Set Plane} {p x y z : Plane}

 




 

theorem polyConnIn_iff_polyReaches : PolyConnIn S x y ↔ PolyReaches S x y := by
  constructor
  · rintro ⟨vs, hne, hsub, hhead, hlast⟩
    have h := polyReaches_of_poly_subset hne hsub
    rwa [hhead, hlast] at h
  · intro h
    obtain ⟨vs, hne, hsub, hhead, hlast⟩ := h.exists_poly
    exact ⟨vs, hne, hsub, hhead, hlast⟩

alias ⟨PolyConnIn.polyReaches, PolyReaches.polyConnIn⟩ := polyConnIn_iff_polyReaches

 





 
theorem IsLocallyPolyConn.isLocallyPolyConnected (h : IsLocallyPolyConn S) :
    IsLocallyPolyConnected S := by
  intro w hw
  obtain ⟨U, hU, hwU, hconn⟩ := h w hw
  exact ⟨U, hU, hwU, fun z hz => (hconn w ⟨hwU, hw⟩ z hz).polyReaches⟩

 
theorem IsLocallyPolyConnected.isLocallyPolyConn (h : IsLocallyPolyConnected S) :
    IsLocallyPolyConn S := by
  intro p hp
  obtain ⟨V, hV, hpV, hreach⟩ := h p hp
  exact ⟨V, hV, hpV, fun x hx y hy => ((hreach x hx).symm.trans (hreach y hy)).polyConnIn⟩

 




namespace Plane

 



theorem openSquare_subset_ball (p : Plane) (ε : ℝ) : openSquare p (ε / 2) ⊆ ball p ε := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x p < ε / 2 := hx
  have hnorm : ‖x - p‖ ≤ Real.sqrt 2 * supDist x p := norm_le_sqrt_two_mul_supNorm _
  rw [mem_ball, dist_eq_norm]
  nlinarith [supDist_nonneg x p]

 

theorem exists_openSquare_subset {W : Set Plane} {p : Plane} (hW : IsOpen W) (hp : p ∈ W)
    {s₀ : ℝ} (hs₀ : 0 < s₀) : ∃ s, 0 < s ∧ s ≤ s₀ ∧ openSquare p s ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW p hp
  exact ⟨min s₀ (ε / 2), lt_min hs₀ (by linarith), min_le_left _ _,
    (openSquare_mono (min_le_right _ _)).trans ((openSquare_subset_ball p ε).trans hball)⟩

end Plane

 

 







def IsLocallyPolyConnAt' (S : Set Plane) (p : Plane) : Prop :=
  ∀ W : Set Plane, IsOpen W → p ∈ W →
    ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
      ∀ x ∈ U ∩ S, ∀ y ∈ U ∩ S, PolyReaches (U ∩ S) x y

 
def IsLocallyPolyConn' (S : Set Plane) : Prop := ∀ p ∈ S, IsLocallyPolyConnAt' S p

theorem IsLocallyPolyConnAt'.weaken (h : IsLocallyPolyConnAt' S p) :
    IsLocallyPolyConnAt S p := by
  obtain ⟨U, hU, hpU, -, hpath⟩ := h univ isOpen_univ (mem_univ p)
  exact ⟨U, hU, hpU, fun x hx y hy => ((hpath x hx y hy).mono inter_subset_right).polyConnIn⟩

 

theorem IsLocallyPolyConn'.weaken (h : IsLocallyPolyConn' S) : IsLocallyPolyConn S :=
  fun p hp => (h p hp).weaken

 
theorem IsLocallyPolyConn'.isLocallyPolyConnected (h : IsLocallyPolyConn' S) :
    IsLocallyPolyConnected S := h.weaken.isLocallyPolyConnected

 

theorem IsLocallyPolyConnAt'.congr_nhds {V : Set Plane} (h : IsLocallyPolyConnAt' T p)
    (hV : IsOpen V) (hpV : p ∈ V) (heq : S ∩ V = T ∩ V) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ V) (hW.inter hV) ⟨hpW, hpV⟩
  have hUV : U ⊆ V := hUsub.trans inter_subset_right
  have hUST : U ∩ S = U ∩ T := by
    ext x
    constructor
    · rintro ⟨hxU, hxS⟩
      exact ⟨hxU, (heq.subset ⟨hxS, hUV hxU⟩).1⟩
    · rintro ⟨hxU, hxT⟩
      exact ⟨hxU, (heq.symm.subset ⟨hxT, hUV hxU⟩).1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_left, ?_⟩
  rw [hUST]
  exact hpath

 

theorem isLocallyPolyConnAt'_of_nbhd_subset {V : Set Plane} (hV : IsOpen V) (hpV : p ∈ V)
    (hVS : V ⊆ S) : IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, -, hsub⟩ := Plane.exists_openSquare_subset (hV.inter hW) ⟨hpV, hpW⟩ one_pos
  refine ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs,
    hsub.trans inter_subset_right, fun x hx y hy => PolyReaches.of_segment ?_⟩
  exact ((convex_openSquare p s).segment_subset hx.1 hy.1).trans
    fun w hw => ⟨hw, hVS (hsub hw).1⟩

 
theorem isLocallyPolyConn'_of_isOpen (hS : IsOpen S) : IsLocallyPolyConn' S :=
  fun _ hp => isLocallyPolyConnAt'_of_nbhd_subset hS hp Subset.rfl

 









theorem isLocallyPolyConnAt'_of_convex_cover {ι : Type*} {H : ι → Set Plane} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hconv : ∀ i, Convex ℝ (H i))
    (hsub : ∀ i, openSquare p s₀ ∩ H i ⊆ S)
    (hcover : openSquare p s₀ ∩ S ⊆ ⋃ i, H i)
    (hstar : ∀ i, ∀ z ∈ openSquare p s₀ ∩ H i, p ∈ H i) :
    IsLocallyPolyConnAt' S p := by
  intro W hW hpW
  obtain ⟨s, hs, hss₀, hsW⟩ := Plane.exists_openSquare_subset hW hpW hs₀
  have hmono : openSquare p s ⊆ openSquare p s₀ := openSquare_mono hss₀
  have hpiece : ∀ i, openSquare p s ∩ H i ⊆ openSquare p s ∩ S :=
    fun i _ hx => ⟨hx.1, hsub i ⟨hmono hx.1, hx.2⟩⟩
  
  have hto : ∀ x ∈ openSquare p s ∩ S, PolyReaches (openSquare p s ∩ S) x p := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (hcover ⟨hmono hx.1, hx.2⟩)
    refine PolyReaches.of_segment (Subset.trans ?_ (hpiece i))
    exact ((convex_openSquare p s).inter (hconv i)).segment_subset ⟨hx.1, hxi⟩
      ⟨mem_openSquare_self hs, hstar i x ⟨hmono hx.1, hxi⟩⟩
  exact ⟨openSquare p s, isOpen_openSquare p s, mem_openSquare_self hs, hsW,
    fun x hx y hy => (hto x hx).trans (hto y hy).symm⟩

 





 


theorem isLocallyPolyConnAt'_compl_openSquare (c : Plane) (r : ℝ) (p : Plane) :
    IsLocallyPolyConnAt' (openSquare c r)ᶜ p := by
  obtain ⟨s, hs, hstar⟩ := Plane.exists_radius_sides c r p
  refine isLocallyPolyConnAt'_of_convex_cover
    (H := fun ib : Fin 2 × Bool => sideHalfPlane c r ib.1 ib.2) hs
    (fun ib => convex_sideHalfPlane c r ib.1 ib.2)
    (fun ib => inter_subset_right.trans (sideHalfPlane_subset_compl c r ib.1 ib.2))
    (fun x hx => compl_openSquare_subset_iUnion c r hx.2)
    (fun ib z hz => (hstar ib z hz).2)

 







theorem isLocallyPolyConn'_compl_biUnion {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn' ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) := by
  intro p _
  
  have room : ∀ c : Plane, ∀ s ≤ supDist p c - ρ c,
      ∀ x ∈ openSquare p s, x ∉ openSquare c (ρ c) := by
    intro c s hs x hx hmem
    have h₁ : supDist x p < s := hx
    have h₂ : supDist x c < ρ c := hmem
    have := supDist_triangle p x c
    rw [supDist_comm p x] at this
    linarith
  by_cases hnear : ∃ c₀ ∈ Q, p ∈ closedSquare c₀ (ρ c₀)
  · 
    obtain ⟨c₀, hc₀Q, hpc₀⟩ := hnear
    have hfar : ∀ c ∈ Q \ {c₀}, 0 < supDist p c - ρ c := by
      rintro c ⟨hcQ, hcne⟩
      have : p ∉ closedSquare c (ρ c) :=
        Set.disjoint_left.1 (hdisj c₀ hc₀Q c hcQ fun h => hcne (h ▸ rfl)) hpc₀
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite (hQ.sdiff (t := {c₀}))
      (f := fun c => supDist p c - ρ c) hfar
    refine (isLocallyPolyConnAt'_compl_openSquare c₀ (ρ c₀) p).congr_nhds
      (isOpen_openSquare p s) (mem_openSquare_self hs) ?_
    ext x
    constructor
    · rintro ⟨hxM, hxU⟩
      exact ⟨fun hcon => hxM (mem_biUnion hc₀Q hcon), hxU⟩
    · rintro ⟨hx₀, hxU⟩
      refine ⟨fun hcon => ?_, hxU⟩
      obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
      rcases eq_or_ne c c₀ with rfl | hcne
      · exact hx₀ hxc
      · exact room c s (hsle c ⟨hcQ, hcne⟩) x hxU hxc
  · 
    push Not at hnear
    have hfar : ∀ c ∈ Q, 0 < supDist p c - ρ c := by
      intro c hcQ
      have := hnear c hcQ
      simp only [closedSquare, mem_setOf_eq, not_le] at this
      linarith
    obtain ⟨s, hs, hsle⟩ := exists_pos_le_of_finite hQ (f := fun c => supDist p c - ρ c) hfar
    refine isLocallyPolyConnAt'_of_nbhd_subset (isOpen_openSquare p s) (mem_openSquare_self hs)
      fun x hx hcon => ?_
    obtain ⟨c, hcQ, hxc⟩ := mem_iUnion₂.1 hcon
    exact room c s (hsle c hcQ) x hx hxc



example {Q : Set Plane} (hQ : Q.Finite) (ρ : Plane → ℝ)
    (hdisj : ∀ c ∈ Q, ∀ c' ∈ Q, c ≠ c' →
      Disjoint (closedSquare c (ρ c)) (closedSquare c' (ρ c'))) :
    IsLocallyPolyConn ((⋃ c ∈ Q, openSquare c (ρ c))ᶜ) :=
  (isLocallyPolyConn'_compl_biUnion hQ ρ hdisj).weaken

example (c : Plane) (r : ℝ) (p : Plane) : IsLocallyPolyConnAt (openSquare c r)ᶜ p :=
  (isLocallyPolyConnAt'_compl_openSquare c r p).weaken

 







 


theorem IsLocallyPolyConnAt'.inter_isOpen (h : IsLocallyPolyConnAt' S p) (hW : IsOpen W)
    (hpW : p ∈ W) : IsLocallyPolyConnAt' (S ∩ W) p := by
  intro W' hW' hpW'
  obtain ⟨U, hU, hpU, hUsub, hpath⟩ := h (W ∩ W') (hW.inter hW') ⟨hpW, hpW'⟩
  have hUW : U ⊆ W := hUsub.trans inter_subset_left
  have hUS : U ∩ (S ∩ W) = U ∩ S :=
    Subset.antisymm (fun _ hx => ⟨hx.1, hx.2.1⟩) fun _ hx => ⟨hx.1, hx.2, hUW hx.1⟩
  refine ⟨U, hU, hpU, hUsub.trans inter_subset_right, ?_⟩
  rw [hUS]
  exact hpath

theorem IsLocallyPolyConn'.inter_isOpen (h : IsLocallyPolyConn' S) (hW : IsOpen W) :
    IsLocallyPolyConn' (S ∩ W) :=
  fun _ hp => (h _ hp.1).inter_isOpen hW hp.2

 

 
def IsRelOpenIn (S A : Set Plane) : Prop := ∃ W : Set Plane, IsOpen W ∧ A = S ∩ W

theorem IsRelOpenIn.subset (h : IsRelOpenIn S A) : A ⊆ S := by
  obtain ⟨W, -, rfl⟩ := h
  exact inter_subset_left

theorem isRelOpenIn_self (S : Set Plane) : IsRelOpenIn S S :=
  ⟨univ, isOpen_univ, (inter_univ S).symm⟩

theorem IsOpen.isRelOpenIn (hA : IsOpen A) (hAS : A ⊆ S) : IsRelOpenIn S A :=
  ⟨A, hA, (inter_eq_self_of_subset_right hAS).symm⟩

 
theorem isRelOpenIn_of_exists (hAS : A ⊆ S) (h : ∃ U : Set Plane, IsOpen U ∧ A ⊆ U ∧ U ∩ S ⊆ A) :
    IsRelOpenIn S A := by
  obtain ⟨U, hU, hAU, hUA⟩ := h
  exact ⟨U, hU, Subset.antisymm (fun _ hx => ⟨hAS hx, hAU hx⟩) fun _ hx => hUA ⟨hx.2, hx.1⟩⟩

 

theorem IsRelOpenIn.trans (hA : IsRelOpenIn S A) (hB : IsRelOpenIn A B) : IsRelOpenIn S B := by
  obtain ⟨W, hW, rfl⟩ := hA
  obtain ⟨W', hW', rfl⟩ := hB
  exact ⟨W ∩ W', hW.inter hW', by rw [inter_assoc]⟩

 
theorem IsLocallyPolyConn'.of_isRelOpenIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A) :
    IsLocallyPolyConn' A := by
  obtain ⟨W, hW, rfl⟩ := hA
  exact h.inter_isOpen hW

 






theorem isRelOpenIn_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsRelOpenIn S (connectedComponentIn A x) := by
  refine hA.trans (isRelOpenIn_of_exists (connectedComponentIn_subset A x) ?_)
  refine isRelOpen_of_polyReaches_stable (h.of_isRelOpenIn hA).isLocallyPolyConnected
    (connectedComponentIn_subset A x) fun w hw z _ hreach => ?_
  
  obtain ⟨vs, hne, hsubA, hhead, hlast⟩ := hreach.exists_poly
  have hpoly : poly vs ⊆ connectedComponentIn A x := by
    rw [connectedComponentIn_eq hw]
    exact (isConnected_poly hne).isPreconnected.subset_connectedComponentIn
      (hhead ▸ head_mem_poly hne) hsubA
  exact hpoly (hlast ▸ getLast_mem_poly hne)

 

theorem isLocallyPolyConn'_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    (x : Plane) : IsLocallyPolyConn' (connectedComponentIn A x) :=
  h.of_isRelOpenIn (isRelOpenIn_connectedComponentIn h hA x)

 

 

theorem polyReaches_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    PolyReaches C x y :=
  PolyReaches.of_isPreconnected (h.of_isRelOpenIn hC).isLocallyPolyConnected hconn hx hy

 
theorem exists_poly_of_isPreconnected_of_isRelOpenIn (h : IsLocallyPolyConn' S)
    (hC : IsRelOpenIn S C) (hconn : IsPreconnected C) (hx : x ∈ C) (hy : y ∈ C) :
    ∃ vs : List Plane, ∃ hne : vs ≠ [], poly vs ⊆ C ∧ vs.head hne = x ∧ vs.getLast hne = y :=
  (polyReaches_of_isPreconnected_of_isRelOpenIn h hC hconn hx hy).exists_poly

 

theorem polyReaches_connectedComponentIn (h : IsLocallyPolyConn' S) (hA : IsRelOpenIn S A)
    {w : Plane} (hx : x ∈ connectedComponentIn A w) (hy : y ∈ connectedComponentIn A w) :
    PolyReaches (connectedComponentIn A w) x y :=
  polyReaches_of_isPreconnected_of_isRelOpenIn h (isRelOpenIn_connectedComponentIn h hA w)
    isPreconnected_connectedComponentIn hx hy

end Schoenflies
