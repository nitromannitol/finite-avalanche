/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/CrosscutAtMostTwo.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Subarc
import FiniteAvalanches.Support.Schoenflies.Topology
import FiniteAvalanches.Support.Schoenflies.Polygonal
import FiniteAvalanches.Support.Schoenflies.Strip

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




































































open Metric Set unitInterval

namespace Schoenflies

variable {D P K K' : Set Plane}

 












 







structure ArcCollar (D P K : Set Plane) where
   
  nbhd : Set Plane
   
  left : Set Plane
   
  right : Set Plane
  isOpen_nbhd : IsOpen nbhd
  subset_nbhd : K ⊆ nbhd
  nbhd_subset : nbhd ⊆ D
  nbhd_diff : nbhd \ P = left ∪ right
  isConnected_left : IsConnected left
  isConnected_right : IsConnected right
  subset_closure_left : K ⊆ closure left
  subset_closure_right : K ⊆ closure right

 









def HasArcCollars (D P : Set Plane) : Prop :=
  ∀ K : Set Plane, K ⊆ D ∩ P → IsCompact K → IsPreconnected K → K.Nontrivial →
    Nonempty (ArcCollar D P K)

namespace ArcCollar

theorem left_subset_nbhd_diff (C : ArcCollar D P K) : C.left ⊆ C.nbhd \ P := by
  rw [C.nbhd_diff]; exact subset_union_left

theorem right_subset_nbhd_diff (C : ArcCollar D P K) : C.right ⊆ C.nbhd \ P := by
  rw [C.nbhd_diff]; exact subset_union_right

theorem nbhd_diff_subset_diff (C : ArcCollar D P K) : C.nbhd \ P ⊆ D \ P :=
  fun _ hy => ⟨C.nbhd_subset hy.1, hy.2⟩

theorem left_subset_diff (C : ArcCollar D P K) : C.left ⊆ D \ P :=
  C.left_subset_nbhd_diff.trans C.nbhd_diff_subset_diff

theorem right_subset_diff (C : ArcCollar D P K) : C.right ⊆ D \ P :=
  C.right_subset_nbhd_diff.trans C.nbhd_diff_subset_diff

 

noncomputable def ptL (C : ArcCollar D P K) : Plane := C.isConnected_left.nonempty.some

 
noncomputable def ptR (C : ArcCollar D P K) : Plane := C.isConnected_right.nonempty.some

theorem ptL_mem (C : ArcCollar D P K) : C.ptL ∈ C.left := C.isConnected_left.nonempty.some_mem

theorem ptR_mem (C : ArcCollar D P K) : C.ptR ∈ C.right := C.isConnected_right.nonempty.some_mem

theorem ptL_mem_diff (C : ArcCollar D P K) : C.ptL ∈ D \ P := C.left_subset_diff C.ptL_mem

theorem ptR_mem_diff (C : ArcCollar D P K) : C.ptR ∈ D \ P := C.right_subset_diff C.ptR_mem

 





theorem meeting_subset_components (C₀ : ArcCollar D P K') {S : Set Plane}
    (hS : IsPreconnected S) (hSsub : S ⊆ D \ P) (hmeet : (C₀.nbhd ∩ S).Nonempty) :
    S ⊆ connectedComponentIn (D \ P) C₀.ptL ∪ connectedComponentIn (D \ P) C₀.ptR := by
  obtain ⟨y, hy₀, hyS⟩ := hmeet
  have hy : y ∈ C₀.left ∪ C₀.right := by
    rw [← C₀.nbhd_diff]; exact ⟨hy₀, (hSsub hyS).2⟩
  rcases hy with hy | hy
  · refine subset_union_of_subset_left ?_ _
    have hconn : IsPreconnected (S ∪ C₀.left) :=
      IsPreconnected.union y hyS hy hS C₀.isConnected_left.2
    have hsub : S ∪ C₀.left ⊆ D \ P := union_subset hSsub C₀.left_subset_diff
    exact fun _ hz =>
      hconn.subset_connectedComponentIn (Or.inr C₀.ptL_mem) hsub (Or.inl hz)
  · refine subset_union_of_subset_right ?_ _
    have hconn : IsPreconnected (S ∪ C₀.right) :=
      IsPreconnected.union y hyS hy hS C₀.isConnected_right.2
    have hsub : S ∪ C₀.right ⊆ D \ P := union_subset hSsub C₀.right_subset_diff
    exact fun _ hz =>
      hconn.subset_connectedComponentIn (Or.inr C₀.ptR_mem) hsub (Or.inl hz)

 






theorem nbhd_diff_subset_components (C₀ : ArcCollar D P K') (C : ArcCollar D P K)
    {z : Plane} (hz' : z ∈ K') (hz : z ∈ K) :
    C.nbhd \ P ⊆ connectedComponentIn (D \ P) C₀.ptL ∪ connectedComponentIn (D \ P) C₀.ptR := by
  have hmeetL : (C₀.nbhd ∩ C.left).Nonempty :=
    mem_closure_iff.1 (C.subset_closure_left hz) C₀.nbhd C₀.isOpen_nbhd (C₀.subset_nbhd hz')
  have hmeetR : (C₀.nbhd ∩ C.right).Nonempty :=
    mem_closure_iff.1 (C.subset_closure_right hz) C₀.nbhd C₀.isOpen_nbhd (C₀.subset_nbhd hz')
  rw [C.nbhd_diff]
  exact union_subset
    (C₀.meeting_subset_components C.isConnected_left.2 C.left_subset_diff hmeetL)
    (C₀.meeting_subset_components C.isConnected_right.2 C.right_subset_diff hmeetR)

end ArcCollar

 

 


theorem isOpen_notMem_two_components {S : Set Plane} (hS : IsOpen S) (zL zR : Plane) :
    IsOpen {y | y ∈ S ∧ y ∉ connectedComponentIn S zL ∧ y ∉ connectedComponentIn S zR} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨hyS, hyL, hyR⟩
  refine ⟨connectedComponentIn S y, ?_, Plane.isOpen_connectedComponentIn hS,
    mem_connectedComponentIn hyS⟩
  intro w hw
  
  
  have hcw : connectedComponentIn S y = connectedComponentIn S w := connectedComponentIn_eq hw
  refine ⟨connectedComponentIn_subset S y hw, fun hwL => hyL ?_, fun hwR => hyR ?_⟩
  · rw [show connectedComponentIn S zL = connectedComponentIn S y from
      (connectedComponentIn_eq hwL).trans hcw.symm]
    exact mem_connectedComponentIn hyS
  · rw [show connectedComponentIn S zR = connectedComponentIn S y from
      (connectedComponentIn_eq hwR).trans hcw.symm]
    exact mem_connectedComponentIn hyS

 







theorem covered_by_two_of_local (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hPclosed : IsClosed P) {zL zR : Plane} (hzL : zL ∈ D \ P)
    (hloc : ∀ w ∈ D ∩ P, ∃ V : Set Plane, IsOpen V ∧ w ∈ V ∧ V ⊆ D ∧
      V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR)
    {x : Plane} (hx : x ∈ D \ P) :
    x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR := by
  by_contra hcon
  push Not at hcon
  have hSopen : IsOpen (D \ P) := hDopen.sdiff hPclosed
  
  have hWopen : IsOpen (⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
      V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) :=
    isOpen_sUnion fun _ hV => hV.1
  have hUopen : IsOpen (connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) :=
    ((Plane.isOpen_connectedComponentIn hSopen).union
      (Plane.isOpen_connectedComponentIn hSopen)).union hWopen
  have hTopen := isOpen_notMem_two_components hSopen zL zR
  
  
  have hdisj : ∀ y, y ∈ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR} →
      y ∈ {y | y ∈ D \ P ∧ y ∉ connectedComponentIn (D \ P) zL ∧
        y ∉ connectedComponentIn (D \ P) zR} → False := by
    rintro y (hy | hy) ⟨hyS, hyL, hyR⟩
    · exact hy.elim hyL hyR
    · obtain ⟨V, hV, hyV⟩ := hy
      exact (hV.2.2 ⟨hyV, hyS.2⟩).elim hyL hyR
  
  have hcover : D ⊆ (connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set Plane | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) ∪
      {y | y ∈ D \ P ∧ y ∉ connectedComponentIn (D \ P) zL ∧
        y ∉ connectedComponentIn (D \ P) zR} := by
    intro y hyD
    by_cases hyP : y ∈ P
    · obtain ⟨V, hVopen, hyV, hVD, hVsub⟩ := hloc y ⟨hyD, hyP⟩
      exact Or.inl (Or.inr ⟨V, ⟨hVopen, hVD, hVsub⟩, hyV⟩)
    · by_cases hyL : y ∈ connectedComponentIn (D \ P) zL
      · exact Or.inl (Or.inl (Or.inl hyL))
      by_cases hyR : y ∈ connectedComponentIn (D \ P) zR
      · exact Or.inl (Or.inl (Or.inr hyR))
      exact Or.inr ⟨⟨hyD, hyP⟩, hyL, hyR⟩
  obtain ⟨y, hyD, hyU, hyT⟩ := hDconn _ _ hUopen hTopen hcover
    ⟨zL, hzL.1, Or.inl (Or.inl (mem_connectedComponentIn hzL))⟩
    ⟨x, hx.1, hx, hcon.1, hcon.2⟩
  exact hdisj y hyU hyT

 

 












theorem crosscut_at_most_two {a b : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (_hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hcollars : HasArcCollars D P) :
    ∃ zL ∈ D \ P, ∃ zR ∈ D \ P, ∀ x ∈ D \ P,
      x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR := by
  have hPclosed : IsClosed P := hP.isArc.isClosed
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := hP
  
  
  have hDPeq : D ∩ P = f '' Ioo 0 1 := by
    have hdiff : P \ {a, b} = f '' Ioo 0 1 := by
      rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi]
      rfl
    rw [← hdiff]
    ext y
    simp only [mem_inter_iff, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨hyD, hyP⟩ => ⟨hyP, ?_⟩, fun ⟨hyP, hy⟩ => ⟨hPD ⟨hyP, by simpa using hy⟩, hyP⟩⟩
    rintro (rfl | rfl)
    exacts [ha hyD, hb hyD]
  
  have hsubarc : ∀ s t : ℝ, 0 < s → s < t → t < 1 → Nonempty (ArcCollar D P (f '' Icc s t)) := by
    intro s t hs hst ht
    have hsubI : Icc s t ⊆ I := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsubIoo : Icc s t ⊆ Ioo 0 1 := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsI : s ∈ Icc s t := left_mem_Icc.2 hst.le
    have htI : t ∈ Icc s t := right_mem_Icc.2 hst.le
    refine hcollars _ (by rw [hDPeq]; exact image_mono hsubIoo)
      (isCompact_image_of_subset_I hc hsubI isClosed_Icc)
      (isPreconnected_Icc.image f (hc.mono hsubI))
      ⟨f s, mem_image_of_mem f hsI, f t, mem_image_of_mem f htI, fun h => ?_⟩
    exact absurd (hi (hsubI hsI) (hsubI htI) h) (ne_of_lt hst)
  
  obtain ⟨C₀⟩ := hsubarc (1 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
  have hz₀ : f (1 / 2) ∈ f '' Icc (1 / 4 : ℝ) (3 / 4) :=
    mem_image_of_mem f ⟨by norm_num, by norm_num⟩
  refine ⟨C₀.ptL, C₀.ptL_mem_diff, C₀.ptR, C₀.ptR_mem_diff, fun x hx => ?_⟩
  refine covered_by_two_of_local hDopen hDconn hPclosed C₀.ptL_mem_diff (fun w hw => ?_) hx
  
  
  rw [hDPeq] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨C⟩ := hsubarc (min u (1 / 4)) (max u (3 / 4))
    (lt_min hu.1 (by norm_num)) (by have := min_le_right u (1 / 4 : ℝ)
                                    have := le_max_right u (3 / 4 : ℝ)
                                    linarith)
    (max_lt hu.2 (by norm_num))
  refine ⟨C.nbhd, C.isOpen_nbhd,
    C.subset_nbhd (mem_image_of_mem f ⟨min_le_left _ _, le_max_left _ _⟩), C.nbhd_subset, ?_⟩
  exact C₀.nbhd_diff_subset_components C hz₀
    (mem_image_of_mem f ⟨le_trans (min_le_right _ _) (by norm_num),
      le_trans (by norm_num) (le_max_right _ _)⟩)

 






theorem covered_by_two_components_of_ne {S : Set Plane} {zL zR v₁ v₂ : Plane}
    (h : ∀ x ∈ S, x ∈ connectedComponentIn S zL ∨ x ∈ connectedComponentIn S zR)
    (h₁ : v₁ ∈ S) (h₂ : v₂ ∈ S)
    (hne : connectedComponentIn S v₁ ≠ connectedComponentIn S v₂) :
    ∀ x ∈ S, x ∈ connectedComponentIn S v₁ ∨ x ∈ connectedComponentIn S v₂ := by
  intro x hx
  rcases h v₁ h₁ with hv₁ | hv₁ <;> rcases h v₂ h₂ with hv₂ | hv₂
  · exact absurd ((connectedComponentIn_eq hv₁).symm.trans (connectedComponentIn_eq hv₂)) hne
  · rcases h x hx with hxx | hxx
    · exact Or.inl (by rw [connectedComponentIn_eq hv₁] at hxx; exact hxx)
    · exact Or.inr (by rw [connectedComponentIn_eq hv₂] at hxx; exact hxx)
  · rcases h x hx with hxx | hxx
    · exact Or.inr (by rw [connectedComponentIn_eq hv₂] at hxx; exact hxx)
    · exact Or.inl (by rw [connectedComponentIn_eq hv₁] at hxx; exact hxx)
  · exact absurd ((connectedComponentIn_eq hv₁).symm.trans (connectedComponentIn_eq hv₂)) hne

 











namespace Plane

 





theorem exists_direction_length {a b : Plane} (hab : a ≠ b) :
    ∃ (u : Plane) (L : ℝ), 0 < L ∧ IsDirection u ∧ L • u = b - a := by
  have hne : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hL : (0 : ℝ) < ‖b - a‖ := norm_pos_iff.2 hne
  exact ⟨dir (b - a), ‖b - a‖, hL, isDirection_dir hne, by
    rw [dir, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]⟩

 




theorem mem_segment_iff_coord {a b u x : Plane} {L : ℝ} (hL : 0 < L) (hu : IsDirection u)
    (hLu : L • u = b - a) :
    x ∈ segment ℝ a b ↔ coordAcross a u x = 0 ∧ coordAlong a u x ∈ Icc 0 L := by
  constructor
  · intro hx
    rw [segment_eq_image'] at hx
    obtain ⟨θ, hθ, rfl⟩ := hx
    have hrw : a + θ • (b - a) = a + (θ * L) • u + (0 : ℝ) • perp u := by
      rw [mul_smul, hLu]; module
    dsimp only
    rw [hrw, coordAlong_param hu, coordAcross_param hu]
    exact ⟨rfl, mul_nonneg hθ.1 hL.le, by nlinarith [hθ.2, hL.le]⟩
  · rintro ⟨h0, hc⟩
    rw [segment_eq_image']
    refine ⟨coordAlong a u x / L, ⟨div_nonneg hc.1 hL.le, (div_le_one hL).2 hc.2⟩, ?_⟩
    dsimp only
    rw [← hLu, smul_smul, div_mul_cancel₀ _ hL.ne']
    nth_rewrite 2 [frame_decomp hu a x]
    rw [h0]
    module

 
theorem eq_foot_of_coordAcross_eq_zero {a u x : Plane} (hu : IsDirection u)
    (h0 : coordAcross a u x = 0) : x = a + (coordAlong a u x) • u := by
  nth_rewrite 1 [frame_decomp hu a x]
  rw [h0]
  module

end Plane

open Plane in
 







theorem hasArcCollars_segment {a b : Plane} (hab : a ≠ b) (hDopen : IsOpen D)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : segment ℝ a b \ {a, b} ⊆ D) :
    HasArcCollars D (segment ℝ a b) := by
  obtain ⟨u, L, hL, hu, hLu⟩ := exists_direction_length hab
  
  have hAlong : ∀ c s : ℝ, coordAlong a u (a + c • u + s • perp u) = c :=
    fun c s => coordAlong_param hu a c s
  have hAcross : ∀ c s : ℝ, coordAcross a u (a + c • u + s • perp u) = s :=
    fun c s => coordAcross_param hu a c s
  have hzero : ∀ c : ℝ, a + c • u = a + c • u + (0 : ℝ) • perp u := fun c => by module
  have hfoot : ∀ c : ℝ, coordAlong a u (a + c • u) = c := fun c => by
    rw [hzero c]; exact hAlong c 0
  have hfoot' : ∀ c : ℝ, coordAcross a u (a + c • u) = 0 := fun c => by
    rw [hzero c]; exact hAcross c 0
  have hAa : coordAlong a u a = 0 := by simp [coordAlong]
  have hAb : coordAlong a u b = L := by
    rw [coordAlong, ← hLu, real_inner_smul_right, real_inner_self_eq_norm_mul_norm, hu.norm]
    ring
  
  have hline : ∀ c : ℝ, 0 < c → c < L → a + c • u ∈ D ∩ segment ℝ a b := by
    intro c hc0 hcL
    have hmem : a + c • u ∈ segment ℝ a b :=
      (mem_segment_iff_coord hL hu hLu).2 ⟨hfoot' c, by rw [hfoot c]; exact ⟨hc0.le, hcL.le⟩⟩
    refine ⟨hPD ⟨hmem, ?_⟩, hmem⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro (h | h)
    · have hcc := hfoot c
      rw [h, hAa] at hcc
      exact absurd hcc.symm (ne_of_gt hc0)
    · have hcc := hfoot c
      rw [h, hAb] at hcc
      exact absurd hcc.symm (ne_of_lt hcL)
  intro K hKsub hKcompact _ hKnontriv
  
  
  have hKcoord : ∀ x ∈ K, coordAcross a u x = 0 ∧ 0 < coordAlong a u x ∧ coordAlong a u x < L := by
    intro x hx
    obtain ⟨h0, hc⟩ := (mem_segment_iff_coord hL hu hLu).1 (hKsub hx).2
    refine ⟨h0, lt_of_le_of_ne hc.1 ?_, lt_of_le_of_ne hc.2 ?_⟩
    · intro hz
      have hxa : x = a := by
        have h := eq_foot_of_coordAcross_eq_zero hu h0
        rwa [← hz, zero_smul, add_zero] at h
      exact ha (hxa ▸ (hKsub hx).1)
    · intro hz
      have hxb : x = b := by
        have h := eq_foot_of_coordAcross_eq_zero hu h0
        rw [hz, hLu, show a + (b - a) = b from by module] at h
        exact h
      exact hb (hxb ▸ (hKsub hx).1)
  obtain ⟨p, hpK, hpmin⟩ :=
    hKcompact.exists_isMinOn hKnontriv.nonempty (continuous_coordAlong a u).continuousOn
  obtain ⟨q, hqK, hqmax⟩ :=
    hKcompact.exists_isMaxOn hKnontriv.nonempty (continuous_coordAlong a u).continuousOn
  have hc₁pos : 0 < coordAlong a u p := (hKcoord p hpK).2.1
  have hc₂lt : coordAlong a u q < L := (hKcoord q hqK).2.2
  have hc₁c₂ : coordAlong a u p ≤ coordAlong a u q := isMinOn_iff.1 hpmin q hqK
  set t₁ := coordAlong a u p / 2 with ht₁
  set t₂ := (coordAlong a u q + L) / 2 with ht₂
  have ht₁pos : 0 < t₁ := by rw [ht₁]; linarith
  have ht₁c₁ : t₁ < coordAlong a u p := by rw [ht₁]; linarith
  have hc₂t₂ : coordAlong a u q < t₂ := by rw [ht₂]; linarith
  have ht₂L : t₂ < L := by rw [ht₂]; linarith
  have ht₁t₂ : t₁ < t₂ := by linarith
  
  have hScompact : IsCompact ((fun c : ℝ => a + c • u) '' Icc t₁ t₂) :=
    isCompact_Icc.image (by fun_prop)
  have hSsub : (fun c : ℝ => a + c • u) '' Icc t₁ t₂ ⊆ D := by
    rintro _ ⟨c, hc, rfl⟩
    exact (hline c (lt_of_lt_of_le ht₁pos hc.1) (lt_of_le_of_lt hc.2 ht₂L)).1
  obtain ⟨ρ, hρ, hρD⟩ := Plane.exists_thickening_subset hScompact hDopen hSsub
  
  have hclose : ∀ x ∈ K, ∀ d : ℝ,
      dist x (a + (coordAlong a u x) • u + d • perp u) = |d| := by
    intro x hx d
    nth_rewrite 1 [eq_foot_of_coordAcross_eq_zero hu (hKcoord x hx).1]
    rw [dist_eq_norm,
      show a + (coordAlong a u x) • u -
        (a + (coordAlong a u x) • u + d • perp u) = (-d) • perp u from by module,
      norm_smul, Real.norm_eq_abs, norm_perp, hu.norm, mul_one, abs_neg]
  have hKt : ∀ x ∈ K, t₁ < coordAlong a u x ∧ coordAlong a u x < t₂ := fun x hx =>
    ⟨lt_of_lt_of_le ht₁c₁ (isMinOn_iff.1 hpmin x hx),
      lt_of_le_of_lt (isMaxOn_iff.1 hqmax x hx) hc₂t₂⟩
  refine ⟨{ nbhd := strip a u t₁ t₂ (-ρ) ρ
            left := strip a u t₁ t₂ 0 ρ
            right := strip a u t₁ t₂ (-ρ) 0
            isOpen_nbhd := isOpen_strip a u t₁ t₂ (-ρ) ρ
            subset_nbhd := ?_
            nbhd_subset := ?_
            nbhd_diff := ?_
            isConnected_left := ?_
            isConnected_right := ?_
            subset_closure_left := ?_
            subset_closure_right := ?_ }⟩
  · 
    intro x hx
    exact ⟨(hKt x hx).1, (hKt x hx).2, by rw [(hKcoord x hx).1]; linarith,
      by rw [(hKcoord x hx).1]; exact hρ⟩
  · 
    intro x hx
    refine hρD (mem_thickening_iff.2 ⟨a + (coordAlong a u x) • u, ⟨_, ⟨hx.1.le, hx.2.1.le⟩, rfl⟩,
      ?_⟩)
    rw [dist_foot hu, abs_lt]
    exact ⟨hx.2.2.1, hx.2.2.2⟩
  · 
    
    ext x
    simp only [mem_sdiff, mem_union, mem_strip_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
      rcases lt_trichotomy (coordAcross a u x) 0 with h | h | h
      · exact Or.inr ⟨h1, h2, h3, h⟩
      · exact absurd ((mem_segment_iff_coord hL hu hLu).2
          ⟨h, by linarith [ht₁pos], by linarith [ht₂L]⟩) h5
      · exact Or.inl ⟨h1, h2, h, h4⟩
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · refine ⟨⟨h1, h2, by linarith, h4⟩, fun hmem => ?_⟩
        linarith [((mem_segment_iff_coord hL hu hLu).1 hmem).1]
      · refine ⟨⟨h1, h2, h3, by linarith⟩, fun hmem => ?_⟩
        linarith [((mem_segment_iff_coord hL hu hLu).1 hmem).1]
  · exact (convex_strip a u t₁ t₂ 0 ρ).isConnected
      ⟨a + ((t₁ + t₂) / 2) • u + (ρ / 2) • perp u,
        (mem_strip_param hu a).2 ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · exact (convex_strip a u t₁ t₂ (-ρ) 0).isConnected
      ⟨a + ((t₁ + t₂) / 2) • u + (-(ρ / 2)) • perp u,
        (mem_strip_param hu a).2 ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hσ : 0 < min (ρ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
    refine ⟨a + (coordAlong a u x) • u + (min (ρ / 2) (ε / 2)) • perp u,
      (mem_strip_param hu a).2 ⟨(hKt x hx).1, (hKt x hx).2, hσ,
        lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩, ?_⟩
    rw [hclose x hx _, abs_of_pos hσ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hσ : 0 < min (ρ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
    refine ⟨a + (coordAlong a u x) • u + (-(min (ρ / 2) (ε / 2))) • perp u,
      (mem_strip_param hu a).2 ⟨(hKt x hx).1, (hKt x hx).2,
        by have := min_le_left (ρ / 2) (ε / 2); linarith, neg_neg_iff_pos.2 hσ⟩, ?_⟩
    rw [hclose x hx _, abs_neg, abs_of_pos hσ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

 

theorem segment_crosscut_at_most_two {a b : Plane} (hab : a ≠ b)
    (hDopen : IsOpen D) (hDconn : IsPreconnected D) (ha : a ∉ D) (hb : b ∉ D)
    (hPD : segment ℝ a b \ {a, b} ⊆ D) :
    ∃ zL ∈ D \ segment ℝ a b, ∃ zR ∈ D \ segment ℝ a b, ∀ x ∈ D \ segment ℝ a b,
      x ∈ connectedComponentIn (D \ segment ℝ a b) zL ∨
        x ∈ connectedComponentIn (D \ segment ℝ a b) zR :=
  crosscut_at_most_two hDopen hDconn (isArcBetween_segment hab) (isPolygonal_segment a b) ha hb
    hPD (hasArcCollars_segment hab hDopen ha hb hPD)

 

theorem crosscut_components_exhaust {a b v₁ v₂ : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (hPpoly : IsPolygonal P)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hcollars : HasArcCollars D P)
    (h₁ : v₁ ∈ D \ P) (h₂ : v₂ ∈ D \ P)
    (hne : connectedComponentIn (D \ P) v₁ ≠ connectedComponentIn (D \ P) v₂) :
    ∀ x ∈ D \ P, x ∈ connectedComponentIn (D \ P) v₁ ∨ x ∈ connectedComponentIn (D \ P) v₂ := by
  obtain ⟨zL, -, zR, -, hcov⟩ :=
    crosscut_at_most_two hDopen hDconn hP hPpoly ha hb hPD hcollars
  exact covered_by_two_components_of_ne hcov h₁ h₂ hne

end Schoenflies
