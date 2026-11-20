/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/GeneralCrosscut.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.CrosscutCells
import FiniteAvalanches.Support.Schoenflies.CrosscutAtMostTwo
import FiniteAvalanches.Support.Schoenflies.TwoArcs

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




























































open Bornology Set unitInterval

namespace Schoenflies

variable {C P A A₁ A₂ : Set Plane} {p q z : Plane}

 





 

theorem IsArcBetween.not_subset_pair (h : IsArcBetween A p q) : ¬ A ⊆ ({p, q} : Set Plane) := by
  obtain ⟨f, -, hi, rfl, rfl, rfl⟩ := h
  intro hsub
  have hhalf : (1 / 2 : ℝ) ∈ I := ⟨by norm_num, by norm_num⟩
  have hmem := hsub (mem_image_of_mem f hhalf)
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with h' | h'
  · exact absurd (hi hhalf zero_mem_I h') (by norm_num)
  · exact absurd (hi hhalf one_mem_I h') (by norm_num)

 








 

structure IsCrosscut (C P : Set Plane) (p q : Plane) : Prop where
   
  curve : IsJordanCurve C
   
  arc : IsArcBetween P p q
   
  polygonal : IsPolygonal P
   
  left_mem : p ∈ C
   
  right_mem : q ∈ C
   
  sdiff_subset : P \ {p, q} ⊆ inside C

 

structure IsCutPair (C : Set Plane) (p q : Plane) (A₁ A₂ : Set Plane) : Prop where
   
  fst : IsArcBetween A₁ p q
   
  snd : IsArcBetween A₂ p q
   
  union_eq : A₁ ∪ A₂ = C
   
  inter_eq : A₁ ∩ A₂ = {p, q}

namespace IsCutPair

 

theorem symm (h : IsCutPair C p q A₁ A₂) : IsCutPair C p q A₂ A₁ :=
  ⟨h.snd, h.fst, by rw [union_comm]; exact h.union_eq, by rw [inter_comm]; exact h.inter_eq⟩

theorem fst_subset (h : IsCutPair C p q A₁ A₂) : A₁ ⊆ C := by
  rw [← h.union_eq]; exact subset_union_left

theorem snd_subset (h : IsCutPair C p q A₁ A₂) : A₂ ⊆ C := h.symm.fst_subset

 
theorem ne (h : IsCutPair C p q A₁ A₂) : A₁ ≠ A₂ :=
  arcs_ne h.inter_eq.subset h.fst.not_subset_pair

end IsCutPair

 

theorem exists_isCutPair (hC : IsJordanCurve C) (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A₁ A₂, IsCutPair C p q A₁ A₂ := by
  obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hC.two_arcs hp hq hpq
  exact ⟨A, B, hA, hB, hcov, hmeet⟩

 




namespace IsCrosscut

theorem left_notMem_inside (h : IsCrosscut C P p q) : p ∉ inside C := fun hp =>
  inside_subset_compl hp h.left_mem

theorem right_notMem_inside (h : IsCrosscut C P p q) : q ∉ inside C := fun hq =>
  inside_subset_compl hq h.right_mem

 

theorem inter_eq (h : IsCrosscut C P p q) : P ∩ C = {p, q} := by
  refine Subset.antisymm (fun z hz => ?_) (pair_subset ⟨h.arc.left_mem, h.left_mem⟩
    ⟨h.arc.right_mem, h.right_mem⟩)
  by_contra hzpq
  exact inside_subset_compl (h.sdiff_subset ⟨hz.1, hzpq⟩) hz.2

 

theorem disjoint_outside (h : IsCrosscut C P p q) : Disjoint P (outside C) := by
  rw [disjoint_left]
  intro z hzP hzO
  by_cases hz : z ∈ ({p, q} : Set Plane)
  · rcases hz with rfl | rfl
    exacts [hzO.1 h.left_mem, hzO.1 h.right_mem]
  · exact disjoint_left.1 disjoint_inside_outside (h.sdiff_subset ⟨hzP, hz⟩) hzO

 

theorem inter_subset_arc (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    P ∩ C ⊆ A₁ := by
  rw [h.inter_eq]
  exact pair_subset hcut.fst.left_mem hcut.fst.right_mem

 


theorem arc_union_inter (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    (A₁ ∪ P) ∩ C = A₁ := by
  refine Subset.antisymm ?_ fun z hz => ⟨Or.inl hz, hcut.fst_subset hz⟩
  rintro z ⟨hz | hz, hzC⟩
  · exact hz
  · exact h.inter_subset_arc hcut ⟨hz, hzC⟩

 

theorem isJordanCurve_union (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    IsJordanCurve (A₁ ∪ P) := by
  refine _root_.Schoenflies.isJordanCurve_union hcut.fst h.arc fun z hzA hzP => ?_
  have hz : z ∈ ({p, q} : Set Plane) := h.inter_eq ▸ ⟨hzP, hcut.fst_subset hzA⟩
  simpa using hz

 




theorem isSeparating_curve (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) : IsSeparating C :=
  hjordan C h.curve

theorem isSeparating_union (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : IsSeparating (A₁ ∪ P) :=
  hjordan _ (h.isJordanCurve_union hcut)

 




theorem outside_subset_outside_union
    (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hA : A ⊆ C) : outside C ⊆ outside (A ∪ P) := by
  have hsep := h.isSeparating_curve hjordan
  have hsub : outside C ⊆ (A ∪ P)ᶜ := by
    rintro z hz (hzA | hzP)
    · exact hz.1 (hA hzA)
    · exact disjoint_left.1 h.disjoint_outside hzP hz
  intro z hz
  refine ⟨hsub hz, fun hb => hsep.not_isBounded_outside (hb.subset ?_)⟩
  exact hsep.isConnected_outside.isPreconnected.subset_connectedComponentIn hz hsub

 

theorem isRegionPair_curve (C : Set Plane) : IsRegionPair C (inside C) (outside C) :=
  Or.inl ⟨rfl, rfl⟩

 
theorem isRegionPair_union (J : Set Plane) : IsRegionPair J (outside J) (inside J) :=
  Or.inr ⟨rfl, rfl⟩

 





 
theorem side_subset (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside (A₁ ∪ P) ⊆ inside C \ P :=
  cell_subset_region_diff (h.isSeparating_curve hjordan) (h.isSeparating_union hjordan hcut)
    (isRegionPair_curve C) (isRegionPair_union (A₁ ∪ P))
    (h.outside_subset_outside_union hjordan hcut.fst_subset) subset_union_right

 

theorem side_isComponent (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    ∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) :=
  cell_isComponent (h.isSeparating_curve hjordan) (h.isSeparating_union hjordan hcut)
    (isRegionPair_curve C) (isRegionPair_union (A₁ ∪ P))
    (h.outside_subset_outside_union hjordan hcut.fst_subset) subset_union_right
    (union_subset_union_left P hcut.fst_subset)

 


theorem closure_side_inter (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    closure (inside (A₁ ∪ P)) ∩ C = A₁ := by
  rw [closure_cell_inter_curve (h.isSeparating_curve hjordan) (h.isSeparating_union hjordan hcut)
    (IsRegionOf.outside C) (isRegionPair_union (A₁ ∪ P))
    (h.outside_subset_outside_union hjordan hcut.fst_subset)]
  exact h.arc_union_inter hcut

 
theorem side_ne (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) := by
  intro heq
  have h₁ := h.closure_side_inter hjordan hcut
  have h₂ := h.closure_side_inter hjordan hcut.symm
  rw [heq] at h₁
  exact hcut.ne (h₁.symm.trans h₂)

theorem side_nonempty (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : (inside (A₁ ∪ P)).Nonempty :=
  (h.isSeparating_union hjordan hcut).isConnected_inside.nonempty

theorem isOpen_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : IsOpen (inside (A₁ ∪ P)) :=
  (h.isSeparating_union hjordan hcut).isOpen_inside

theorem isConnected_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : IsConnected (inside (A₁ ∪ P)) :=
  (h.isSeparating_union hjordan hcut).isConnected_inside

theorem isBounded_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    IsBounded (inside (A₁ ∪ P)) :=
  (h.isSeparating_union hjordan hcut).isBounded_inside

 
theorem frontier_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    frontier (inside (A₁ ∪ P)) = A₁ ∪ P :=
  (h.isSeparating_union hjordan hcut).frontier_inside

 

theorem closure_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) :=
  (IsRegionOf.inside (A₁ ∪ P)).closure_eq (h.isSeparating_union hjordan hcut)

 
theorem disjoint_sides (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) := by
  rw [disjoint_left]
  intro z hz₁ hz₂
  exact h.side_ne hjordan hcut
    ((h.side_isComponent hjordan hcut z hz₁).symm.trans
      (h.side_isComponent hjordan hcut.symm z hz₂))

 




 

theorem components_eq (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    ∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
      connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P) := by
  have hsep := h.isSeparating_curve hjordan
  obtain ⟨v₁, hv₁⟩ := h.side_nonempty hjordan hcut
  obtain ⟨v₂, hv₂⟩ := h.side_nonempty hjordan hcut.symm
  have hc₁ := h.side_isComponent hjordan hcut v₁ hv₁
  have hc₂ := h.side_isComponent hjordan hcut.symm v₂ hv₂
  have hexh := crosscut_components_exhaust hsep.isOpen_inside
    hsep.isConnected_inside.isPreconnected h.arc h.polygonal
    h.left_notMem_inside h.right_notMem_inside h.sdiff_subset hcollars
    (h.side_subset hjordan hcut hv₁) (h.side_subset hjordan hcut.symm hv₂)
    (by rw [hc₁, hc₂]; exact h.side_ne hjordan hcut)
  intro z hz
  rcases hexh z hz with hzz | hzz
  · rw [hc₁] at hzz
    exact Or.inl (h.side_isComponent hjordan hcut z hzz)
  · rw [hc₂] at hzz
    exact Or.inr (h.side_isComponent hjordan hcut.symm z hzz)

 
theorem inside_diff_eq (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by
  refine Subset.antisymm (fun z hz => ?_)
    (union_subset (h.side_subset hjordan hcut) (h.side_subset hjordan hcut.symm))
  rcases h.components_eq hjordan hcut hcollars z hz with heq | heq
  · exact Or.inl (heq ▸ mem_connectedComponentIn hz)
  · exact Or.inr (heq ▸ mem_connectedComponentIn hz)

end IsCrosscut

 







theorem general_crosscut (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧ closure (inside (A₂ ∪ P)) ∩ C = A₂ :=
  ⟨h.inside_diff_eq hjordan hcut hcollars, h.disjoint_sides hjordan hcut,
    h.side_nonempty hjordan hcut, h.side_nonempty hjordan hcut.symm, h.side_ne hjordan hcut,
    h.side_isComponent hjordan hcut, h.side_isComponent hjordan hcut.symm,
    h.components_eq hjordan hcut hcollars, h.closure_side_inter hjordan hcut,
    h.closure_side_inter hjordan hcut.symm⟩

 






namespace IsCrosscut

 

theorem compl_eq (h : IsCrosscut C P p q) : (C ∪ P)ᶜ = outside C ∪ (inside C \ P) := by
  refine Subset.antisymm (fun z hz => ?_) ?_
  · have hzC : z ∉ C := fun hzc => hz (Or.inl hzc)
    have hzP : z ∉ P := fun hzp => hz (Or.inr hzp)
    have hz' : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hzC
    rcases hz' with hzi | hzo
    · exact Or.inr ⟨hzi, hzP⟩
    · exact Or.inl hzo
  · rintro z (hzo | ⟨hzi, hzP⟩) (hzc | hzp)
    · exact hzo.1 hzc
    · exact disjoint_left.1 h.disjoint_outside hzp hzo
    · exact hzi.1 hzc
    · exact hzP hzp

 
theorem compl_eq_three (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    (C ∪ P)ᶜ = outside C ∪ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by
  rw [h.compl_eq, h.inside_diff_eq hjordan hcut hcollars, union_assoc]

theorem outside_subset_compl (h : IsCrosscut C P p q) : outside C ⊆ (C ∪ P)ᶜ := by
  rw [h.compl_eq]; exact subset_union_left

theorem side_subset_compl (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside (A₁ ∪ P) ⊆ (C ∪ P)ᶜ := by
  intro w hw
  obtain ⟨hwD, hwP⟩ := h.side_subset hjordan hcut hw
  rintro (hwC | hwP')
  · exact inside_subset_compl hwD hwC
  · exact hwP hwP'

 

theorem outside_isComponent (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) :
    ∀ z ∈ outside C, connectedComponentIn (C ∪ P)ᶜ z = outside C := by
  have hsep := h.isSeparating_curve hjordan
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint hsep.isOpen_outside
    hsep.isConnected_outside.isPreconnected h.outside_subset_compl ?_ hz
  rw [hsep.frontier_outside]
  exact eq_empty_iff_forall_notMem.2 fun w hw => hw.2 (Or.inl hw.1)

 

theorem side_isComponent_compl (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    ∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) := by
  have hJ := h.isSeparating_union hjordan hcut
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint hJ.isOpen_inside
    hJ.isConnected_inside.isPreconnected (h.side_subset_compl hjordan hcut) ?_ hz
  rw [hJ.frontier_inside]
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwA | hwP, hw⟩
  · exact hw (Or.inl (hcut.fst_subset hwA))
  · exact hw (Or.inr hwP)

 
theorem three_regions (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    ∀ z ∈ (C ∪ P)ᶜ, connectedComponentIn (C ∪ P)ᶜ z = outside C ∨
      connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) ∨
      connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P) := by
  intro z hz
  rw [h.compl_eq_three hjordan hcut hcollars] at hz
  rcases hz with (hz | hz) | hz
  · exact Or.inl (h.outside_isComponent hjordan z hz)
  · exact Or.inr (Or.inl (h.side_isComponent_compl hjordan hcut z hz))
  · exact Or.inr (Or.inr (h.side_isComponent_compl hjordan hcut.symm z hz))

 
theorem disjoint_outside_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    Disjoint (outside C) (inside (A₁ ∪ P)) := by
  rw [disjoint_left]
  intro w hw hw'
  exact disjoint_left.1 disjoint_inside_outside (h.side_subset hjordan hcut hw').1 hw

 
theorem outside_ne_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    outside C ≠ inside (A₁ ∪ P) := by
  intro heq
  obtain ⟨w, hw⟩ := h.side_nonempty hjordan hcut
  exact disjoint_left.1 (h.disjoint_outside_side hjordan hcut) (heq ▸ hw) hw

end IsCrosscut

 






theorem general_crosscut_three_regions
    (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    (C ∪ P)ᶜ = outside C ∪ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      (∀ z ∈ outside C, connectedComponentIn (C ∪ P)ᶜ z = outside C) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ (C ∪ P)ᶜ, connectedComponentIn (C ∪ P)ᶜ z = outside C ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      Disjoint (outside C) (inside (A₁ ∪ P)) ∧ Disjoint (outside C) (inside (A₂ ∪ P)) ∧
        Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      outside C ≠ inside (A₁ ∪ P) ∧ outside C ≠ inside (A₂ ∪ P) ∧
        inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      frontier (outside C) = C ∧ frontier (inside (A₁ ∪ P)) = A₁ ∪ P ∧
        frontier (inside (A₂ ∪ P)) = A₂ ∪ P :=
  ⟨h.compl_eq_three hjordan hcut hcollars, h.outside_isComponent hjordan,
    h.side_isComponent_compl hjordan hcut, h.side_isComponent_compl hjordan hcut.symm,
    h.three_regions hjordan hcut hcollars,
    h.disjoint_outside_side hjordan hcut, h.disjoint_outside_side hjordan hcut.symm,
    h.disjoint_sides hjordan hcut,
    h.outside_ne_side hjordan hcut, h.outside_ne_side hjordan hcut.symm,
    h.side_ne hjordan hcut,
    (h.isSeparating_curve hjordan).frontier_outside,
    h.frontier_side hjordan hcut, h.frontier_side hjordan hcut.symm⟩

end Schoenflies
