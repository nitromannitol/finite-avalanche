/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/PolygonalCrosscut.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.ParitySplitting

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 







































































open Bornology Set

namespace Schoenflies

variable {C J P Ω Ω' W V : Set Plane} {x y z : Plane}

 






 


def farRegion (C : Set Plane) (y : Plane) : Set Plane := Cᶜ \ connectedComponentIn Cᶜ y

theorem mem_farRegion_iff : x ∈ farRegion C y ↔ x ∉ C ∧ x ∉ connectedComponentIn Cᶜ y := Iff.rfl

theorem farRegion_subset_compl : farRegion C y ⊆ Cᶜ := fun _ hx => hx.1

theorem notMem_farRegion_self (hy : y ∉ C) : y ∉ farRegion C y :=
  fun h => h.2 (mem_connectedComponentIn hy)

 
theorem mem_farRegion_iff_connectedComponentIn_ne (hx : x ∉ C) :
    x ∈ farRegion C y ↔ connectedComponentIn Cᶜ x ≠ connectedComponentIn Cᶜ y := by
  refine ⟨fun h hEq => h.2 (hEq ▸ mem_connectedComponentIn hx), fun h => ⟨hx, fun hmem => ?_⟩⟩
  exact h (connectedComponentIn_eq hmem).symm

 
theorem diff_subset_farRegion (hdis : Disjoint P (connectedComponentIn Cᶜ y)) :
    P \ C ⊆ farRegion C y :=
  fun _ hz => ⟨hz.2, fun hmem => Set.disjoint_left.1 hdis hz.1 hmem⟩

theorem compl_diff_inside (C : Set Plane) : Cᶜ \ inside C = outside C := by
  ext w
  constructor
  · rintro ⟨hw, hwin⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_left hwin
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside h hw⟩

theorem compl_diff_outside (C : Set Plane) : Cᶜ \ outside C = inside C := by
  ext w
  constructor
  · rintro ⟨hw, hwout⟩
    have hcov : w ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hw
    exact hcov.resolve_right hwout
  · exact fun hw => ⟨hw.1, fun h => Set.disjoint_left.1 disjoint_inside_outside hw h⟩

 
theorem IsSeparating.isRegionPair_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionPair C (connectedComponentIn Cᶜ y) (farRegion C y) := by
  rcases hC.isRegionOf_connectedComponentIn hy with hc | hc
  · exact Or.inl ⟨hc, by rw [farRegion, hc, compl_diff_inside]⟩
  · exact Or.inr ⟨hc, by rw [farRegion, hc, compl_diff_outside]⟩

theorem IsSeparating.isRegionOf_farRegion (hC : IsSeparating C) (hy : y ∉ C) :
    IsRegionOf C (farRegion C y) := (hC.isRegionPair_farRegion hy).right

 

theorem IsSeparating.farRegion_eq_inside (hC : IsSeparating C) (hy : y ∈ outside C) :
    farRegion C y = inside C := by
  rw [farRegion, hC.connectedComponentIn_eq_outside hy, compl_diff_outside]

 
theorem IsSeparating.farRegion_eq_outside (hC : IsSeparating C) (hy : y ∈ inside C) :
    farRegion C y = outside C := by
  rw [farRegion, hC.connectedComponentIn_eq_inside hy, compl_diff_inside]

 





 
theorem compl_union_eq_of_isRegionPair (hΩ : IsRegionPair C Ω Ω') (hdis : Disjoint P Ω') :
    (C ∪ P)ᶜ = (Ω \ P) ∪ Ω' := by
  ext w
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff, not_or]
  constructor
  · rintro ⟨hwC, hwP⟩
    have hcov : w ∈ Ω ∪ Ω' := by rw [hΩ.union_eq]; exact hwC
    exact hcov.imp (fun h => ⟨h, hwP⟩) id
  · rintro (⟨hwΩ, hwP⟩ | hwΩ')
    · exact ⟨hΩ.left.subset_compl hwΩ, hwP⟩
    · exact ⟨hΩ.right.subset_compl hwΩ', fun hwP => Set.disjoint_left.1 hdis hwP hwΩ'⟩

 
theorem far_isComponent (hC : IsSeparating C) (hΩ : IsRegionPair C Ω Ω')
    (hdis : Disjoint P Ω') (hz : z ∈ Ω') : connectedComponentIn (C ∪ P)ᶜ z = Ω' := by
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hΩ.right.isOpen hC)
    (hΩ.right.isConnected hC).isPreconnected (fun w hw => ?_) ?_ hz
  · rintro (h | h)
    · exact hΩ.right.subset_compl hw h
    · exact Set.disjoint_left.1 hdis h hw
  · rw [hΩ.right.frontier_eq hC]
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro w ⟨hwC, hw⟩
    exact hw (Or.inl hwC)

 
theorem cell_isComponent_compl (hJ : IsSeparating J) (hWV : IsRegionPair J W V)
    (hJCP : J ⊆ C ∪ P) (hV : V ⊆ (C ∪ P)ᶜ) (hz : z ∈ V) :
    connectedComponentIn (C ∪ P)ᶜ z = V := by
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hWV.right.isOpen hJ)
    (hWV.right.isConnected hJ).isPreconnected hV ?_ hz
  rw [hWV.right.frontier_eq hJ]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwJ, hw⟩
  exact hw (hJCP hwJ)

 

 

theorem zmod_add_sub_cancel {m k : ℕ} (hk : k ≤ m + 3) (a : ZMod (m + 3)) :
    a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a := by
  have hcast : ((k : ℕ) : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = 0 := by
    rw [← Nat.cast_add, show k + (m + 3 - k) = m + 3 by omega]
    exact ZMod.natCast_self _
  rw [add_assoc, hcast, add_zero]

namespace ClosedPolygon

variable {m : ℕ} {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

 

def arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (C.arcPieces a k)

theorem arc_subset_carrier (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.arc a k ⊆ C.carrier := cover_arcPieces_subset C a k

 
theorem arc_union (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    C.arc a k ∪ C.arc (a + k) (m + 3 - k) = C.carrier := cover_arcPieces_union C a hk

 
theorem carrier_eq_arc_union {m' : ℕ} {J : ClosedPolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (C.arcPieces a k ++ K)) : J.carrier = C.arc a k ∪ cover K :=
  carrier_eq_of_sameEdges h

 



theorem parity_ne_iff_mem_farRegion (C : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ C.carrier) (hy : y ∉ C.carrier) :
    parity u C.pieces x ≠ parity u C.pieces y ↔ x ∈ farRegion C.carrier y := by
  rw [mem_farRegion_iff_connectedComponentIn_ne hx]
  constructor
  · intro hne heq
    exact hne (C.parity_eq_of_mem_connectedComponentIn_carrier hu hL hy
      (heq ▸ mem_connectedComponentIn hx))
  · intro hne
    rcases C.connectedComponentIn_eq_inside_or_outside hx with hxr | hxr <;>
      rcases C.connectedComponentIn_eq_inside_or_outside hy with hyr | hyr
    · exact absurd (hxr.trans hyr.symm) hne
    · rw [C.parity_eq_one_of_mem_inside hu hL (hxr ▸ mem_connectedComponentIn hx),
        C.parity_eq_zero_of_mem_outside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · rw [C.parity_eq_zero_of_mem_outside hu hL (hxr ▸ mem_connectedComponentIn hx),
        C.parity_eq_one_of_mem_inside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · exact absurd (hxr.trans hyr.symm) hne

 
theorem vertex_mem_arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    C.vertex a ∈ C.arc a k := by
  have h0 : a + ((0 : ℕ) : ZMod (m + 3)) = a := by rw [Nat.cast_zero, add_zero]
  refine mem_cover (P := (C.vertex a, C.vertex (a + 1))) ?_ ?_
  · exact List.mem_map.2 ⟨0, List.mem_range.2 hk, by rw [h0]⟩
  · exact left_mem_segment ℝ _ _

 
theorem vertex_add_mem_arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    C.vertex (a + k) ∈ C.arc a k := by
  have hlast : a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = a + (k : ZMod (m + 3)) := by
    have : ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = ((k : ℕ) : ZMod (m + 3)) := by
      rw [show ((k : ℕ) : ZMod (m + 3)) = (((k - 1) + 1 : ℕ) : ZMod (m + 3)) by
        congr 1; omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc, this]
  refine mem_cover (P := (C.vertex (a + ((k - 1 : ℕ) : ZMod (m + 3))),
    C.vertex (a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1))) ?_ ?_
  · exact List.mem_map.2 ⟨k - 1, List.mem_range.2 (by omega), rfl⟩
  · rw [Piece.seg, hlast]
    exact right_mem_segment ℝ _ _

 

theorem endpoints_subset_arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    ({C.vertex a, C.vertex (a + k)} : Set Plane) ⊆ C.arc a k := by
  rintro w (rfl | rfl)
  · exact C.vertex_mem_arc a hk
  · exact C.vertex_add_mem_arc a hk

 

theorem endpoints_subset_arc' (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk2 : k ≤ m + 2) :
    ({C.vertex a, C.vertex (a + k)} : Set Plane) ⊆ C.arc (a + k) (m + 3 - k) := by
  have hpos : 1 ≤ m + 3 - k := by omega
  have hwrap := zmod_add_sub_cancel (k := k) (by omega) a
  rintro w (rfl | rfl)
  · have hm := C.vertex_add_mem_arc (a + k) hpos
    rwa [hwrap] at hm
  · exact C.vertex_mem_arc (a + k) hpos

end ClosedPolygon

 

variable {m m₁ m₂ : ℕ} {C : ClosedPolygon m} {J₁ : ClosedPolygon m₁} {J₂ : ClosedPolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ}

 










structure IsPolygonalCrosscut (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁)
    (J₂ : ClosedPolygon m₂) (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (y : Plane) : Prop where
   
  le : k ≤ m + 3
   
  edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K)
   
  edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K)
   
  meets₁ : cover K ∩ C.carrier ⊆ C.arc a k
   
  meets₂ : cover K ∩ C.carrier ⊆ C.arc (a + k) (m + 3 - k)
   
  notMem : y ∉ C.carrier
   
  avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)

 



theorem IsPolygonalCrosscut.of_endpoints {y : Plane} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    (meets : cover K ∩ C.carrier ⊆ ({C.vertex a, C.vertex (a + k)} : Set Plane))
    (notMem : y ∉ C.carrier)
    (avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)) :
    IsPolygonalCrosscut C J₁ J₂ K a k y :=
  ⟨by omega, edges₁, edges₂, meets.trans (C.endpoints_subset_arc a hk1),
    meets.trans (C.endpoints_subset_arc' a hk2), notMem, avoids⟩

namespace IsPolygonalCrosscut

variable {y : Plane} (h : IsPolygonalCrosscut C J₁ J₂ K a k y)
include h

 
theorem symm : IsPolygonalCrosscut C J₂ J₁ K (a + k) (m + 3 - k) y := by
  have hk : k ≤ m + 3 := h.le
  have hnat : m + 3 - (m + 3 - k) = k := by omega
  have hzmod := zmod_add_sub_cancel (k := k) hk a
  refine ⟨by omega, h.edges₂, ?_, h.meets₂, ?_, h.notMem, h.avoids⟩
  · rw [hzmod, hnat]; exact h.edges₁
  · rw [hzmod, hnat]; exact h.meets₁

 

theorem notMem_cover : y ∉ cover K :=
  fun hy => Set.disjoint_left.1 h.avoids hy (mem_connectedComponentIn h.notMem)

theorem carrier₁ : J₁.carrier = C.arc a k ∪ cover K :=
  ClosedPolygon.carrier_eq_arc_union h.edges₁

theorem notMem_carrier₁ : y ∉ J₁.carrier :=
  ClosedPolygon.notMem_carrier_of_sameEdges h.edges₁ h.notMem h.notMem_cover

theorem cover_subset_carrier₁ : cover K ⊆ J₁.carrier := by
  rw [h.carrier₁]; exact Set.subset_union_right

theorem carrier₁_subset : J₁.carrier ⊆ C.carrier ∪ cover K := by
  rw [h.carrier₁]
  exact Set.union_subset_union_left _ (C.arc_subset_carrier a k)

 
theorem nondeg : ∀ Q ∈ K, Q.Nondeg := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.edges₁.symm.exists_mem (List.mem_append_right _ hQ)
  have hRn : (orientPiece R).Nondeg := orientPiece_nondeg (J₁.pieces_nondeg R hR)
  rw [hRQ] at hRn
  rcases orientPiece_eq_or Q with e | e
  · rw [e] at hRn; exact hRn
  · rw [e] at hRn; exact fun hh => hRn hh.symm

 
theorem exists_direction : ∃ u : Plane, Plane.IsDirection u ∧
    (∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) ∧ (∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) := by
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ K) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ' | hQ'
    · exact C.pieces_nondeg Q hQ'
    · exact h.nondeg Q hQ')
  exact ⟨u, hu, fun Q hQ => hlev Q (List.mem_append_left _ hQ),
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)⟩

 






theorem regionPairC :
    IsRegionPair C.carrier (farRegion C.carrier y) (connectedComponentIn C.carrierᶜ y) :=
  (C.isSeparating_carrier.isRegionPair_farRegion h.notMem).symm

theorem regionPair₁ :
    IsRegionPair J₁.carrier (connectedComponentIn J₁.carrierᶜ y) (farRegion J₁.carrier y) :=
  J₁.isSeparating_carrier.isRegionPair_farRegion h.notMem_carrier₁

 
theorem near_subset₁ :
    connectedComponentIn C.carrierᶜ y ⊆ connectedComponentIn J₁.carrierᶜ y := by
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_connectedComponentIn h.notMem) (fun w hw => ?_)
  have hwC : w ∉ C.carrier := connectedComponentIn_subset _ _ hw
  have hwK : w ∉ cover K := fun hK => Set.disjoint_left.1 h.avoids hK hw
  exact ClosedPolygon.notMem_carrier_of_sameEdges h.edges₁ hwC hwK

 
theorem cell_subset₁ : farRegion J₁.carrier y ⊆ farRegion C.carrier y \ cover K :=
  cell_subset_region_diff (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁

theorem cell_subset₂ : farRegion J₂.carrier y ⊆ farRegion C.carrier y \ cover K :=
  h.symm.cell_subset₁

 
theorem cell_isComponent₁ : ∀ z ∈ farRegion J₁.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₁.carrier y :=
  cell_isComponent (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁ h.carrier₁_subset

theorem cell_isComponent₂ : ∀ z ∈ farRegion J₂.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₂.carrier y :=
  h.symm.cell_isComponent₁

 
theorem closure_cell_inter₁ : closure (farRegion J₁.carrier y) ∩ C.carrier = C.arc a k := by
  rw [closure_cell_inter_curve C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC.right h.regionPair₁ h.near_subset₁, h.carrier₁]
  refine Set.Subset.antisymm ?_ (fun w hw => ⟨Or.inl hw, C.arc_subset_carrier a k hw⟩)
  rintro w ⟨hw | hw, hwC⟩
  · exact hw
  · exact h.meets₁ ⟨hw, hwC⟩

theorem closure_cell_inter₂ :
    closure (farRegion J₂.carrier y) ∩ C.carrier = C.arc (a + k) (m + 3 - k) :=
  h.symm.closure_cell_inter₁

 
theorem frontier_cell₁ : frontier (farRegion J₁.carrier y) = J₁.carrier :=
  h.regionPair₁.right.frontier_eq J₁.isSeparating_carrier

theorem frontier_cell₂ : frontier (farRegion J₂.carrier y) = J₂.carrier :=
  h.symm.frontier_cell₁

theorem cell_nonempty₁ : (farRegion J₁.carrier y).Nonempty :=
  (h.regionPair₁.right.isConnected J₁.isSeparating_carrier).nonempty

 



 



theorem separates_xor {x : Plane} (hxC : x ∉ C.carrier) (hxK : x ∉ cover K) :
    x ∈ farRegion C.carrier y ↔
      (x ∈ farRegion J₁.carrier y ↔ ¬ x ∈ farRegion J₂.carrier y) := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  have hlev₁ := h.edges₁.hgt_ne (ClosedPolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hlev₂ := h.edges₂.hgt_ne (ClosedPolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hxJ₁ := ClosedPolygon.notMem_carrier_of_sameEdges h.edges₁ hxC hxK
  have hxJ₂ := ClosedPolygon.notMem_carrier_of_sameEdges h.edges₂ hxC hxK
  rw [← C.parity_ne_iff_mem_farRegion hu hlevC hxC h.notMem,
    ← J₁.parity_ne_iff_mem_farRegion hu hlev₁ hxJ₁ h.notMem_carrier₁,
    ← J₂.parity_ne_iff_mem_farRegion hu hlev₂ hxJ₂ h.symm.notMem_carrier₁]
  have hsx := C.parity_splitting u a h.le h.edges₁ h.edges₂ x
  have hsy := C.parity_splitting u a h.le h.edges₁ h.edges₂ y
  have key : ∀ s₁ s₂ s t₁ t₂ t : ZMod 2, s₁ + s₂ = s → t₁ + t₂ = t →
      (s ≠ t ↔ ((s₁ ≠ t₁) ↔ ¬ (s₂ ≠ t₂))) := by decide
  exact key _ _ _ _ _ _ hsx hsy

 

theorem region_eq :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  refine Set.Subset.antisymm ?_ (Set.union_subset h.cell_subset₁ h.cell_subset₂)
  rintro w ⟨hwΩ, hwK⟩
  by_cases hw₁ : w ∈ farRegion J₁.carrier y
  · exact Or.inl hw₁
  · refine Or.inr ?_
    by_contra hw₂
    exact hw₁ (((h.separates_xor hwΩ.1 hwK).1 hwΩ).2 hw₂)

theorem cells_disjoint : Disjoint (farRegion J₁.carrier y) (farRegion J₂.carrier y) := by
  rw [Set.disjoint_left]
  intro w hw₁ hw₂
  obtain ⟨hwΩ, hwK⟩ := h.cell_subset₁ hw₁
  exact ((h.separates_xor hwΩ.1 hwK).1 hwΩ).1 hw₁ hw₂

theorem cells_ne : farRegion J₁.carrier y ≠ farRegion J₂.carrier y := by
  intro heq
  obtain ⟨w, hw⟩ := h.cell_nonempty₁
  exact Set.disjoint_left.1 h.cells_disjoint hw (heq ▸ hw)

 
theorem cell_ne_near₁ : farRegion J₁.carrier y ≠ connectedComponentIn C.carrierᶜ y := by
  intro heq
  obtain ⟨w, hw⟩ := h.cell_nonempty₁
  exact Set.disjoint_left.1 h.regionPairC.disjoint (h.cell_subset₁ hw).1 (heq ▸ hw)

theorem cell_ne_near₂ : farRegion J₂.carrier y ≠ connectedComponentIn C.carrierᶜ y :=
  h.symm.cell_ne_near₁

 

theorem cell_subset_compl₁ : farRegion J₁.carrier y ⊆ (C.carrier ∪ cover K)ᶜ := by
  intro w hw
  obtain ⟨hwΩ, hwK⟩ := h.cell_subset₁ hw
  rintro (hw' | hw')
  · exact hwΩ.1 hw'
  · exact hwK hw'

 
theorem compl_eq : (C.carrier ∪ cover K)ᶜ =
    (farRegion J₁.carrier y ∪ farRegion J₂.carrier y) ∪ connectedComponentIn C.carrierᶜ y := by
  rw [← h.region_eq]
  exact compl_union_eq_of_isRegionPair h.regionPairC h.avoids

 
theorem near_isComponent {z : Plane} (hz : z ∈ connectedComponentIn C.carrierᶜ y) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = connectedComponentIn C.carrierᶜ y :=
  far_isComponent C.isSeparating_carrier h.regionPairC h.avoids hz

theorem frontier_near :
    frontier (connectedComponentIn C.carrierᶜ y) = C.carrier :=
  h.regionPairC.right.frontier_eq C.isSeparating_carrier

 
theorem cell_isComponent_compl₁ {z : Plane} (hz : z ∈ farRegion J₁.carrier y) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₁.carrier y :=
  cell_isComponent_compl J₁.isSeparating_carrier h.regionPair₁ h.carrier₁_subset
    h.cell_subset_compl₁ hz

theorem cell_isComponent_compl₂ {z : Plane} (hz : z ∈ farRegion J₂.carrier y) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₂.carrier y :=
  h.symm.cell_isComponent_compl₁ hz

 


theorem isComponent {z : Plane} (hz : z ∉ C.carrier ∪ cover K) :
    connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₁.carrier y ∨
      connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₂.carrier y ∨
      connectedComponentIn (C.carrier ∪ cover K)ᶜ z = connectedComponentIn C.carrierᶜ y := by
  have hmem : z ∈ (C.carrier ∪ cover K)ᶜ := hz
  rw [h.compl_eq] at hmem
  rcases hmem with (h₁ | h₂) | h₃
  · exact Or.inl (h.cell_isComponent_compl₁ h₁)
  · exact Or.inr (Or.inl (h.cell_isComponent_compl₂ h₂))
  · exact Or.inr (Or.inr (h.near_isComponent h₃))

 

 

theorem mem_outside₁ (hy : y ∈ outside C.carrier) : y ∈ outside J₁.carrier := by
  rcases J₁.isSeparating_carrier.isRegionOf_connectedComponentIn h.notMem_carrier₁ with hc | hc
  · refine absurd ?_ C.isSeparating_carrier.not_isBounded_outside
    refine J₁.isSeparating_carrier.isBounded_inside.subset ?_
    rw [← hc, ← C.isSeparating_carrier.connectedComponentIn_eq_outside hy]
    exact h.near_subset₁
  · exact hc ▸ mem_connectedComponentIn h.notMem_carrier₁

theorem cell₁_eq_inside (hy : y ∈ outside C.carrier) :
    farRegion J₁.carrier y = inside J₁.carrier :=
  J₁.isSeparating_carrier.farRegion_eq_inside (h.mem_outside₁ hy)

theorem cell₂_eq_inside (hy : y ∈ outside C.carrier) :
    farRegion J₂.carrier y = inside J₂.carrier :=
  h.symm.cell₁_eq_inside hy

 


theorem inside_diff_eq (hy : y ∈ outside C.carrier) :
    inside C.carrier \ cover K = inside J₁.carrier ∪ inside J₂.carrier := by
  rw [← C.isSeparating_carrier.farRegion_eq_inside hy, ← h.cell₁_eq_inside hy,
    ← h.cell₂_eq_inside hy]
  exact h.region_eq

 




theorem outside_diff_eq (hy : y ∈ inside C.carrier) :
    outside C.carrier \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  rw [← C.isSeparating_carrier.farRegion_eq_outside hy]
  exact h.region_eq

 

theorem inside_exactly_one (hy : y ∈ inside C.carrier) :
    y ∈ inside J₁.carrier ↔ y ∉ inside J₂.carrier := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  exact C.crosscut_inside_exactly_one J₁ J₂ hu hlevC hlevK h.le h.edges₁ h.edges₂ hy
    h.notMem_cover

end IsPolygonalCrosscut

 












theorem polygonal_crosscut {y : Plane} (h : IsPolygonalCrosscut C J₁ J₂ K a k y) :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y ∧
      Disjoint (farRegion J₁.carrier y) (farRegion J₂.carrier y) ∧
      (∀ z ∈ farRegion J₁.carrier y,
        connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₁.carrier y) ∧
      (∀ z ∈ farRegion J₂.carrier y,
        connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₂.carrier y) ∧
      frontier (farRegion J₁.carrier y) = J₁.carrier ∧
      frontier (farRegion J₂.carrier y) = J₂.carrier ∧
      closure (farRegion J₁.carrier y) ∩ C.carrier = C.arc a k ∧
      closure (farRegion J₂.carrier y) ∩ C.carrier = C.arc (a + k) (m + 3 - k) ∧
      (∀ z ∉ C.carrier ∪ cover K,
        connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₁.carrier y ∨
          connectedComponentIn (C.carrier ∪ cover K)ᶜ z = farRegion J₂.carrier y ∨
          connectedComponentIn (C.carrier ∪ cover K)ᶜ z = connectedComponentIn C.carrierᶜ y) :=
  ⟨h.region_eq, h.cells_disjoint, h.cell_isComponent₁, h.cell_isComponent₂, h.frontier_cell₁,
    h.frontier_cell₂, h.closure_cell_inter₁, h.closure_cell_inter₂, fun _ hz => h.isComponent hz⟩

end Schoenflies
