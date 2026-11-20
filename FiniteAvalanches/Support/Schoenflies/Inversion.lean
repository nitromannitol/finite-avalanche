/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Inversion.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Accessible
import FiniteAvalanches.Support.Schoenflies.Jordan
import Mathlib.Geometry.Euclidean.Inversion.Basic

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





















































































open Bornology Metric Set

namespace Schoenflies

variable {C Ω : Set Plane} {a p x y : Plane} {ε : ℝ}

 






 

noncomputable def invert (a x : Plane) : Plane := EuclideanGeometry.inversion a 1 x

theorem invert_apply (a x : Plane) : invert a x = a + (‖x - a‖ ^ 2)⁻¹ • (x - a) := by
  unfold invert EuclideanGeometry.inversion
  rw [dist_eq_norm]
  simp [add_comm]

@[simp] theorem invert_center (a : Plane) : invert a a = a :=
  EuclideanGeometry.inversion_self a 1

 
theorem dist_invert_center (a x : Plane) : dist (invert a x) a = (dist x a)⁻¹ := by
  rw [invert, EuclideanGeometry.dist_inversion_center]
  simp

theorem invert_invert (a x : Plane) : invert a (invert a x) = x :=
  EuclideanGeometry.inversion_inversion a one_ne_zero x

theorem invert_involutive (a : Plane) : Function.Involutive (invert a) := invert_invert a

theorem invert_injective (a : Plane) : Function.Injective (invert a) :=
  (invert_involutive a).injective

 

theorem invert_image_eq_preimage (a : Plane) (S : Set Plane) :
    invert a '' S = invert a ⁻¹' S :=
  congrFun (invert_involutive a).image_eq_preimage_symm S

@[simp] theorem invert_image_invert_image (a : Plane) (S : Set Plane) :
    invert a '' (invert a '' S) = S := by
  simp [← Set.image_comp, invert_invert]

theorem invert_eq_center_iff : invert a x = a ↔ x = a :=
  EuclideanGeometry.inversion_eq_center one_ne_zero

theorem invert_ne_center (h : x ≠ a) : invert a x ≠ a := fun hc => h (invert_eq_center_iff.1 hc)

theorem continuousAt_invert (h : x ≠ a) : ContinuousAt (invert a) x :=
  ContinuousAt.inversion continuousAt_const continuousAt_const continuousAt_id h

theorem continuousOn_invert (a : Plane) : ContinuousOn (invert a) ({a}ᶜ : Set Plane) :=
  fun _ hx => (continuousAt_invert (by simpa using hx)).continuousWithinAt

 

theorem isOpen_invert_image {S : Set Plane} (hS : IsOpen S) (ha : a ∉ S) :
    IsOpen (invert a '' S) := by
  rw [invert_image_eq_preimage]
  refine (continuousOn_invert a).isOpen_preimage isOpen_compl_singleton ?_ hS
  intro z hz
  simp only [mem_compl_iff, mem_singleton_iff]
  rintro rfl
  exact ha (by simpa using hz)

 
@[simps! -isSimp apply]
noncomputable def invertHomeo (a : Plane) : ({a}ᶜ : Set Plane) ≃ₜ ({a}ᶜ : Set Plane) where
  toFun z := ⟨invert a z, fun h =>
    z.2 (mem_singleton_iff.2 (invert_eq_center_iff.1 (mem_singleton_iff.1 h)))⟩
  invFun z := ⟨invert a z, fun h =>
    z.2 (mem_singleton_iff.2 (invert_eq_center_iff.1 (mem_singleton_iff.1 h)))⟩
  left_inv z := Subtype.ext (invert_invert a z)
  right_inv z := Subtype.ext (invert_invert a z)
  continuous_toFun := ((continuousOn_invert a).restrict).subtype_mk _
  continuous_invFun := ((continuousOn_invert a).restrict).subtype_mk _

 




 

theorem IsJordanCurve.invert_image (hC : IsJordanCurve C) (ha : a ∉ C) :
    IsJordanCurve (invert a '' C) := by
  obtain ⟨f, hf, rfl⟩ := hC
  have hmaps : MapsTo f unitInterval ({a}ᶜ : Set Plane) := by
    intro t ht
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact ha ⟨t, ht, rfl⟩
  refine ⟨invert a ∘ f, ⟨(continuousOn_invert a).comp hf.continuousOn hmaps, ?_, ?_⟩, ?_⟩
  · simp only [Function.comp_apply, hf.closes]
  · exact ((invert_injective a).injOn).comp hf.injOn (mapsTo_univ _ _)
  · rw [Set.image_comp]

 





 

theorem exists_radius_compl_closedBall_subset_outside (hC : IsSeparating C) (a : Plane) :
    ∃ R > 0, (closedBall a R)ᶜ ⊆ outside C := by
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall a).1
    (hC.isJordanCurve.isCompact.isBounded.union hC.isBounded_inside)
  refine ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
  have hz' : z ∉ C ∪ inside C := fun h =>
    hz (closedBall_subset_closedBall (le_max_left _ _) (hr h))
  have hzc : z ∈ inside C ∪ outside C := by
    rw [inside_union_outside]
    exact fun h => hz' (Or.inl h)
  exact hzc.resolve_left fun h => hz' (Or.inr h)

 





theorem invert_image_outside_union_singleton
    (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' outside C ∪ {a} = inside (invert a '' C) := by
  have hsep : IsSeparating C := hC.isSeparating harc
  have haC : a ∉ C := ha.1
  have haout : a ∉ outside C := Set.disjoint_left.1 disjoint_inside_outside ha
  have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact haout hz
  
  obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
  obtain ⟨δ, hδ, hδin⟩ := Metric.isOpen_iff.1 hsep.isOpen_inside a ha
  have hTopen : IsOpen (invert a '' outside C) :=
    isOpen_invert_image hsep.isOpen_outside haout
  
  have hfar : ∀ z ∈ outside C, δ ≤ dist z a := by
    intro z hz
    by_contra h
    push Not at h
    exact Set.disjoint_left.1 disjoint_inside_outside (hδin (mem_ball.2 h)) hz
  
  have hUbdd : IsBounded (invert a '' outside C ∪ {a}) := by
    refine (isBounded_iff_subset_closedBall a).2 ⟨δ⁻¹, ?_⟩
    rintro z (⟨w, hw, rfl⟩ | rfl)
    · rw [mem_closedBall, dist_invert_center]
      exact inv_anti₀ hδ (hfar w hw)
    · simpa using inv_nonneg.2 hδ.le
  
  have hUball : ball a R⁻¹ ⊆ invert a '' outside C ∪ {a} := by
    intro z hz
    rcases eq_or_ne z a with rfl | hza
    · exact Or.inr rfl
    · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
      have hpos : 0 < dist z a := dist_pos.2 hza
      rw [mem_compl_iff, mem_closedBall, dist_invert_center]
      exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
  have hUopen : IsOpen (invert a '' outside C ∪ {a}) := by
    have hrw : invert a '' outside C ∪ {a} = invert a '' outside C ∪ ball a R⁻¹ := by
      refine Subset.antisymm (union_subset subset_union_left ?_)
        (union_subset subset_union_left hUball)
      rintro z rfl
      exact Or.inr (mem_ball_self (by positivity))
    rw [hrw]
    exact hTopen.union isOpen_ball
  
  have hacl : a ∈ closure (invert a '' outside C) := by
    rw [Metric.mem_closure_iff]
    intro e he
    obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
      by_contra hcon
      push Not at hcon
      exact hsep.not_isBounded_outside
        ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
    refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
    rw [dist_comm, dist_invert_center]
    exact inv_lt_of_inv_lt₀ he hzfar
  have hUconn : IsPreconnected (invert a '' outside C ∪ {a}) :=
    (hsep.isConnected_outside.image _
      ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
      (union_subset subset_closure (by rintro z rfl; exact hacl))
  
  have hUD : invert a '' outside C ∪ {a} ⊆ (invert a '' C)ᶜ := by
    rintro z (⟨w, hw, rfl⟩ | rfl)
    · rintro ⟨u, hu, huw⟩
      exact hw.1 (invert_injective a huw ▸ hu)
    · rintro ⟨u, hu, hua⟩
      exact haC (invert_eq_center_iff.1 hua ▸ hu)
  
  have hAopen : IsOpen (invert a '' (inside C \ {a})) :=
    isOpen_invert_image (hsep.isOpen_inside.sdiff isClosed_singleton) (fun h => h.2 rfl)
  have hAU : Disjoint (invert a '' (inside C \ {a})) (invert a '' outside C ∪ {a}) := by
    rw [Set.disjoint_left]
    rintro z ⟨w, ⟨hwin, hwne⟩, rfl⟩ (⟨u, hu, huw⟩ | hza)
    · exact Set.disjoint_left.1 disjoint_inside_outside hwin (invert_injective a huw ▸ hu)
    · exact hwne (mem_singleton_iff.2
        (invert_eq_center_iff.1 (mem_singleton_iff.1 hza)))
  
  have hcompl : (invert a '' outside C ∪ {a})ᶜ ⊆
      invert a '' C ∪ invert a '' (inside C \ {a}) := by
    intro z hz
    by_cases hzC : invert a z ∈ C
    · exact Or.inl ⟨invert a z, hzC, invert_invert a z⟩
    · have hmem : invert a z ∈ inside C ∪ outside C := by
        rw [inside_union_outside]; exact hzC
      rcases hmem with hin | hout
      · refine Or.inr ⟨invert a z, ⟨hin, ?_⟩, invert_invert a z⟩
        intro hsing
        have hza : z = a := by
          rw [← invert_invert a z, mem_singleton_iff.1 hsing, invert_center]
        exact hz (Set.mem_union_right _ (mem_singleton_iff.2 hza))
      · exact absurd (show z ∈ invert a '' outside C ∪ {a} from
          Or.inl ⟨invert a z, hout, invert_invert a z⟩) hz
  
  have hfrontier : frontier (invert a '' outside C ∪ {a}) = invert a '' C := by
    refine Subset.antisymm (fun z hz => ?_) ?_
    · have hzU : z ∉ invert a '' outside C ∪ {a} := by
        rw [hUopen.frontier_eq] at hz; exact hz.2
      refine (hcompl hzU).resolve_right fun hA => ?_
      exact Set.disjoint_left.1 (hAU.closure_right hAopen) hA (frontier_subset_closure hz)
    · rintro z ⟨w, hwC, rfl⟩
      have hwne : w ≠ a := fun h => haC (h ▸ hwC)
      rw [hUopen.frontier_eq]
      refine ⟨closure_mono subset_union_left
        (mem_closure_image (continuousAt_invert hwne) ?_), fun hmem => hUD hmem ⟨w, hwC, rfl⟩⟩
      rw [← hsep.frontier_outside] at hwC
      exact frontier_subset_closure hwC
  
  have hsepa : IsSeparating (invert a '' C) := (hC.invert_image haC).isSeparating harc
  have haU : a ∈ invert a '' outside C ∪ {a} := Or.inr rfl
  have hcomp : connectedComponentIn (invert a '' C)ᶜ a = invert a '' outside C ∪ {a} :=
    Plane.connectedComponentIn_eq_of_frontier_disjoint hUopen hUconn hUD
      (by rw [hfrontier]; exact Set.inter_compl_self _) haU
  have hain : a ∈ inside (invert a '' C) := ⟨hUD haU, by rw [hcomp]; exact hUbdd⟩
  exact hcomp.symm.trans (hsepa.connectedComponentIn_eq_inside hain)

 
theorem notMem_invert_image (ha : a ∉ C) : a ∉ invert a '' C := by
  rintro ⟨w, hw, hwa⟩
  exact ha (invert_eq_center_iff.1 hwa ▸ hw)

 

theorem invert_image_outside (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' outside C = inside (invert a '' C) \ {a} := by
  rw [← invert_image_outside_union_singleton harc hC ha]
  refine (Set.union_sdiff_cancel_right ?_).symm
  rintro z ⟨⟨w, hw, rfl⟩, hza⟩
  exact Set.disjoint_left.1 disjoint_inside_outside ha
    (invert_eq_center_iff.1 (mem_singleton_iff.1 hza) ▸ hw)

 


theorem invert_image_inside_diff (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' (inside C \ {a}) = outside (invert a '' C) := by
  have haC : a ∉ C := ha.1
  have haout : a ∉ outside C := Set.disjoint_left.1 disjoint_inside_outside ha
  have hins := invert_image_outside_union_singleton harc hC ha
  
  have hout : ∀ z : Plane, z ∈ outside (invert a '' C) ↔
      z ∉ invert a '' C ∧ z ∉ inside (invert a '' C) := by
    intro z
    constructor
    · intro hz
      exact ⟨hz.1, Set.disjoint_left.1 disjoint_inside_outside.symm hz⟩
    · rintro ⟨h1, h2⟩
      have hmem : z ∈ inside (invert a '' C) ∪ outside (invert a '' C) := by
        rw [inside_union_outside]; exact h1
      exact hmem.resolve_left h2
  ext z
  rw [hout z]
  constructor
  · rintro ⟨w, ⟨hwin, hwne⟩, rfl⟩
    refine ⟨fun hmem => ?_, fun hmem => ?_⟩
    · obtain ⟨u, hu, huw⟩ := hmem
      exact hwin.1 (invert_injective a huw ▸ hu)
    · rw [← hins] at hmem
      rcases hmem with ⟨u, hu, huw⟩ | hza
      · exact Set.disjoint_left.1 disjoint_inside_outside hwin (invert_injective a huw ▸ hu)
      · exact hwne (mem_singleton_iff.2 (invert_eq_center_iff.1 (mem_singleton_iff.1 hza)))
  · rintro ⟨h1, h2⟩
    refine ⟨invert a z, ⟨?_, ?_⟩, invert_invert a z⟩
    · 
      have hzC : invert a z ∉ C := fun h => h1 ⟨invert a z, h, invert_invert a z⟩
      have hzout : invert a z ∉ outside C := fun h => h2 (by
        rw [← hins]; exact Set.mem_union_left _ ⟨invert a z, h, invert_invert a z⟩)
      have : invert a z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hzC
      exact this.resolve_right hzout
    · intro hsing
      exact h2 (by
        rw [← hins]
        refine Set.mem_union_right _ (mem_singleton_iff.2 ?_)
        rw [← invert_invert a z, mem_singleton_iff.1 hsing, invert_center])

 

theorem invert_image_union_outside (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    invert a '' (C ∪ outside C) =
      (invert a '' C ∪ inside (invert a '' C)) \ {a} := by
  rw [Set.image_union, invert_image_outside harc hC ha, Set.union_sdiff_distrib,
    Set.sdiff_singleton_eq_self (notMem_invert_image ha.1)]

 




theorem inversion_sides (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) :
    IsJordanCurve (invert a '' C) ∧
      invert a '' outside C = inside (invert a '' C) \ {a} ∧
      invert a '' (C ∪ outside C) = (invert a '' C ∪ inside (invert a '' C)) \ {a} ∧
      invert a '' ((invert a '' C ∪ inside (invert a '' C)) \ {a}) = C ∪ outside C ∧
      InjOn (invert a) (C ∪ outside C) ∧
      ContinuousOn (invert a) (C ∪ outside C) ∧
      ContinuousOn (invert a) ((invert a '' C ∪ inside (invert a '' C)) \ {a}) := by
  have haC : a ∉ C := ha.1
  have haout : a ∉ outside C := Set.disjoint_left.1 disjoint_inside_outside ha
  have himg := invert_image_union_outside harc hC ha
  have hsrc : C ∪ outside C ⊆ ({a}ᶜ : Set Plane) := by
    rintro z (hz | hz) <;> · simp only [mem_compl_iff, mem_singleton_iff]
                             rintro rfl
                             exact absurd hz (by assumption)
  refine ⟨hC.invert_image haC, invert_image_outside harc hC ha, himg, ?_,
    (invert_injective a).injOn, (continuousOn_invert a).mono hsrc,
    (continuousOn_invert a).mono ?_⟩
  · rw [← himg, invert_image_invert_image]
  · intro z hz
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact hz.2 rfl

 
theorem mem_inside_invert_image (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) (ha : a ∈ inside C) : a ∈ inside (invert a '' C) := by
  rw [← invert_image_outside_union_singleton harc hC ha]
  exact Or.inr rfl

 











 

structure IsHomeoOn (f g : Plane → Plane) (S T : Set Plane) : Prop where
   
  mapsTo : MapsTo f S T
   
  mapsTo_inv : MapsTo g T S
   
  continuousOn : ContinuousOn f S
   
  continuousOn_inv : ContinuousOn g T
   
  invOn : InvOn g f S T

namespace IsHomeoOn

variable {f g f' g' : Plane → Plane} {S T U S' T' : Set Plane}

theorem symm (h : IsHomeoOn f g S T) : IsHomeoOn g f T S where
  mapsTo := h.mapsTo_inv
  mapsTo_inv := h.mapsTo
  continuousOn := h.continuousOn_inv
  continuousOn_inv := h.continuousOn
  invOn := h.invOn.symm

theorem bijOn (h : IsHomeoOn f g S T) : BijOn f S T :=
  h.invOn.bijOn h.mapsTo h.mapsTo_inv

theorem injOn (h : IsHomeoOn f g S T) : InjOn f S := h.bijOn.injOn

theorem image_eq (h : IsHomeoOn f g S T) : f '' S = T := h.bijOn.image_eq

 
theorem comp (h : IsHomeoOn f g S T) (h' : IsHomeoOn f' g' T U) :
    IsHomeoOn (f' ∘ f) (g ∘ g') S U where
  mapsTo := h'.mapsTo.comp h.mapsTo
  mapsTo_inv := h.mapsTo_inv.comp h'.mapsTo_inv
  continuousOn := h'.continuousOn.comp h.continuousOn h.mapsTo
  continuousOn_inv := h.continuousOn_inv.comp h'.continuousOn_inv h'.mapsTo_inv
  invOn := h.invOn.comp h'.invOn h.mapsTo h'.mapsTo_inv

 
theorem mono (h : IsHomeoOn f g S T) (hS : S' ⊆ S) (hT : T' ⊆ T) (hf : MapsTo f S' T')
    (hg : MapsTo g T' S') : IsHomeoOn f g S' T' where
  mapsTo := hf
  mapsTo_inv := hg
  continuousOn := h.continuousOn.mono hS
  continuousOn_inv := h.continuousOn_inv.mono hT
  invOn := h.invOn.mono hS hT

 

theorem sdiff_singleton (h : IsHomeoOn f g S T) {u v : Plane} (hu : u ∈ S) (huv : f u = v) :
    IsHomeoOn f g (S \ {u}) (T \ {v}) := by
  refine h.mono Set.sdiff_subset Set.sdiff_subset (fun z hz => ⟨h.mapsTo hz.1, ?_⟩)
    (fun w hw => ⟨h.mapsTo_inv hw.1, ?_⟩)
  · 
    intro hmem
    exact hz.2 (mem_singleton_iff.2
      (h.injOn hz.1 hu ((mem_singleton_iff.1 hmem).trans huv.symm)))
  · 
    intro hmem
    refine hw.2 (mem_singleton_iff.2 ?_)
    rw [← huv, ← mem_singleton_iff.1 hmem, h.invOn.2 hw.1]

end IsHomeoOn

 
theorem isHomeoOn_invert {S : Set Plane} (ha : a ∉ S) :
    IsHomeoOn (invert a) (invert a) S (invert a '' S) where
  mapsTo := Set.mapsTo_image _ _
  mapsTo_inv := by
    rintro z ⟨w, hw, rfl⟩
    rwa [invert_invert]
  continuousOn := (continuousOn_invert a).mono (Set.subset_compl_singleton_iff.2 ha)
  continuousOn_inv := (continuousOn_invert a).mono
    (Set.subset_compl_singleton_iff.2 (notMem_invert_image ha))
  invOn := ⟨fun z _ => invert_invert a z, fun z _ => invert_invert a z⟩

 










 






def PointedInteriorExtension : Prop :=
  ∀ (C C' : Set Plane) (f g : Plane → Plane) (a b : Plane),
    IsJordanCurve C → IsJordanCurve C' → IsHomeoOn f g C C' → a ∈ inside C → b ∈ inside C' →
      ∃ F G : Plane → Plane,
        IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C') ∧ EqOn F f C ∧ F a = b

 







theorem exterior_extension (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hpt : PointedInteriorExtension) {C C' : Set Plane} {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ outside C) (C' ∪ outside C') ∧ EqOn F f C := by
  
  obtain ⟨a, ha⟩ := (hC.isSeparating harc).isConnected_inside.nonempty
  obtain ⟨b, hb⟩ := (hC'.isSeparating harc).isConnected_inside.nonempty
  have haC : a ∉ C := ha.1
  have hbC' : b ∉ C' := hb.1
  
  have hIa : IsHomeoOn (invert a) (invert a) C (invert a '' C) := isHomeoOn_invert haC
  have hIb : IsHomeoOn (invert b) (invert b) C' (invert b '' C') := isHomeoOn_invert hbC'
  
  have haout : a ∉ C ∪ outside C := by
    rintro (h | h)
    · exact haC h
    · exact Set.disjoint_left.1 disjoint_inside_outside ha h
  have hbout : b ∉ C' ∪ outside C' := by
    rintro (h | h)
    · exact hbC' h
    · exact Set.disjoint_left.1 disjoint_inside_outside hb h
  have hEa : IsHomeoOn (invert a) (invert a) (C ∪ outside C)
      ((invert a '' C ∪ inside (invert a '' C)) \ {a}) := by
    rw [← invert_image_union_outside harc hC ha]
    exact isHomeoOn_invert haout
  have hEb : IsHomeoOn (invert b) (invert b) (C' ∪ outside C')
      ((invert b '' C' ∪ inside (invert b '' C')) \ {b}) := by
    rw [← invert_image_union_outside harc hC' hb]
    exact isHomeoOn_invert hbout
  
  have hstar : IsHomeoOn (invert b ∘ f ∘ invert a) (invert a ∘ g ∘ invert b)
      (invert a '' C) (invert b '' C') := by
    have := (hIa.symm.comp hfg).comp hIb
    simpa [Function.comp_assoc] using this
  
  obtain ⟨Φ, Ψ, hΦ, hΦeq, hΦa⟩ := hpt (invert a '' C) (invert b '' C') _ _ a b
    (hC.invert_image haC) (hC'.invert_image hbC') hstar
    (mem_inside_invert_image harc hC ha) (mem_inside_invert_image harc hC' hb)
  
  have hΦ' := hΦ.sdiff_singleton
    (Set.mem_union_right _ (mem_inside_invert_image harc hC ha)) hΦa
  refine ⟨invert b ∘ Φ ∘ invert a, invert a ∘ Ψ ∘ invert b, ?_, ?_⟩
  · have := (hEa.comp hΦ').comp hEb.symm
    simpa [Function.comp_assoc] using this
  · 
    intro z hz
    have h1 : invert a z ∈ invert a '' C := ⟨z, hz, rfl⟩
    simp only [Function.comp_apply, hΦeq h1, invert_invert]

 






 




theorem exists_stronglyAccessible_dist_lt (hCcpt : IsCompact C) (hCne : C.Nonempty)
    (hΩC : Ω ⊆ Cᶜ) (hΩmax : ∀ q ∈ Ω, connectedComponentIn Cᶜ q ⊆ Ω) (hCΩ : C ⊆ closure Ω)
    (hp : p ∈ C) (hε : 0 < ε) :
    ∃ b ∈ C, StronglyAccessible Ω b ∧ dist b p < ε := by
  obtain ⟨q, hqΩ, hqp⟩ := Metric.mem_closure_iff.1 (hCΩ hp) (ε / 2) (by linarith)
  
  obtain ⟨b, hbC, hbmin⟩ :=
    hCcpt.exists_isMinOn hCne (Continuous.continuousOn (continuous_const.dist continuous_id))
  have hmin : ∀ c ∈ C, dist q b ≤ dist q c := fun c hc => isMinOn_iff.1 hbmin c hc
  refine ⟨b, hbC, stronglyAccessible_of_isMinOn (hΩC hqΩ) hbC hmin (hΩmax q hqΩ), ?_⟩
  
  have h1 : dist q b ≤ dist q p := hmin p hp
  have h2 : dist b p ≤ dist b q + dist q p := dist_triangle _ _ _
  rw [dist_comm q b] at h1
  rw [dist_comm p q] at hqp
  linarith

 

theorem tangent_dense (hC : IsSeparating C) (hΩ : IsRegionOf C Ω) :
    C ⊆ closure {b ∈ C | StronglyAccessible Ω b} := by
  intro p hp
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨b, hbC, hbacc, hbp⟩ := exists_stronglyAccessible_dist_lt
    hC.isJordanCurve.isCompact hC.isJordanCurve.nonempty hΩ.subset_compl
    (fun q hq => (hΩ.connectedComponentIn_eq hC hq).le) (hΩ.subset_closure hC) hp hε
  exact ⟨b, ⟨hbC, hbacc⟩, by rwa [dist_comm]⟩

 
theorem tangent_dense_inside (hC : IsSeparating C) :
    C ⊆ closure {b ∈ C | StronglyAccessible (inside C) b} :=
  tangent_dense hC (IsRegionOf.inside C)

 

theorem IsJordanCurve.tangent_dense (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) :
    C ⊆ closure {b ∈ C | StronglyAccessible (inside C) b} :=
  tangent_dense_inside (hC.isSeparating harc)

end Schoenflies
