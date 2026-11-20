/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Endgame.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Inversion
import FiniteAvalanches.Support.Schoenflies.JordanClosed
import FiniteAvalanches.Support.Schoenflies.ModelCurve
import FiniteAvalanches.Support.Schoenflies.SquareMover
import FiniteAvalanches.Support.Schoenflies.Topology

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 
















































































open Bornology Metric Set

namespace Schoenflies

 






 




theorem exists_isHomeoOn_of_homeomorph {S T : Set Plane} (e : ↥S ≃ₜ ↥T) :
    ∃ f g : Plane → Plane, IsHomeoOn f g S T ∧ ∀ (z : Plane) (hz : z ∈ S),
      f z = (e ⟨z, hz⟩ : Plane) := by
  classical
  refine ⟨fun z => if hz : z ∈ S then (e ⟨z, hz⟩ : Plane) else z,
    fun w => if hw : w ∈ T then (e.symm ⟨w, hw⟩ : Plane) else w,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun z hz => dif_pos hz⟩
  · exact fun z hz => by simp only [dif_pos hz]; exact (e ⟨z, hz⟩).2
  · exact fun w hw => by simp only [dif_pos hw]; exact (e.symm ⟨w, hw⟩).2
  · rw [continuousOn_iff_continuous_restrict]
    have heq : (S.restrict fun z => if hz : z ∈ S then (e ⟨z, hz⟩ : Plane) else z) =
        fun z : ↥S => (e z : Plane) := by
      funext z
      simp only [Set.restrict_apply, dif_pos z.2]
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  · rw [continuousOn_iff_continuous_restrict]
    have heq : (T.restrict fun w => if hw : w ∈ T then (e.symm ⟨w, hw⟩ : Plane) else w) =
        fun w : ↥T => (e.symm w : Plane) := by
      funext w
      simp only [Set.restrict_apply, dif_pos w.2]
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  · intro z hz
    simp only [dif_pos hz, dif_pos (e ⟨z, hz⟩).2]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
  · intro w hw
    simp only [dif_pos hw, dif_pos (e.symm ⟨w, hw⟩).2]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)

namespace IsHomeoOn

variable {f g : Plane → Plane} {S T : Set Plane}

 

noncomputable def homeomorphOfUniv (h : IsHomeoOn f g univ univ) : Plane ≃ₜ Plane where
  toFun := f
  invFun := g
  left_inv z := h.invOn.1 (mem_univ z)
  right_inv z := h.invOn.2 (mem_univ z)
  continuous_toFun := continuousOn_univ.1 h.continuousOn
  continuous_invFun := continuousOn_univ.1 h.continuousOn_inv

@[simp] theorem homeomorphOfUniv_apply (h : IsHomeoOn f g univ univ) (z : Plane) :
    h.homeomorphOfUniv z = f z := rfl

 

theorem image_inv_eq (h : IsHomeoOn f g S T) {A A' : Set Plane} (hA : A ⊆ S)
    (hA' : f '' A = A') : g '' A' = A := by
  rw [← hA', Set.image_image]
  exact (Set.EqOn.image_eq (fun z hz => h.invOn.1 (hA hz))).trans (Set.image_id A)

end IsHomeoOn

 





theorem image_eq_diff_of_bijOn_union {F : Plane → Plane} {A B T A' : Set Plane}
    (hF : BijOn F (A ∪ B) T) (hA : F '' A = A') (hdisj : Disjoint A B) :
    F '' B = T \ A' := by
  refine Subset.antisymm ?_ ?_
  · rintro y ⟨z, hzB, rfl⟩
    refine ⟨hF.mapsTo (Or.inr hzB), fun hy => ?_⟩
    rw [← hA] at hy
    obtain ⟨w, hwA, hw⟩ := hy
    exact Set.disjoint_left.1 hdisj hwA (hF.injOn (Or.inl hwA) (Or.inr hzB) hw ▸ hzB)
  · rintro y ⟨hyT, hyA'⟩
    obtain ⟨z, hz, rfl⟩ := hF.surjOn hyT
    have hzB : z ∈ B := hz.resolve_left fun hzA => hyA' (by rw [← hA]; exact ⟨z, hzA, rfl⟩)
    exact ⟨z, hzB, rfl⟩

 





open Classical in
 

noncomputable def paste (S : Set Plane) (f₁ f₂ : Plane → Plane) : Plane → Plane :=
  fun z => if z ∈ S then f₁ z else f₂ z

theorem paste_of_mem {S : Set Plane} {f₁ f₂ : Plane → Plane} {z : Plane} (hz : z ∈ S) :
    paste S f₁ f₂ z = f₁ z := by
  classical exact if_pos hz

theorem paste_of_notMem {S : Set Plane} {f₁ f₂ : Plane → Plane} {z : Plane} (hz : z ∉ S) :
    paste S f₁ f₂ z = f₂ z := by
  classical exact if_neg hz

 






 
theorem closedSquare_sdiff_modelCurve :
    Plane.closedSquare 0 1 \ modelCurve = Plane.openSquare 0 1 := by
  rw [modelCurve_eq_frontier, Plane.frontier_closedSquare]
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    exact lt_of_le_of_ne h1 h2
  · intro h
    have h' : Plane.supDist z 0 < 1 := h
    exact ⟨h'.le, ne_of_lt h'⟩

 
theorem Plane.IsSquareMover.isHomeoOn {c : Plane} {r : ℝ} {M N : Plane → Plane}
    (h : Plane.IsSquareMover c r M N) :
    IsHomeoOn M N (Plane.closedSquare c r) (Plane.closedSquare c r) where
  mapsTo := h.mapsTo
  mapsTo_inv := h.mapsTo_inv
  continuousOn := h.continuousOn
  continuousOn_inv := h.continuousOn_inv
  invOn := h.invOn

 





 





def SquareExtension : Prop :=
  ∀ (C : Set Plane) (u v : Plane → Plane), IsJordanCurve C → IsHomeoOn u v C modelCurve →
    ∃ F G : Plane → Plane,
      IsHomeoOn F G (C ∪ inside C) (Plane.closedSquare 0 1) ∧ EqOn F u C

 




variable {C C' : Set Plane}

theorem disjoint_curve_inside (C : Set Plane) : Disjoint C (inside C) :=
  Set.disjoint_left.2 fun _ hzC hz => hz.1 hzC

theorem disjoint_curve_outside (C : Set Plane) : Disjoint C (outside C) :=
  Set.disjoint_left.2 fun _ hzC hz => hz.1 hzC

theorem union_inside_sdiff (C : Set Plane) : (C ∪ inside C) \ C = inside C :=
  Set.union_sdiff_cancel_left (Set.disjoint_iff_inter_eq_empty.1 (disjoint_curve_inside C)).le

theorem union_outside_sdiff (C : Set Plane) : (C ∪ outside C) \ C = outside C :=
  Set.union_sdiff_cancel_left (Set.disjoint_iff_inter_eq_empty.1 (disjoint_curve_outside C)).le

 


theorem image_inside_eq {F G f : Plane → Plane}
    (hF : IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C')) (hf : EqOn F f C) (hfC : f '' C = C') :
    F '' inside C = inside C' := by
  have hFC : F '' C = C' := (Set.EqOn.image_eq hf).trans hfC
  have := image_eq_diff_of_bijOn_union hF.bijOn hFC (disjoint_curve_inside C)
  rwa [union_inside_sdiff] at this

 
theorem image_outside_eq {F G f : Plane → Plane}
    (hF : IsHomeoOn F G (C ∪ outside C) (C' ∪ outside C')) (hf : EqOn F f C)
    (hfC : f '' C = C') : F '' outside C = outside C' := by
  have hFC : F '' C = C' := (Set.EqOn.image_eq hf).trans hfC
  have := image_eq_diff_of_bijOn_union hF.bijOn hFC (disjoint_curve_outside C)
  rwa [union_outside_sdiff] at this

 




 


theorem square_reduction (hsq : SquareExtension) {f g : Plane → Plane} (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C') ∧ EqOn F f C := by
  obtain ⟨e⟩ := hC'.homeomorph_modelCurve
  obtain ⟨h, k, hhk, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨Φ, Φ', hΦ, hΦeq⟩ := hsq C (h ∘ f) (g ∘ k) hC (hfg.comp hhk)
  obtain ⟨Ψ, Ψ', hΨ, hΨeq⟩ := hsq C' h k hC' hhk
  refine ⟨Ψ' ∘ Φ, Φ' ∘ Ψ, hΦ.comp hΨ.symm, fun z hz => ?_⟩
  have h1 : f z ∈ C' := hfg.mapsTo hz
  change Ψ' (Φ z) = f z
  rw [hΦeq hz]
  change Ψ' (h (f z)) = f z
  rw [← hΨeq h1]
  exact hΨ.invOn.1 (Set.mem_union_left _ h1)

 




theorem closed_interior_extension (hsq : SquareExtension) {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ inside C) (C' ∪ inside C') ∧ EqOn F f C :=
  square_reduction hsq hC hC' hfg

 






 





theorem pointed_extension (hsq : SquareExtension) : PointedInteriorExtension := by
  intro C C' f g a b hC hC' hfg ha hb
  
  obtain ⟨Φ, Φ', hΦ, hΦeq⟩ := square_reduction hsq hC hC' hfg
  obtain ⟨e⟩ := hC'.homeomorph_modelCurve
  obtain ⟨h, k, hhk, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨Θ, Θ', hΘ, hΘeq⟩ := hsq C' h k hC' hhk
  
  have hΘC : Θ '' C' = modelCurve := (Set.EqOn.image_eq hΘeq).trans hhk.image_eq
  have hΘin : Θ '' inside C' = Plane.openSquare 0 1 := by
    rw [← closedSquare_sdiff_modelCurve]
    exact image_eq_diff_of_bijOn_union hΘ.bijOn hΘC (disjoint_curve_inside C')
  
  have hΦin : Φ '' inside C = inside C' := image_inside_eq hΦ hΦeq hfg.image_eq
  have haΦ : Φ a ∈ inside C' := by rw [← hΦin]; exact ⟨a, ha, rfl⟩
  have hx : Θ (Φ a) ∈ Plane.openSquare 0 1 := by rw [← hΘin]; exact ⟨Φ a, haΦ, rfl⟩
  have hy : Θ b ∈ Plane.openSquare 0 1 := by rw [← hΘin]; exact ⟨b, hb, rfl⟩
  
  
  obtain ⟨M, N, hM, hMx, -⟩ := Plane.exists_squareMover hx hy
  refine ⟨_, _, ((hΦ.comp hΘ).comp hM.isHomeoOn).comp hΘ.symm, fun z hz => ?_, ?_⟩
  · have h1 : f z ∈ C' := hfg.mapsTo hz
    change Θ' (M (Θ (Φ z))) = f z
    rw [hΦeq hz]
    
    have h2 : Θ (f z) ∈ frontier (Plane.closedSquare 0 1) := by
      rw [← modelCurve_eq_frontier, ← hΘC]
      exact ⟨f z, h1, rfl⟩
    rw [hM.eqOn_frontier h2]
    exact hΘ.invOn.1 (Set.mem_union_left _ h1)
  · change Θ' (M (Θ (Φ a))) = b
    rw [hMx]
    exact hΘ.invOn.1 (Set.mem_union_right _ hb)

 






 


theorem exterior_extension_of_squareExtension (hsq : SquareExtension) {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G (C ∪ outside C) (C' ∪ outside C') ∧ EqOn F f C :=
  exterior_extension (fun _ hA => arc_complement hA) (pointed_extension hsq) hC hC' hfg

 






 
theorem isClosed_union_inside (hC : IsSeparating C) : IsClosed (C ∪ inside C) := by
  rw [Set.union_comm, ← (IsRegionOf.inside C).closure_eq hC]
  exact isClosed_closure

 
theorem isClosed_union_outside (hC : IsSeparating C) : IsClosed (C ∪ outside C) := by
  rw [Set.union_comm, ← (IsRegionOf.outside C).closure_eq hC]
  exact isClosed_closure

 
theorem union_inside_union_outside (C : Set Plane) :
    (C ∪ inside C) ∪ (C ∪ outside C) = univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  by_cases hz : z ∈ C
  · exact Or.inl (Or.inl hz)
  · have hz' : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hz
    exact hz'.imp Or.inr Or.inr

 
theorem mem_outside_of_notMem_union_inside {z : Plane} (hz : z ∉ C ∪ inside C) :
    z ∈ outside C := by
  have hzC : z ∉ C := fun h => hz (Or.inl h)
  have : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hzC
  exact this.resolve_left fun h => hz (Or.inr h)

 





theorem jordan_schoenflies_of_squareExtension (hsq : SquareExtension)
    {f g : Plane → Plane} (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G univ univ ∧ EqOn F f C := by
  have hsC : IsSeparating C := jordan_curve_theorem hC
  have hsC' : IsSeparating C' := jordan_curve_theorem hC'
  obtain ⟨Fi, Gi, hFi, hFieq⟩ := closed_interior_extension hsq hC hC' hfg
  obtain ⟨Fe, Ge, hFe, hFeeq⟩ := exterior_extension_of_squareExtension hsq hC hC' hfg
  
  have hFiin : Fi '' inside C = inside C' := image_inside_eq hFi hFieq hfg.image_eq
  have hFeout : Fe '' outside C = outside C' := image_outside_eq hFe hFeeq hfg.image_eq
  have hGiin : Gi '' inside C' = inside C := hFi.image_inv_eq Set.subset_union_right hFiin
  have hGeout : Ge '' outside C' = outside C := hFe.image_inv_eq Set.subset_union_right hFeout
  
  have hGieq : EqOn Gi g C' := by
    intro w hw
    have hgw : g w ∈ C := hfg.mapsTo_inv hw
    have hFw : Fi (g w) = w := by rw [hFieq hgw]; exact hfg.invOn.2 hw
    calc Gi w = Gi (Fi (g w)) := by rw [hFw]
      _ = g w := hFi.invOn.1 (Set.mem_union_left _ hgw)
  have hGeeq : EqOn Ge g C' := by
    intro w hw
    have hgw : g w ∈ C := hfg.mapsTo_inv hw
    have hFw : Fe (g w) = w := by rw [hFeeq hgw]; exact hfg.invOn.2 hw
    calc Ge w = Ge (Fe (g w)) := by rw [hFw]
      _ = g w := hFe.invOn.1 (Set.mem_union_left _ hgw)
  
  
  
  have hFint : EqOn (paste (C ∪ inside C) Fi Fe) Fi (C ∪ inside C) := fun _ hz => paste_of_mem hz
  have hFext : EqOn (paste (C ∪ inside C) Fi Fe) Fe (C ∪ outside C) := by
    rintro z (hzC | hzout)
    · rw [paste_of_mem (Set.mem_union_left _ hzC), hFieq hzC, hFeeq hzC]
    · refine paste_of_notMem fun hz => ?_
      exact Set.disjoint_left.1 disjoint_inside_outside
        (hz.resolve_left fun h => Set.disjoint_left.1 (disjoint_curve_outside C) h hzout) hzout
  have hGint : EqOn (paste (C' ∪ inside C') Gi Ge) Gi (C' ∪ inside C') :=
    fun _ hw => paste_of_mem hw
  have hGext : EqOn (paste (C' ∪ inside C') Gi Ge) Ge (C' ∪ outside C') := by
    rintro w (hwC | hwout)
    · rw [paste_of_mem (Set.mem_union_left _ hwC), hGieq hwC, hGeeq hwC]
    · refine paste_of_notMem fun hw => ?_
      exact Set.disjoint_left.1 disjoint_inside_outside
        (hw.resolve_left fun h => Set.disjoint_left.1 (disjoint_curve_outside C') h hwout) hwout
  refine ⟨paste (C ∪ inside C) Fi Fe, paste (C' ∪ inside C') Gi Ge,
    ⟨mapsTo_univ _ _, mapsTo_univ _ _, ?_, ?_, ?_, ?_⟩, ?_⟩
  · 
    rw [← union_inside_union_outside C]
    exact Plane.continuousOn_union_of_isClosed (isClosed_union_inside hsC)
      (isClosed_union_outside hsC) (hFi.continuousOn.congr hFint)
      (hFe.continuousOn.congr hFext)
  · rw [← union_inside_union_outside C']
    exact Plane.continuousOn_union_of_isClosed (isClosed_union_inside hsC')
      (isClosed_union_outside hsC') (hFi.continuousOn_inv.congr hGint)
      (hFe.continuousOn_inv.congr hGext)
  · 
    
    intro z _
    by_cases hz : z ∈ C ∪ inside C
    · rw [hFint hz, hGint (hFi.mapsTo hz), hFi.invOn.1 hz]
    · have hzout : z ∈ outside C := mem_outside_of_notMem_union_inside hz
      have hzL : z ∈ C ∪ outside C := Or.inr hzout
      have hFz : Fe z ∈ outside C' := by rw [← hFeout]; exact ⟨z, hzout, rfl⟩
      rw [hFext hzL, hGext (Or.inr hFz), hFe.invOn.1 hzL]
  · 
    intro w _
    by_cases hw : w ∈ C' ∪ inside C'
    · rw [hGint hw, hFint (hFi.mapsTo_inv hw), hFi.invOn.2 hw]
    · have hwout : w ∈ outside C' := mem_outside_of_notMem_union_inside hw
      have hwL : w ∈ C' ∪ outside C' := Or.inr hwout
      have hGw : Ge w ∈ outside C := by rw [← hGeout]; exact ⟨w, hwout, rfl⟩
      rw [hGext hwL, hFext (Or.inr hGw), hFe.invOn.2 hwL]
  · exact fun z hz => (hFint (Set.mem_union_left _ hz)).trans (hFieq hz)

 


theorem jordan_schoenflies_homeomorph_of_squareExtension (hsq : SquareExtension)
    {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F : Plane ≃ₜ Plane, EqOn F f C := by
  obtain ⟨F, G, hFG, hFeq⟩ := jordan_schoenflies_of_squareExtension hsq hC hC' hfg
  exact ⟨hFG.homeomorphOfUniv, hFeq⟩

 

theorem jordan_schoenflies_of_homeomorph_of_squareExtension (hsq : SquareExtension)
    (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z := by
  obtain ⟨f, g, hfg, hfe⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, hF⟩ := jordan_schoenflies_homeomorph_of_squareExtension hsq hC hC' hfg
  exact ⟨F, fun z => (hF z.2).trans (hfe z z.2)⟩

end Schoenflies
