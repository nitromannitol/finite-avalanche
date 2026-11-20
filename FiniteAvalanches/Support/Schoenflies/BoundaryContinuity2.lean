/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/BoundaryContinuity2.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.BoundaryContinuity
import FiniteAvalanches.Support.Schoenflies.Endgame

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 















































































open Bornology Filter Metric Schoenflies Set Topology
open scoped Graph

namespace Graph

 




theorem IsStageOn.exists_isCrosscut {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {C : Set Plane} [G.Finite] (h : IsStageOn G drawing C (Schoenflies.inside C))
    (hC : Schoenflies.IsJordanCurve C) {a b : Plane} (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (ha : ∃ e, G.Inc e a ∧ Nonboundary drawing C e)
    (hb : ∃ e, G.Inc e b ∧ Nonboundary drawing C e) :
    ∃ P ⊆ pointSet G drawing, Schoenflies.IsCrosscut C P a b := by
  obtain ⟨P, hPsub, hPpoly, hParc, -, hPD⟩ := h.exists_crosscut hab haC hbC ha hb
  exact ⟨P, hPsub, ⟨hC, hParc, hPpoly, haC, hbC, hPD⟩⟩

end Graph

namespace Schoenflies

variable {C 𝒜 A₁ A₂ B₁ B₂ P P' : Set Plane} {u v F F' : Plane → Plane} {a b p r : Plane}

 





 
theorem inside_modelCurve : inside modelCurve = Plane.openSquare 0 1 := by
  rw [modelCurve_eq_frontier]
  exact inside_frontier_closedSquare 0 1

 
theorem isCompact_closedSquare (c : Plane) (r : ℝ) : IsCompact (Plane.closedSquare c r) :=
  Metric.isCompact_of_isClosed_isBounded (Plane.isClosed_closedSquare c r)
    (Plane.isBounded_closedSquare c r)

 




 
theorem IsArcBetween.image_of_injOn {A S : Set Plane} {p q : Plane} {f : Plane → Plane}
    (h : IsArcBetween A p q) (hAS : A ⊆ S) (hcont : ContinuousOn f S) (hinj : InjOn f S) :
    IsArcBetween (f '' A) (f p) (f q) := by
  obtain ⟨g, hg, hgi, hgim, hg0, hg1⟩ := h
  have hmem : ∀ t ∈ unitInterval, g t ∈ S := by
    intro t ht
    exact hAS (hgim ▸ mem_image_of_mem g ht)
  refine ⟨f ∘ g, hcont.comp hg hmem, ?_, ?_, by simp [hg0], by simp [hg1]⟩
  · intro s hs t ht hst
    exact hgi hs ht (hinj (hmem s hs) (hmem t ht) hst)
  · rw [← hgim, image_comp]

 
theorem IsCutPair.image {f : Plane → Plane} (h : IsCutPair C a b A₁ A₂)
    (hcont : ContinuousOn f C) (hinj : InjOn f C) :
    IsCutPair (f '' C) (f a) (f b) (f '' A₁) (f '' A₂) where
  fst := h.fst.image_of_injOn h.fst_subset hcont hinj
  snd := h.snd.image_of_injOn h.snd_subset hcont hinj
  union_eq := by rw [← image_union, h.union_eq]
  inter_eq := by
    rw [← hinj.image_inter h.fst_subset h.snd_subset, h.inter_eq, image_pair]

 

theorem IsCutPair.image_of_isHomeoOn {T : Set Plane} (h : IsCutPair C a b A₁ A₂)
    (hu : IsHomeoOn u v C T) : IsCutPair T (u a) (u b) (u '' A₁) (u '' A₂) := by
  have h' := h.image hu.continuousOn hu.injOn
  rwa [hu.image_eq] at h'

 







 

theorem exists_anchor_mem_arc (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcut : IsCutPair C a b A₁ A₂) : ∃ c ∈ 𝒜, c ∈ A₁ ∧ c ∉ A₂ := by
  
  obtain ⟨z, hzA, hz⟩ := not_subset.1 hcut.fst.not_subset_pair
  have hzA2 : z ∉ A₂ := fun h => hz (by rw [← hcut.inter_eq]; exact ⟨hzA, h⟩)
  have hA2closed : IsClosed A₂ := hcut.snd.isArc.isClosed
  obtain ⟨c, hcmem, hc⟩ :=
    mem_closure_iff.1 (hdense (hcut.fst_subset hzA)) _ hA2closed.isOpen_compl hzA2
  have hcC : c ∈ A₁ ∪ A₂ := by rw [hcut.union_eq]; exact hsub hc
  exact ⟨c, hc, hcC.resolve_right hcmem, hcmem⟩

 







theorem IsCutPair.separates (hB : IsCutPair C p r B₁ B₂) (hA : IsCutPair C a b A₁ A₂)
    (ha' : a ∉ B₂) (hb' : b ∉ B₁) :
    (p ∈ A₁ ∧ r ∈ A₂) ∨ (p ∈ A₂ ∧ r ∈ A₁) := by
  have hpB : p ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inl rfl
  have hrB : r ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inr rfl
  
  have key : ∀ A : Set Plane, IsArcBetween A a b → A ⊆ C → p ∉ A → r ∉ A → False := by
    intro A hAarc hAC hpA hrA
    have hcov : A ⊆ B₂ᶜ ∪ B₁ᶜ := by
      intro z hz
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
      have : z ∈ ({p, r} : Set Plane) := by rw [← hB.inter_eq]; exact ⟨hcon.2, hcon.1⟩
      rcases this with rfl | rfl
      · exact hpA hz
      · exact hrA hz
    have hempty : ∀ z ∈ A, z ∈ B₂ᶜ → z ∉ B₁ᶜ := by
      intro z hz hz2 hz1
      have : z ∈ B₁ ∪ B₂ := by rw [hB.union_eq]; exact hAC hz
      exact this.elim hz1 hz2
    obtain ⟨z, hzA, hz2, hz1⟩ :=
      hAarc.isArc.isConnected.2 _ _ (hB.snd.isArc.isClosed.isOpen_compl)
        (hB.fst.isArc.isClosed.isOpen_compl) hcov ⟨a, hAarc.left_mem, ha'⟩
        ⟨b, hAarc.right_mem, hb'⟩
    exact hempty z hzA hz2 hz1
  
  have hpne : p ≠ a ∧ p ≠ b := ⟨fun h => ha' (h ▸ hpB.2), fun h => hb' (h ▸ hpB.1)⟩
  have hrne : r ≠ a ∧ r ≠ b := ⟨fun h => ha' (h ▸ hrB.2), fun h => hb' (h ▸ hrB.1)⟩
  have hone : ∀ z : Plane, z ∈ C → z ≠ a → z ≠ b → (z ∈ A₁ ∧ z ∉ A₂) ∨ (z ∈ A₂ ∧ z ∉ A₁) := by
    intro z hzC hza hzb
    have hboth : ¬ (z ∈ A₁ ∧ z ∈ A₂) := by
      intro h
      have : z ∈ ({a, b} : Set Plane) := by rw [← hA.inter_eq]; exact h
      rcases this with h' | h'
      · exact hza h'
      · exact hzb h'
    have : z ∈ A₁ ∪ A₂ := by rw [hA.union_eq]; exact hzC
    rcases this with h | h
    · exact Or.inl ⟨h, fun h' => hboth ⟨h, h'⟩⟩
    · exact Or.inr ⟨h, fun h' => hboth ⟨h', h⟩⟩
  have hpC : p ∈ C := by rw [← hB.union_eq]; exact Or.inl hpB.1
  have hrC : r ∈ C := by rw [← hB.union_eq]; exact Or.inl hrB.1
  rcases hone p hpC hpne.1 hpne.2 with ⟨hp1, hp2⟩ | ⟨hp2, hp1⟩ <;>
    rcases hone r hrC hrne.1 hrne.2 with ⟨hr1, hr2⟩ | ⟨hr2, hr1⟩
  · exact absurd (key A₂ hA.snd hA.snd_subset hp2 hr2) not_false
  · exact Or.inl ⟨hp1, hr2⟩
  · exact Or.inr ⟨hp2, hr1⟩
  · exact absurd (key A₁ hA.fst hA.fst_subset hp1 hr1) not_false

 

theorem exists_separating_anchors (hC : IsJordanCurve C) (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hp : p ∈ C) (hr : r ∈ C) (hpr : p ≠ r) :
    ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ A₁ A₂ : Set Plane, a ≠ b ∧ IsCutPair C a b A₁ A₂ ∧
      p ∈ A₁ ∧ p ∉ A₂ ∧ r ∈ A₂ ∧ r ∉ A₁ := by
  obtain ⟨B₁, B₂, hB⟩ := exists_isCutPair hC hp hr hpr
  obtain ⟨a, ha𝒜, haB, haB'⟩ := exists_anchor_mem_arc hsub hdense hB
  obtain ⟨b, hb𝒜, hbB, hbB'⟩ := exists_anchor_mem_arc hsub hdense hB.symm
  have hab : a ≠ b := fun h => haB' (h ▸ hbB)
  obtain ⟨A₁, A₂, hA⟩ := exists_isCutPair hC (hsub ha𝒜) (hsub hb𝒜) hab
  
  have hpB : p ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inl rfl
  have hrB : r ∈ B₁ ∩ B₂ := by rw [hB.inter_eq]; exact Or.inr rfl
  have hsplit : ∀ (D₁ D₂ : Set Plane), IsCutPair C a b D₁ D₂ → ∀ z : Plane,
      z ∈ B₁ ∩ B₂ → z ∈ D₁ → z ∉ D₂ := by
    intro D₁ D₂ hD z hz hzD hzD'
    have : z ∈ ({a, b} : Set Plane) := by rw [← hD.inter_eq]; exact ⟨hzD, hzD'⟩
    rcases this with rfl | rfl
    · exact haB' hz.2
    · exact hbB' hz.1
  rcases hB.separates hA haB' hbB' with ⟨hp1, hr2⟩ | ⟨hp2, hr1⟩
  · exact ⟨a, ha𝒜, b, hb𝒜, A₁, A₂, hab, hA, hp1, hsplit A₁ A₂ hA p hpB hp1, hr2,
      hsplit A₂ A₁ hA.symm r hrB hr2⟩
  · exact ⟨a, ha𝒜, b, hb𝒜, A₂, A₁, hab, hA.symm, hp2, hsplit A₂ A₁ hA.symm p hpB hp2, hr1,
      hsplit A₁ A₂ hA r hrB hr1⟩

 




 






def HasAnchorCrosscuts (C 𝒜 : Set Plane) (u F : Plane → Plane) : Prop :=
  ∀ ⦃a b : Plane⦄, a ∈ 𝒜 → b ∈ 𝒜 → a ≠ b → ∃ P P' : Set Plane,
    IsCrosscut C P a b ∧ IsCrosscut modelCurve P' (u a) (u b) ∧
      F '' (P \ {a, b}) = P' \ {u a, u b}

 






def HasSpokes (C 𝒜 : Set Plane) (u F : Plane → Plane) : Prop :=
  ∀ c ∈ 𝒜, ∀ ε > 0, ∃ J : Set Plane, J ⊆ inside C ∧ IsPreconnected J ∧ J ⊆ ball c ε ∧
    c ∈ closure J ∧ u c ∈ closure (F '' J)

 







 



theorem IsCrosscut.image_of_injOn {C' Sk : Set Plane} {g : Plane → Plane}
    (hP : IsCrosscut C P a b) (hPSk : P ⊆ Sk) (hcont : ContinuousOn g Sk) (hinj : InjOn g Sk)
    (hC' : IsJordanCurve C') (hpoly : IsPolygonal (g '' P)) (ha : g a ∈ C') (hb : g b ∈ C')
    (hint : g '' (P \ {a, b}) ⊆ inside C') : IsCrosscut C' (g '' P) (g a) (g b) := by
  refine ⟨hC', hP.arc.image_of_injOn hPSk hcont hinj, hpoly, ha, hb, ?_⟩
  rintro z ⟨⟨w, hwP, rfl⟩, hz⟩
  refine hint ⟨w, ⟨hwP, ?_⟩, rfl⟩
  rintro (rfl | rfl)
  · exact hz (Or.inl rfl)
  · exact hz (Or.inr rfl)

 

theorem image_sdiff_eq_of_eqOn {Sk : Set Plane} {g : Plane → Plane} (hPSk : P ⊆ Sk)
    (hinj : InjOn g Sk) (ha : a ∈ P) (hb : b ∈ P) (hFg : EqOn F g (P \ {a, b})) :
    F '' (P \ {a, b}) = g '' P \ {g a, g b} := by
  rw [hFg.image_eq, (hinj.mono hPSk).image_sdiff_subset (pair_subset ha hb), image_pair]

 

 

theorem inside_sdiff_crosscut (h : IsCrosscut C P a b) :
    inside C \ P = inside C \ (P \ {a, b}) := by
  refine Set.ext fun z => ⟨fun hz => ⟨hz.1, fun h' => hz.2 h'.1⟩, fun hz => ⟨hz.1, fun h' => ?_⟩⟩
  have hzab : z ∈ ({a, b} : Set Plane) := by
    by_contra hcon
    exact hz.2 ⟨h', hcon⟩
  rcases hzab with rfl | rfl
  · exact inside_subset_compl hz.1 h.left_mem
  · exact inside_subset_compl hz.1 h.right_mem

 


theorem image_inside_sdiff (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hP : IsCrosscut C P a b) (hP' : IsCrosscut modelCurve P' (u a) (u b))
    (hagree : F '' (P \ {a, b}) = P' \ {u a, u b}) :
    F '' (inside C \ P) = inside modelCurve \ P' := by
  have hFin : F '' inside C = inside modelCurve := by rw [hF.image_eq, inside_modelCurve]
  rw [inside_sdiff_crosscut hP, hF.injOn.image_sdiff_subset hP.sdiff_subset, hagree, hFin,
    ← inside_sdiff_crosscut hP']

 




theorem image_crosscut_side_subset (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜) (hspoke : HasSpokes C 𝒜 u F)
    (hcut : IsCutPair C a b A₁ A₂) (hP : IsCrosscut C P a b)
    (hP' : IsCrosscut modelCurve P' (u a) (u b)) (hagree : F '' (P \ {a, b}) = P' \ {u a, u b}) :
    F '' inside (A₁ ∪ P) ⊆ inside (u '' A₁ ∪ P') := by
  classical
  have hcut' : IsCutPair modelCurve (u a) (u b) (u '' A₁) (u '' A₂) :=
    hcut.image_of_isHomeoOn hu
  obtain ⟨hsrc1, hsrc2, -, -, -, -, -, -, hsrc9, hsrc10⟩ := crosscut_theorem hP hcut
  obtain ⟨htgt1, htgt2, -, -, -, -, -, -, htgt9, htgt10⟩ := crosscut_theorem hP' hcut'
  have hdiff := image_inside_sdiff hF hP hP' hagree
  
  have hopenS : ∀ A : Set Plane, IsArcBetween A a b → IsOpen (inside (A ∪ P)) := fun A hA =>
    isOpen_inside (hA.isArc.isCompact.union hP.arc.isArc.isCompact).isClosed
  have hopenT : ∀ A : Set Plane, IsArcBetween A (u a) (u b) → IsOpen (inside (A ∪ P')) :=
    fun A hA => isOpen_inside (hA.isArc.isCompact.union hP'.arc.isArc.isCompact).isClosed
  have hS1 := hopenS A₁ hcut.fst
  have hS2 := hopenS A₂ hcut.snd
  have hT1 := hopenT _ hcut'.fst
  have hT2 := hopenT _ hcut'.snd
  
  have hW1sub : inside (A₁ ∪ P) ⊆ inside C \ P := by rw [hsrc1]; exact subset_union_left
  have hconn : IsPreconnected (F '' inside (A₁ ∪ P)) := by
    refine IsPreconnected.image ?_ F (hF.continuousOn.mono fun z hz => (hW1sub hz).1)
    exact ((jordan_curve_theorem (hP.isJordanCurve_union hcut)).isConnected_inside).2
  have himsub : F '' inside (A₁ ∪ P) ⊆ inside (u '' A₁ ∪ P') ∪ inside (u '' A₂ ∪ P') := by
    rw [← htgt1, ← hdiff]
    exact image_mono hW1sub
  
  by_cases hmeet : (F '' inside (A₁ ∪ P) ∩ inside (u '' A₁ ∪ P')).Nonempty
  · exact hconn.subset_left_of_subset_union hT1 hT2 htgt2 himsub hmeet
  rw [not_nonempty_iff_eq_empty] at hmeet
  exfalso
  have hother : F '' inside (A₁ ∪ P) ⊆ inside (u '' A₂ ∪ P') := by
    intro w hw
    refine (himsub hw).resolve_left fun h' => ?_
    exact (eq_empty_iff_forall_notMem.1 hmeet w) ⟨hw, h'⟩
  
  obtain ⟨c, hc𝒜, hcA1, hcA2⟩ := exists_anchor_mem_arc hsub hdense hcut
  have hcC : c ∈ C := hsub hc𝒜
  have hca : c ≠ a := fun h => hcA2 (h ▸ hcut.snd.left_mem)
  have hcb : c ≠ b := fun h => hcA2 (h ▸ hcut.snd.right_mem)
  
  have hcP : c ∉ P := by
    intro h
    have : c ∈ ({a, b} : Set Plane) := by rw [← hP.inter_eq]; exact ⟨h, hcC⟩
    rcases this with h' | h'
    · exact hca h'
    · exact hcb h'
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 hP.arc.isArc.isClosed.isOpen_compl c hcP
  obtain ⟨J, hJin, hJconn, hJball, hJc, hJuc⟩ := hspoke c hc𝒜 ε hε
  have hJsub : J ⊆ inside C \ P := fun z hz => ⟨hJin hz, hball (hJball hz)⟩
  have hJcov : J ⊆ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by rw [← hsrc1]; exact hJsub
  
  have hJ1 : J ⊆ inside (A₁ ∪ P) := by
    by_cases hJ1 : (J ∩ inside (A₁ ∪ P)).Nonempty
    · exact hJconn.subset_left_of_subset_union hS1 hS2 hsrc2 hJcov hJ1
    · rw [not_nonempty_iff_eq_empty] at hJ1
      have hJ2 : J ⊆ inside (A₂ ∪ P) := fun z hz =>
        (hJcov hz).resolve_left fun h' => (eq_empty_iff_forall_notMem.1 hJ1 z) ⟨hz, h'⟩
      have : c ∈ A₂ := by
        rw [← hsrc10]
        exact ⟨closure_mono hJ2 hJc, hcC⟩
      exact absurd this hcA2
  
  have : u c ∈ u '' A₂ := by
    rw [← htgt10]
    refine ⟨closure_mono (subset_trans (image_mono hJ1) hother) hJuc, hu.mapsTo hcC⟩
  obtain ⟨w, hwA2, hw⟩ := this
  exact hcA2 (hu.injOn (hcut.snd_subset hwA2) hcC hw ▸ hwA2)

 




theorem crosscut_side_correspondence (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜) (hspoke : HasSpokes C 𝒜 u F)
    (hcut : IsCutPair C a b A₁ A₂) (hP : IsCrosscut C P a b)
    (hP' : IsCrosscut modelCurve P' (u a) (u b)) (hagree : F '' (P \ {a, b}) = P' \ {u a, u b}) :
    F '' inside (A₁ ∪ P) = inside (u '' A₁ ∪ P') ∧
      F '' inside (A₂ ∪ P) = inside (u '' A₂ ∪ P') := by
  have hcut' : IsCutPair modelCurve (u a) (u b) (u '' A₁) (u '' A₂) :=
    hcut.image_of_isHomeoOn hu
  have h1 := image_crosscut_side_subset hu hF hsub hdense hspoke hcut hP hP' hagree
  have h2 := image_crosscut_side_subset hu hF hsub hdense hspoke hcut.symm hP hP' hagree
  obtain ⟨hsrc1, -⟩ := crosscut_theorem hP hcut
  obtain ⟨htgt1, htgt2, -⟩ := crosscut_theorem hP' hcut'
  have hdiff := image_inside_sdiff hF hP hP' hagree
  
  have hcover : F '' inside (A₁ ∪ P) ∪ F '' inside (A₂ ∪ P) =
      inside (u '' A₁ ∪ P') ∪ inside (u '' A₂ ∪ P') := by
    rw [← image_union, ← hsrc1, hdiff, htgt1]
  constructor
  · refine subset_antisymm h1 fun w hw => ?_
    have : w ∈ F '' inside (A₁ ∪ P) ∪ F '' inside (A₂ ∪ P) := by
      rw [hcover]; exact Or.inl hw
    exact this.resolve_right fun h' => Set.disjoint_left.1 htgt2 hw (h2 h')
  · refine subset_antisymm h2 fun w hw => ?_
    have : w ∈ F '' inside (A₁ ∪ P) ∪ F '' inside (A₂ ∪ P) := by
      rw [hcover]; exact Or.inr hw
    exact this.resolve_left fun h' => Set.disjoint_left.1 htgt2 (h1 h') hw

 

 

noncomputable def extendByBoundary (C : Set Plane) (u F : Plane → Plane) : Plane → Plane :=
  paste C u F

theorem extendByBoundary_of_mem {z : Plane} (hz : z ∈ C) : extendByBoundary C u F z = u z :=
  paste_of_mem hz

theorem extendByBoundary_of_notMem {z : Plane} (hz : z ∉ C) : extendByBoundary C u F z = F z :=
  paste_of_notMem hz

 




theorem tendsto_nhdsWithin_inside (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcross : HasAnchorCrosscuts C 𝒜 u F) (hspoke : HasSpokes C 𝒜 u F) (hp : p ∈ C) :
    Tendsto F (𝓝[inside C] p) (𝓝 (u p)) := by
  classical
  by_contra hcon
  rw [Filter.tendsto_def] at hcon
  push Not at hcon
  obtain ⟨s, hs, hsnot⟩ := hcon
  obtain ⟨W, hWs, hWopen, hWmem⟩ := _root_.mem_nhds_iff.1 hs
  have hWnot : F ⁻¹' W ∉ 𝓝[inside C] p := fun h =>
    hsnot (mem_of_superset h (preimage_mono hWs))
  
  set l' : Filter Plane := 𝓝[inside C] p ⊓ 𝓟 (F ⁻¹' Wᶜ) with hl'
  haveI : l'.NeBot := by
    refine ⟨fun h => hWnot ?_⟩
    rw [hl', Filter.inf_principal_eq_bot] at h
    simpa using h
  have hl'in : inside C ∈ l' := mem_inf_of_left self_mem_nhdsWithin
  have hl'W : F ⁻¹' Wᶜ ∈ l' := mem_inf_of_right (mem_principal_self _)
  have hl'p : l' ≤ 𝓝 p := le_trans inf_le_left nhdsWithin_le_nhds
  
  have hmapK : map F l' ≤ 𝓟 (Plane.closedSquare 0 1) := by
    rw [le_principal_iff, mem_map]
    filter_upwards [hl'in] with z hz using Plane.openSquare_subset_closedSquare 0 1 (hF.mapsTo hz)
  obtain ⟨q, hqK, hqcl⟩ := (isCompact_closedSquare 0 1).exists_clusterPt hmapK
  have hqW : q ∈ Wᶜ := by
    have hle : map F l' ≤ 𝓟 Wᶜ := by rw [le_principal_iff]; exact hl'W
    have := mem_closure_iff_clusterPt.2 (hqcl.mono hle)
    rwa [hWopen.isClosed_compl.closure_eq] at this
  have hqne : q ≠ u p := fun h => hqW (h ▸ hWmem)
  
  
  have hqcurve : q ∈ modelCurve := by
    by_contra hq
    have hqopen : q ∈ Plane.openSquare 0 1 := by
      rw [← closedSquare_sdiff_modelCurve]; exact ⟨hqK, hq⟩
    have hmapO : map F l' ≤ 𝓟 (Plane.openSquare 0 1) := by
      rw [le_principal_iff, mem_map]
      filter_upwards [hl'in] with z hz using hF.mapsTo hz
    set m : Filter Plane := 𝓝 q ⊓ map F l' with hm
    haveI : m.NeBot := hqcl
    have hm1 : m ≤ 𝓝[Plane.openSquare 0 1] q :=
      le_inf inf_le_left (le_trans inf_le_right hmapO)
    have h1 : Tendsto F' m (𝓝 (F' q)) := (hF.continuousOn_inv q hqopen).mono_left hm1
    have h2 : Tendsto F' m (𝓝 p) := by
      refine le_trans (map_mono (inf_le_right : m ≤ map F l')) ?_
      rw [Filter.map_map]
      have heq : (F' ∘ F) =ᶠ[l'] id := by
        filter_upwards [hl'in] with z hz using hF.invOn.1 hz
      rw [Filter.map_congr heq, Filter.map_id]
      exact hl'p
    have hpin : p ∈ inside C := tendsto_nhds_unique h1 h2 ▸ hF.mapsTo_inv hqopen
    exact inside_subset_compl hpin hp
  
  have hrC : v q ∈ C := hu.mapsTo_inv hqcurve
  have hur : u (v q) = q := hu.invOn.2 hqcurve
  have hpr : p ≠ v q := fun h => hqne (by rw [← hur, ← h])
  obtain ⟨a, ha𝒜, b, hb𝒜, A₁, A₂, hab, hcut, hpA1, hpA2, hrA2, hrA1⟩ :=
    exists_separating_anchors hC hsub hdense hp hrC hpr
  obtain ⟨P, P', hP, hP', hagree⟩ := hcross ha𝒜 hb𝒜 hab
  have hcut' : IsCutPair modelCurve (u a) (u b) (u '' A₁) (u '' A₂) :=
    hcut.image_of_isHomeoOn hu
  have hside := image_crosscut_side_subset hu hF hsub hdense hspoke hcut hP hP' hagree
  obtain ⟨hsrc1, -, -, -, -, -, -, -, -, hsrc10⟩ := crosscut_theorem hP hcut
  obtain ⟨-, -, -, -, -, -, -, -, htgt9, -⟩ := crosscut_theorem hP' hcut'
  
  have hpa : p ≠ a := fun h => hpA2 (h ▸ hcut.snd.left_mem)
  have hpb : p ≠ b := fun h => hpA2 (h ▸ hcut.snd.right_mem)
  have hpP : p ∉ P := by
    intro h
    have : p ∈ ({a, b} : Set Plane) := by rw [← hP.inter_eq]; exact ⟨h, hp⟩
    rcases this with h' | h'
    · exact hpa h'
    · exact hpb h'
  have hpfar : p ∉ closure (inside (A₂ ∪ P)) := fun h => hpA2 (hsrc10 ▸ ⟨h, hp⟩)
  
  have hV : IsOpen (Pᶜ ∩ (closure (inside (A₂ ∪ P)))ᶜ) :=
    hP.arc.isArc.isClosed.isOpen_compl.inter isClosed_closure.isOpen_compl
  have hnear : inside (A₁ ∪ P) ∈ 𝓝[inside C] p := by
    refine mem_nhdsWithin.2 ⟨_, hV, ⟨hpP, hpfar⟩, ?_⟩
    rintro z ⟨⟨hz1, hz2⟩, hzin⟩
    have : z ∈ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by rw [← hsrc1]; exact ⟨hzin, hz1⟩
    exact this.resolve_right fun h' => hz2 (subset_closure h')
  
  have hmapW : map F l' ≤ 𝓟 (inside (u '' A₁ ∪ P')) := by
    rw [le_principal_iff, mem_map]
    filter_upwards [mem_inf_of_left hnear] with z hz using hside ⟨z, hz, rfl⟩
  have hqclos : q ∈ closure (inside (u '' A₁ ∪ P')) :=
    mem_closure_iff_clusterPt.2 (hqcl.mono hmapW)
  have hqA1 : q ∈ u '' A₁ := by rw [← htgt9]; exact ⟨hqclos, hqcurve⟩
  obtain ⟨w, hwA1, hw⟩ := hqA1
  have : v q = w := by
    rw [← hw, hu.invOn.1 (hcut.fst_subset hwA1)]
  exact hrA1 (this ▸ hwA1)

 
theorem boundary_continuity (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcross : HasAnchorCrosscuts C 𝒜 u F) (hspoke : HasSpokes C 𝒜 u F) :
    ContinuousOn (extendByBoundary C u F) (C ∪ inside C) := by
  have heqC : EqOn (extendByBoundary C u F) u C := fun _ hz => extendByBoundary_of_mem hz
  have heqD : EqOn (extendByBoundary C u F) F (inside C) := fun _ hz =>
    extendByBoundary_of_notMem (inside_subset_compl hz)
  intro z hz
  rcases hz with hzC | hzin
  · 
    rw [ContinuousWithinAt, extendByBoundary_of_mem hzC, nhdsWithin_union, Filter.tendsto_sup]
    constructor
    · exact Tendsto.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heqC).symm
        (hu.continuousOn z hzC)
    · exact Tendsto.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heqD).symm
        (tendsto_nhdsWithin_inside hC hu hF hsub hdense hcross hspoke hzC)
  · 
    have hopen : IsOpen (inside C) := isOpen_inside hC.isClosed
    have hmem : inside C ∈ 𝓝 z := hopen.mem_nhds hzin
    have hFat : ContinuousAt F z := hF.continuousOn.continuousAt hmem
    exact (hFat.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hmem heqD)).continuousWithinAt

 

 





theorem isHomeoOn_extendByBoundary (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve)
    (hF : IsHomeoOn F F' (inside C) (Plane.openSquare 0 1))
    (hsub : 𝒜 ⊆ C) (hdense : C ⊆ closure 𝒜)
    (hcross : HasAnchorCrosscuts C 𝒜 u F) (hspoke : HasSpokes C 𝒜 u F) :
    IsHomeoOn (extendByBoundary C u F) (extendByBoundary modelCurve v F')
      (C ∪ inside C) (Plane.closedSquare 0 1) := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  have hcont : ContinuousOn (extendByBoundary C u F) (C ∪ inside C) :=
    boundary_continuity hC hu hF hsub hdense hcross hspoke
  have hK : IsCompact (C ∪ inside C) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_union_inside hsep)
      (hC.isCompact.isBounded.union hsep.isBounded_inside)
  
  have hmaps : MapsTo (extendByBoundary C u F) (C ∪ inside C) (Plane.closedSquare 0 1) := by
    rintro z (hz | hz)
    · rw [extendByBoundary_of_mem hz]
      exact modelCurve_subset_closedSquare (hu.mapsTo hz)
    · rw [extendByBoundary_of_notMem (inside_subset_compl hz)]
      exact Plane.openSquare_subset_closedSquare 0 1 (hF.mapsTo hz)
  have hmaps' : MapsTo (extendByBoundary modelCurve v F') (Plane.closedSquare 0 1)
      (C ∪ inside C) := by
    intro w hw
    by_cases hwc : w ∈ modelCurve
    · rw [extendByBoundary_of_mem hwc]
      exact Or.inl (hu.mapsTo_inv hwc)
    · have hwo : w ∈ Plane.openSquare 0 1 := by
        rw [← closedSquare_sdiff_modelCurve]; exact ⟨hw, hwc⟩
      rw [extendByBoundary_of_notMem hwc]
      exact Or.inr (hF.mapsTo_inv hwo)
  
  have hleft : LeftInvOn (extendByBoundary modelCurve v F') (extendByBoundary C u F)
      (C ∪ inside C) := by
    rintro z (hz | hz)
    · rw [extendByBoundary_of_mem hz, extendByBoundary_of_mem (hu.mapsTo hz)]
      exact hu.invOn.1 hz
    · have hFz : F z ∈ Plane.openSquare 0 1 := hF.mapsTo hz
      have : F z ∉ modelCurve := by
        rw [← inside_modelCurve] at hFz
        exact inside_subset_compl hFz
      rw [extendByBoundary_of_notMem (inside_subset_compl hz),
        extendByBoundary_of_notMem this]
      exact hF.invOn.1 hz
  have hright : RightInvOn (extendByBoundary modelCurve v F') (extendByBoundary C u F)
      (Plane.closedSquare 0 1) := by
    intro w hw
    by_cases hwc : w ∈ modelCurve
    · rw [extendByBoundary_of_mem hwc, extendByBoundary_of_mem (hu.mapsTo_inv hwc)]
      exact hu.invOn.2 hwc
    · have hwo : w ∈ Plane.openSquare 0 1 := by
        rw [← closedSquare_sdiff_modelCurve]; exact ⟨hw, hwc⟩
      have : F' w ∉ C := inside_subset_compl (hF.mapsTo_inv hwo)
      rw [extendByBoundary_of_notMem hwc, extendByBoundary_of_notMem this]
      exact hF.invOn.2 hwo
  
  refine ⟨hmaps, hmaps', hcont, ?_, hleft, hright⟩
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨extendByBoundary C u F '' (t ∩ (C ∪ inside C)), ?_, ?_⟩
  · exact ((hK.inter_left ht).image_of_continuousOn
      (hcont.mono inter_subset_right)).isClosed
  · ext w
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hwt, hw⟩
      exact ⟨⟨_, ⟨hwt, hmaps' hw⟩, hright hw⟩, hw⟩
    · rintro ⟨⟨z, ⟨hzt, hzK⟩, rfl⟩, hw⟩
      exact ⟨by rw [hleft hzK]; exact hzt, hw⟩

 

 







def HasLimitHomeomorphism : Prop :=
  ∀ (C : Set Plane) (u v : Plane → Plane), IsJordanCurve C → IsHomeoOn u v C modelCurve →
    ∃ (𝒜 : Set Plane) (F F' : Plane → Plane), 𝒜 ⊆ C ∧ C ⊆ closure 𝒜 ∧
      IsHomeoOn F F' (inside C) (Plane.openSquare 0 1) ∧
      HasAnchorCrosscuts C 𝒜 u F ∧ HasSpokes C 𝒜 u F

 

theorem squareExtension_of_hasLimitHomeomorphism (h : HasLimitHomeomorphism) :
    SquareExtension := by
  intro C u v hC hu
  obtain ⟨𝒜, F, F', hsub, hdense, hF, hcross, hspoke⟩ := h C u v hC hu
  exact ⟨extendByBoundary C u F, extendByBoundary modelCurve v F',
    isHomeoOn_extendByBoundary hC hu hF hsub hdense hcross hspoke,
    fun _ hz => extendByBoundary_of_mem hz⟩

end Schoenflies
