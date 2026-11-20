/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Line.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Plane
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.Order.Bornology
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 











































open Bornology Metric Set

namespace Schoenflies

 





 

theorem exists_Ioo_eq_connectedComponentIn {T : Set ℝ} (hopen : IsOpen T) (hbdd : IsBounded T)
    {s : ℝ} (hs : s ∈ T) :
    ∃ t₀ t₁ : ℝ, t₀ < t₁ ∧ connectedComponentIn T s = Ioo t₀ t₁ ∧ t₀ ∉ T ∧ t₁ ∉ T := by
  set J := connectedComponentIn T s with hJdef
  have hJsub : J ⊆ T := connectedComponentIn_subset T s
  have hJs : s ∈ J := mem_connectedComponentIn hs
  have hJopen : IsOpen J := hopen.connectedComponentIn
  have hJord : J.OrdConnected :=
    (isPreconnected_connectedComponentIn (F := T) (x := s)).ordConnected
  have hbb : BddBelow J := (hbdd.subset hJsub).bddBelow
  have hba : BddAbove J := (hbdd.subset hJsub).bddAbove
  have hne : J.Nonempty := ⟨s, hJs⟩
  
  have hout : ∀ x ∈ J, sInf J < x ∧ x < sSup J := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hJopen x hx
    have hlo : x - ε / 2 ∈ J := by
      refine hball ?_
      rw [mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    have hhi : x + ε / 2 ∈ J := by
      refine hball ?_
      rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    exact ⟨lt_of_le_of_lt (csInf_le hbb hlo) (by linarith),
      lt_of_lt_of_le (by linarith : x < x + ε / 2) (le_csSup hba hhi)⟩
  
  have hIoo : Ioo (sInf J) (sSup J) ⊆ J := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := exists_lt_of_csInf_lt hne hx.1
    obtain ⟨v, hv, hxv⟩ := exists_lt_of_lt_csSup hne hx.2
    exact hJord.out hu hv ⟨hux.le, hxv.le⟩
  have hlt : sInf J < sSup J := (hout s hJs).1.trans (hout s hJs).2
  refine ⟨sInf J, sSup J, hlt, subset_antisymm (fun x hx => hout x hx) hIoo, ?_, ?_⟩
  · 
    intro hmem
    have hsub : Ico (sInf J) (sSup J) ⊆ T := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · rw [← h]; exact hmem
      · exact hJsub (hIoo ⟨h, hx.2⟩)
    have h2 := (isPreconnected_Ico (a := sInf J) (b := sSup J)).subset_connectedComponentIn
      (show s ∈ Ico (sInf J) (sSup J) from ⟨(hout s hJs).1.le, (hout s hJs).2⟩) hsub
    exact absurd (hout _ (h2 ⟨le_rfl, hlt⟩)).1 (lt_irrefl _)
  · intro hmem
    have hsub : Ioc (sInf J) (sSup J) ⊆ T := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with h | h
      · rw [h]; exact hmem
      · exact hJsub (hIoo ⟨hx.1, h⟩)
    have h2 := (isPreconnected_Ioc (a := sInf J) (b := sSup J)).subset_connectedComponentIn
      (show s ∈ Ioc (sInf J) (sSup J) from ⟨(hout s hJs).1, (hout s hJs).2.le⟩) hsub
    exact absurd (hout _ (h2 ⟨hlt, le_rfl⟩)).2 (lt_irrefl _)

namespace Plane

variable {a b x y : Plane} {S U : Set Plane}

 

 


def line (a b : Plane) : Set Plane := Set.range (AffineMap.lineMap a b : ℝ → Plane)

 


noncomputable def lineCoord (a b x : Plane) : ℝ := inner ℝ (x - a) (b - a) / ‖b - a‖ ^ 2

theorem mem_line_iff : x ∈ line a b ↔ ∃ t : ℝ, AffineMap.lineMap a b t = x := Iff.rfl

theorem lineMap_mem_line (a b : Plane) (t : ℝ) : AffineMap.lineMap a b t ∈ line a b :=
  mem_range_self t

@[simp] theorem left_mem_line (a b : Plane) : a ∈ line a b :=
  ⟨0, AffineMap.lineMap_apply_zero a b⟩

@[simp] theorem right_mem_line (a b : Plane) : b ∈ line a b :=
  ⟨1, AffineMap.lineMap_apply_one a b⟩

 
theorem line_eq_affineSpan (a b : Plane) :
    line a b = (affineSpan ℝ ({a, b} : Set Plane) : Set Plane) := by
  ext x
  rw [mem_line_iff, SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]

theorem continuous_lineCoord (a b : Plane) : Continuous (lineCoord a b) := by
  unfold lineCoord
  fun_prop

 
@[simp] theorem lineCoord_lineMap (hab : a ≠ b) (t : ℝ) :
    lineCoord a b (AffineMap.lineMap a b t) = t := by
  have hne : ‖b - a‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero, sub_eq_zero]
    exact fun h => hab h.symm
  have hsub : (AffineMap.lineMap a b t : Plane) - a = t • (b - a) := by
    rw [AffineMap.lineMap_apply_module']
    abel
  rw [lineCoord, hsub, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

 

theorem lineMap_lineCoord (hx : x ∈ line a b) :
    AffineMap.lineMap a b (lineCoord a b x) = x := by
  obtain ⟨t, rfl⟩ := hx
  rcases eq_or_ne a b with rfl | hab
  · simp
  · rw [lineCoord_lineMap hab]

theorem lineMap_injective (hab : a ≠ b) :
    Function.Injective (AffineMap.lineMap a b : ℝ → Plane) :=
  Function.LeftInverse.injective (g := lineCoord a b) (lineCoord_lineMap hab)

 
theorem isClosed_line (a b : Plane) : IsClosed (line a b) := by
  have hchar : line a b = {x : Plane | AffineMap.lineMap a b (lineCoord a b x) = x} :=
    Set.ext fun x => ⟨fun hx => lineMap_lineCoord hx, fun hx => hx ▸ lineMap_mem_line a b _⟩
  rw [hchar]
  exact isClosed_eq (AffineMap.lineMap_continuous.comp (continuous_lineCoord a b)) continuous_id

 

theorem mem_line_iff_det_eq_zero (hab : a ≠ b) :
    x ∈ line a b ↔ det (b - a) (x - a) = 0 := by
  have hu : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  rw [det_eq_zero_iff_smul _ _ hu, mem_line_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [AffineMap.lineMap_apply_module']; abel⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by rw [AffineMap.lineMap_apply_module', ← hr]; abel⟩

 

 

theorem exists_segment_eq_of_isCompact_isConnected (hS : S ⊆ line a b) (hcompact : IsCompact S)
    (hconn : IsConnected S) :
    ∃ p q : Plane, p ∈ S ∧ q ∈ S ∧ S = segment ℝ p q := by
  
  set T : Set ℝ := lineCoord a b '' S with hTdef
  have hTcompact : IsCompact T := hcompact.image (continuous_lineCoord a b)
  have hTconn : IsConnected T := hconn.image _ (continuous_lineCoord a b).continuousOn
  obtain ⟨t₀, t₁, hT⟩ : ∃ t₀ t₁, T = Icc t₀ t₁ :=
    ⟨_, _, eq_Icc_of_connected_compact hTconn hTcompact⟩
  have hle : t₀ ≤ t₁ := by
    rw [hT] at hTconn
    exact nonempty_Icc.1 hTconn.nonempty
  
  have himage : (AffineMap.lineMap a b : ℝ → Plane) '' T = S := by
    rw [hTdef, image_image]
    exact (image_congr fun z hz => lineMap_lineCoord (hS hz)).trans (image_id S)
  have hmem : ∀ t ∈ T, (AffineMap.lineMap a b t : Plane) ∈ S := fun t ht => himage ▸ ⟨t, ht, rfl⟩
  refine ⟨AffineMap.lineMap a b t₀, AffineMap.lineMap a b t₁,
    hmem _ (hT ▸ left_mem_Icc.2 hle), hmem _ (hT ▸ right_mem_Icc.2 hle), ?_⟩
  rw [← himage, hT, ← segment_eq_Icc hle, image_segment]

 

theorem exists_segment_eq_of_not_subsingleton (hS : S ⊆ line a b) (hcompact : IsCompact S)
    (hconn : IsConnected S) (hnontriv : ¬ S.Subsingleton) :
    ∃ p q : Plane, p ≠ q ∧ p ∈ S ∧ q ∈ S ∧ S = segment ℝ p q := by
  obtain ⟨p, q, hp, hq, hSeq⟩ := exists_segment_eq_of_isCompact_isConnected hS hcompact hconn
  refine ⟨p, q, ?_, hp, hq, hSeq⟩
  rintro rfl
  rw [segment_same] at hSeq
  exact hnontriv (hSeq ▸ subsingleton_singleton)

 

 





theorem exists_openSegment_eq_connectedComponentIn (hab : a ≠ b) (hU : IsOpen U)
    (hbdd : IsBounded U) (hy : y ∈ line a b ∩ U) :
    ∃ p q : Plane, p ≠ q ∧ p ∈ line a b ∧ q ∈ line a b ∧
      connectedComponentIn (line a b ∩ U) y = openSegment ℝ p q ∧
      closure (connectedComponentIn (line a b ∩ U) y) = segment ℝ p q ∧
      p ∈ frontier U ∧ q ∈ frontier U := by
  set f : ℝ → Plane := (AffineMap.lineMap a b : ℝ → Plane) with hfdef
  
  
  set T : Set ℝ := f ⁻¹' U with hTdef
  have hTopen : IsOpen T := hU.preimage AffineMap.lineMap_continuous
  have hTbdd : IsBounded T := by
    have hpos : 0 < dist a b := dist_pos.2 hab
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hbdd
    refine Metric.isBounded_iff.2 ⟨C / dist a b, fun s hs t ht => ?_⟩
    have h1 : dist s t * dist a b ≤ C := by
      have h2 := hC hs ht
      rwa [hfdef, dist_lineMap_lineMap] at h2
    exact (le_div_iff₀ hpos).2 h1
  set s : ℝ := lineCoord a b y with hsdef
  have hfs : f s = y := lineMap_lineCoord hy.1
  have hsT : s ∈ T := by rw [hTdef, mem_preimage, hfs]; exact hy.2
  obtain ⟨t₀, t₁, hlt, hJ, hn0, hn1⟩ := exists_Ioo_eq_connectedComponentIn hTopen hTbdd hsT
  have hIooT : Ioo t₀ t₁ ⊆ T := hJ ▸ connectedComponentIn_subset T s
  have hsIoo : s ∈ Ioo t₀ t₁ := hJ ▸ mem_connectedComponentIn hsT
  
  have hC : connectedComponentIn (line a b ∩ U) y = f '' Ioo t₀ t₁ := by
    refine subset_antisymm (fun z hz => ?_) ?_
    · 
      have hzmem : z ∈ line a b ∩ U := connectedComponentIn_subset _ _ hz
      have hsubT : lineCoord a b '' connectedComponentIn (line a b ∩ U) y ⊆ T := by
        rintro _ ⟨w, hw, rfl⟩
        have hwmem : w ∈ line a b ∩ U := connectedComponentIn_subset _ _ hw
        rw [hTdef, mem_preimage, hfdef, lineMap_lineCoord hwmem.1]
        exact hwmem.2
      have hpre : IsPreconnected (lineCoord a b '' connectedComponentIn (line a b ∩ U) y) :=
        isPreconnected_connectedComponentIn.image _ (continuous_lineCoord a b).continuousOn
      have hsub := hpre.subset_connectedComponentIn ⟨y, mem_connectedComponentIn hy, hsdef.symm⟩
        hsubT
      rw [hJ] at hsub
      exact ⟨lineCoord a b z, hsub ⟨z, hz, rfl⟩, lineMap_lineCoord hzmem.1⟩
    · 
      refine (isPreconnected_Ioo.image f
        AffineMap.lineMap_continuous.continuousOn).subset_connectedComponentIn ⟨s, hsIoo, hfs⟩ ?_
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨lineMap_mem_line a b t, hIooT ht⟩
  
  have himg : f '' Ioo t₀ t₁ = openSegment ℝ (f t₀) (f t₁) := by
    rw [← openSegment_eq_Ioo hlt, hfdef, image_openSegment]
  have hclos : closure (connectedComponentIn (line a b ∩ U) y) = segment ℝ (f t₀) (f t₁) := by
    rw [hC, himg, closure_openSegment]
  
  have hsubclos : closure (connectedComponentIn (line a b ∩ U) y) ⊆ closure U :=
    closure_mono fun z hz => (connectedComponentIn_subset _ _ hz).2
  have hfrontier : ∀ t : ℝ, t ∉ T → f t ∈ segment ℝ (f t₀) (f t₁) → f t ∈ frontier U := by
    intro t ht hseg
    rw [hU.frontier_eq]
    exact ⟨hsubclos (by rw [hclos]; exact hseg), fun h => ht h⟩
  exact ⟨f t₀, f t₁, fun h => hlt.ne (lineMap_injective hab h),
    lineMap_mem_line a b t₀, lineMap_mem_line a b t₁, by rw [hC, himg], hclos,
    hfrontier t₀ hn0 (left_mem_segment ℝ _ _), hfrontier t₁ hn1 (right_mem_segment ℝ _ _)⟩

 

 
theorem eqOn_line_of_fixed (F : Plane →ᵃ[ℝ] Plane) (ha : F a = a) (hb : F b = b) :
    EqOn F id (line a b) := by
  rintro _ ⟨t, rfl⟩
  rw [id, F.apply_lineMap, ha, hb]

 

theorem affineMap_ext_of_affineIndependent {p : Fin 3 → Plane} (hp : AffineIndependent ℝ p)
    (F G : Plane →ᵃ[ℝ] Plane) (h : ∀ i, F (p i) = G (p i)) : F = G := by
  refine AffineMap.ext_on (s := Set.range p) ?_ ?_
  · rw [hp.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp
  · rintro _ ⟨i, rfl⟩
    exact h i

end Plane

end Schoenflies
