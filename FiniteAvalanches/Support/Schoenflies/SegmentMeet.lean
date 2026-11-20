/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/SegmentMeet.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.PolyPath

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 

















open Metric Set

namespace Schoenflies

 
theorem segment_inter_segment (a b c d : Plane)
    (hne : (segment ℝ a b ∩ segment ℝ c d).Nonempty) :
    ∃ p q : Plane, segment ℝ a b ∩ segment ℝ c d = segment ℝ p q := by
  set S : Set Plane := segment ℝ a b ∩ segment ℝ c d with hSdef
  have hScompact : IsCompact S := (isCompact_segment a b).inter (isCompact_segment c d)
  have hSconvex : Convex ℝ S := (convex_segment a b).inter (convex_segment c d)
  
  set f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap a b with hfdef
  set T : Set ℝ := Icc 0 1 ∩ f ⁻¹' S with hTdef
  
  
  have himage : f '' T = S := by
    refine subset_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨t, ht, rfl⟩ := hx
      exact ht.2
    · have : x ∈ segment ℝ a b := hx.1
      rw [segment_eq_image_lineMap] at this
      obtain ⟨t, ht, rfl⟩ := this
      exact ⟨t, ⟨ht, hx⟩, rfl⟩
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have : x ∈ f '' T := by rw [himage]; exact hx
    obtain ⟨t, ht, -⟩ := this
    exact ⟨t, ht⟩
  have hTcompact : IsCompact T :=
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.inter (hScompact.isClosed.preimage AffineMap.lineMap_continuous))
      inter_subset_left
  have hTconvex : Convex ℝ T := (convex_Icc 0 1).inter (hSconvex.affine_preimage f)
  
  obtain ⟨t₀, t₁, hTIcc⟩ : ∃ t₀ t₁, T = Icc t₀ t₁ :=
    ⟨_, _, eq_Icc_of_connected_compact ⟨hTne, hTconvex.isPreconnected⟩ hTcompact⟩
  have hle : t₀ ≤ t₁ := by
    rw [hTIcc] at hTne
    exact nonempty_Icc.1 hTne
  exact ⟨f t₀, f t₁, by rw [← himage, hTIcc, ← segment_eq_Icc hle, image_segment]⟩

end Schoenflies
