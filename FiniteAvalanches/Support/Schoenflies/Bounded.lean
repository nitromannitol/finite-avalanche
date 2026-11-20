/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Bounded.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Square

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 




















open Metric Set

namespace Schoenflies

namespace Plane

@[simp] theorem supDist_zero (x : Plane) : supDist x 0 = supNorm x := by
  simp [supDist, supNorm]

 
theorem beyondSquare_eq_compl (r : ℝ) : beyondSquare r = (closedSquare 0 r)ᶜ := by
  ext x
  simp only [beyondSquare, closedSquare, mem_setOf_eq, mem_compl_iff, supDist_zero, supNorm,
    max_le_iff, not_and_or, not_le]

 
theorem exists_closedSquare_of_isBounded {s : Set Plane} (hs : Bornology.IsBounded s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have hnorm : ‖x‖ ≤ R := by simpa using hR hx
  have : supNorm x ≤ R := le_trans (supNorm_le_norm x) hnorm
  simpa [closedSquare, supDist_zero] using le_trans this (le_max_left _ _)

theorem IsCompact.exists_closedSquare {s : Set Plane} (hs : IsCompact s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded hs.isBounded

 

theorem closedSquare_mono {r s : ℝ} (h : r ≤ s) : closedSquare 0 r ⊆ closedSquare 0 s :=
  fun _ hx => le_trans hx h

 
theorem exists_closedSquare_of_finite {ι : Type*} {S : ι → Set Plane} {t : Set ι}
    (ht : t.Finite) (hS : ∀ i ∈ t, Bornology.IsBounded (S i)) :
    ∃ r : ℝ, 0 ≤ r ∧ (⋃ i ∈ t, S i) ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded ((Bornology.isBounded_biUnion ht).2 hS)

 

theorem isOpen_compl_of_finite_isCompact {ι : Type*} {S : ι → Set Plane} {t : Set ι}
    (ht : t.Finite) (hS : ∀ i ∈ t, IsCompact (S i)) : IsOpen (⋃ i ∈ t, S i)ᶜ :=
  (ht.isClosed_biUnion fun i hi => (hS i hi).isClosed).isOpen_compl

end Plane

end Schoenflies
