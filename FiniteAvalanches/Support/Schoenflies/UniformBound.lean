/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/UniformBound.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Plane

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 


















open Set

namespace Schoenflies

variable {ι : Type*}

 
theorem exists_pos_le_of_finite {S : Set ι} (hS : S.Finite) {f : ι → ℝ}
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε > 0, ∀ i ∈ S, ε ≤ f i := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a S ha hS ih =>
    obtain ⟨ε, hε, hbound⟩ := ih fun i hi => hf i (mem_insert_of_mem _ hi)
    refine ⟨min ε (f a), lt_min hε (hf a (mem_insert _ _)), fun i hi => ?_⟩
    rcases mem_insert_iff.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hbound i hi)

 


theorem exists_pos_forall_of_finite {S : Set ι} (hS : S.Finite) {P : ι → ℝ → Prop}
    (hmono : ∀ i, ∀ ⦃δ ε : ℝ⦄, 0 < δ → δ ≤ ε → P i ε → P i δ)
    (hex : ∀ i ∈ S, ∃ ε > 0, P i ε) :
    ∃ ε > 0, ∀ i ∈ S, P i ε := by
  classical
  
  choose! f hfpos hfP using hex
  obtain ⟨ε, hε, hbound⟩ := exists_pos_le_of_finite hS (f := f) hfpos
  exact ⟨ε, hε, fun i hi => hmono i hε (hbound i hi) (hfP i hi)⟩

end Schoenflies
