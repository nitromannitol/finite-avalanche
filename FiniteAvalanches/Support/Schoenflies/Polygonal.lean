/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Polygonal.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`;
explicit binders added for this project's Lean option `autoImplicit false`.
-/
import FiniteAvalanches.Support.Schoenflies.PolyPath
import FiniteAvalanches.Support.Schoenflies.Curve

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 
















open Metric Set

namespace Schoenflies

 

def IsPolygonal (A : Set Plane) : Prop := ∃ vs : List Plane, A = poly vs

theorem IsPolygonal.isCompact {A : Set Plane} (h : IsPolygonal A) : IsCompact A := by
  obtain ⟨vs, rfl⟩ := h
  exact isCompact_poly vs

@[simp] theorem poly_pair (a b : Plane) : poly [a, b] = segment ℝ a b := by
  rw [poly_cons_cons, poly_singleton]
  exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ a b))

theorem isPolygonal_segment (a b : Plane) : IsPolygonal (segment ℝ a b) :=
  ⟨[a, b], (poly_pair a b).symm⟩

 


theorem injOn_lineMap {a b : Plane} {I : Set ℝ} (hab : a ≠ b) :
    Set.InjOn (AffineMap.lineMap a b : ℝ → Plane) I := by
  intro s _ t _ hst
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have key : (s - t) • (b - a) = 0 := by
    simp only [AffineMap.lineMap_apply_module] at hst
    linear_combination (norm := module) hst
  rcases smul_eq_zero.1 key with h | h
  · linarith
  · exact absurd h hba

 

theorem isArcBetween_segment {a b : Plane} (hab : a ≠ b) :
    IsArcBetween (segment ℝ a b) a b := by
  refine ⟨AffineMap.lineMap a b, AffineMap.lineMap_continuous.continuousOn, ?_, ?_, ?_, ?_⟩
  · exact injOn_lineMap hab
  · rw [segment_eq_image_lineMap]
  · simp
  · simp

theorem isArc_segment {a b : Plane} (hab : a ≠ b) : IsArc (segment ℝ a b) :=
  (isArcBetween_segment hab).isArc

 


theorem exists_poly_anchored : ∀ (vs : List Plane), vs ≠ [] → ∀ z w : Plane,
    z ∈ poly vs → w ∈ poly vs → ∃ mid : List Plane, poly (z :: (mid ++ [w])) = poly vs := by
  intro vs
  induction vs with
  | nil => exact fun h => absurd rfl h
  | cons u tl ih =>
    rcases tl with _ | ⟨v, rest⟩
    · 
      intro _ z w hz hw
      rw [poly_singleton, Set.mem_singleton_iff] at hz hw
      subst hz; subst hw
      exact ⟨[], by simp [segment_same]⟩
    · intro _ z w hz hw
      have hne : (v :: rest) ≠ [] := List.cons_ne_nil v rest
      have hv : v ∈ poly (v :: rest) := mem_poly_of_mem (List.mem_cons_self ..)
      rw [poly_cons_cons] at hz hw
      
      have hsub : ∀ p ∈ segment ℝ u v, segment ℝ p u ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset hp (left_mem_segment ℝ u v)
      have hsub' : ∀ p ∈ segment ℝ u v, segment ℝ u p ⊆ segment ℝ u v := fun p hp =>
        (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hp
      rcases hz with hz | hz
      · rcases hw with hw | hw
        · 
          obtain ⟨Z, hZ⟩ := ih hne v v hv hv
          refine ⟨u :: v :: (Z ++ [v, v, u]), ?_⟩
          have hlast : (z :: u :: (v :: (Z ++ [v]))).getLast (by simp) = v := by
            simp
          have hsplit : z :: ((u :: v :: (Z ++ [v, v, u])) ++ [w])
              = (z :: u :: (v :: (Z ++ [v]))) ++ (v :: u :: [w]) := by
            simp
          have h1 : poly (z :: u :: (v :: (Z ++ [v])))
              = segment ℝ z u ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hZ]
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          have hd2 : segment ℝ u v ∪ segment ℝ u w ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            Set.union_subset Set.subset_union_left ((hsub' w hw).trans Set.subset_union_left)
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, h1, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1, Set.union_eq_self_of_subset_right hd2]
        · 
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨u :: v :: Y, ?_⟩
          have hsplit : z :: ((u :: v :: Y) ++ [w]) = z :: u :: (v :: (Y ++ [w])) := by simp
          have hd1 : segment ℝ z u ⊆ segment ℝ u v ∪ poly (v :: rest) :=
            (hsub z hz).trans Set.subset_union_left
          rw [hsplit, poly_cons_cons, poly_cons_cons, hY, poly_cons_cons,
            Set.union_eq_self_of_subset_left hd1]
      · rcases hw with hw | hw
        · 
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          refine ⟨X ++ [v, v, u], ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u]) ++ [w]) = (z :: (X ++ [v])) ++ (v :: u :: [w]) := by
            simp
          have h2 : poly (v :: u :: [w]) = segment ℝ u v ∪ segment ℝ u w := by
            rw [poly_cons_cons, poly_pair, segment_symm ℝ v u]
          rw [hsplit, poly_append (by simp) v (u :: [w]) hlast, hX, h2, poly_cons_cons,
            Set.union_eq_self_of_subset_right (hsub' w hw), Set.union_comm]
        · 
          obtain ⟨X, hX⟩ := ih hne z v hz hv
          obtain ⟨Y, hY⟩ := ih hne v w hv hw
          refine ⟨X ++ [v, v, u] ++ (v :: Y), ?_⟩
          have hlast : (z :: (X ++ [v])).getLast (by simp) = v := by simp
          have hsplit : z :: ((X ++ [v, v, u] ++ (v :: Y)) ++ [w])
              = (z :: (X ++ [v])) ++ (v :: u :: (v :: (Y ++ [w]))) := by simp
          have h2 : poly (v :: u :: (v :: (Y ++ [w])))
              = segment ℝ u v ∪ (segment ℝ u v ∪ poly (v :: rest)) := by
            rw [poly_cons_cons, poly_cons_cons, hY, segment_symm ℝ v u]
          have hd1 : segment ℝ u v ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_left
          have hd2 : poly (v :: rest) ⊆ segment ℝ u v ∪ poly (v :: rest) := Set.subset_union_right
          rw [hsplit, poly_append (by simp) v (u :: (v :: (Y ++ [w]))) hlast, hX, h2,
            poly_cons_cons, Set.union_eq_self_of_subset_left hd1,
            Set.union_eq_self_of_subset_left hd2]

 

theorem IsPolygonal.union {A B : Set Plane} (hA : IsPolygonal A) (hB : IsPolygonal B)
    (hmeet : (A ∩ B).Nonempty) : IsPolygonal (A ∪ B) := by
  obtain ⟨vs, rfl⟩ := hA
  obtain ⟨ws, rfl⟩ := hB
  obtain ⟨z, hzA, hzB⟩ := hmeet
  have hvs : vs ≠ [] := by rintro rfl; exact hzA
  have hws : ws ≠ [] := by rintro rfl; exact hzB
  obtain ⟨X, hX⟩ := exists_poly_anchored vs hvs z z hzA hzA
  obtain ⟨Y, hY⟩ := exists_poly_anchored ws hws z z hzB hzB
  refine ⟨(z :: (X ++ [z])) ++ (z :: (Y ++ [z])), ?_⟩
  have hlast : (z :: (X ++ [z])).getLast (by simp) = z := by simp
  rw [poly_append (by simp) z (Y ++ [z]) hlast, hX, hY]

end Schoenflies
