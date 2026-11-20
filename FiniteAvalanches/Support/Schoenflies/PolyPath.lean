/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/PolyPath.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Plane
import Mathlib.Analysis.Convex.PathConnected

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 















open Metric Set

namespace Schoenflies

variable {Ω : Set Plane} {x y z : Plane}

 

theorem isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image' ℝ x y]
  exact isCompact_Icc.image (by fun_prop)

 

 

def poly : List Plane → Set Plane
  | [] => ∅
  | [v] => {v}
  | u :: v :: rest => segment ℝ u v ∪ poly (v :: rest)

@[simp] theorem poly_nil : poly [] = ∅ := rfl

@[simp] theorem poly_singleton (v : Plane) : poly [v] = {v} := rfl

@[simp] theorem poly_cons_cons (u v : Plane) (rest : List Plane) :
    poly (u :: v :: rest) = segment ℝ u v ∪ poly (v :: rest) := rfl

theorem poly_nonempty : ∀ {vs : List Plane}, vs ≠ [] → (poly vs).Nonempty
  | [], h => absurd rfl h
  | [v], _ => ⟨v, rfl⟩
  | _ :: v :: _, _ => ⟨v, Or.inl (right_mem_segment ℝ _ _)⟩

theorem isCompact_poly : ∀ vs : List Plane, IsCompact (poly vs)
  | [] => by simp
  | [v] => by simp
  | u :: v :: rest => by
    rw [poly_cons_cons]
    exact (isCompact_segment u v).union (isCompact_poly (v :: rest))

 
theorem mem_poly_of_mem : ∀ {vs : List Plane} {v : Plane}, v ∈ vs → v ∈ poly vs
  | [], _, h => absurd h (by simp)
  | [_], _, h => by simpa using h
  | u :: w :: rest, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (mem_poly_of_mem h)

theorem head_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.head h ∈ poly vs :=
  mem_poly_of_mem (List.head_mem h)

theorem getLast_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.getLast h ∈ poly vs :=
  mem_poly_of_mem (List.getLast_mem h)

 
theorem isConnected_poly : ∀ {vs : List Plane}, vs ≠ [] → IsConnected (poly vs)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isConnected_singleton (x := v)
  | u :: v :: rest, _ => by
    rw [poly_cons_cons]
    refine IsConnected.union ⟨v, right_mem_segment ℝ u v, head_mem_poly (by simp)⟩
      ((convex_segment u v).isConnected ⟨u, left_mem_segment ℝ u v⟩)
      (isConnected_poly (List.cons_ne_nil v rest))

 
theorem poly_concat : ∀ {vs : List Plane} (h : vs ≠ []) (z : Plane),
    poly (vs ++ [z]) = poly vs ∪ segment ℝ (vs.getLast h) z
  | [], h, _ => absurd rfl h
  | [v], _, z => by
    simp only [List.singleton_append, poly_cons_cons, poly_singleton, List.getLast_singleton]
    rw [union_singleton, insert_eq_self.2 (right_mem_segment ℝ v z), singleton_union,
      insert_eq_self.2 (left_mem_segment ℝ v z)]
  | u :: v :: rest, _, z => by
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_concat (List.cons_ne_nil v rest) z,
      List.getLast_cons (List.cons_ne_nil v rest)]
    exact (union_assoc _ _ _).symm

 

 





theorem exists_poly_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = y := by
  
  set R : Set Plane :=
    {w ∈ Ω | ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w}
    with hR
  
  
  have key : ∀ C : Set Plane, Convex ℝ C → C ⊆ Ω → ∀ w ∈ C, ∀ z ∈ C,
      (∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w) →
      ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = z := by
    rintro C hC hCΩ w hw z hz ⟨vs, hne, hsub, hhead, hlast⟩
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact union_subset hsub ((hC.segment_subset hw hz).trans hCΩ)
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp
  have hRopen : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hpath⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    exact ⟨ball w r, fun z hz =>
      ⟨hball hz, key _ (convex_ball w r) hball w (mem_ball_self hr) z hz hpath⟩,
      isOpen_ball, mem_ball_self hr⟩
  have hRcompl : IsOpen (Ω \ R) := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hwR⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    refine ⟨ball w r, fun z hz => ⟨hball hz, fun hzR => ?_⟩, isOpen_ball, mem_ball_self hr⟩
    
    exact hwR ⟨hw, key _ (convex_ball w r) hball z hz w (mem_ball_self hr) hzR.2⟩
  
  have hxR : x ∈ R := ⟨hx, [x], by simp, by simpa using hx, rfl, rfl⟩
  have : y ∈ R := by
    by_contra hyR
    obtain ⟨w, _, hw⟩ := hconn R (Ω \ R) hRopen hRcompl
      (fun w hw => (em (w ∈ R)).imp id fun h => ⟨hw, h⟩) ⟨x, hx, hxR⟩ ⟨y, hy, hy, hyR⟩
    exact hw.2.2 hw.1
  exact this.2

 


theorem poly_append : ∀ {vs : List Plane} (h : vs ≠ []) (w : Plane) (rest : List Plane),
    vs.getLast h = w → poly (vs ++ w :: rest) = poly vs ∪ poly (w :: rest)
  | [], h, _, _, _ => absurd rfl h
  | [v], _, w, rest, hvw => by
    simp only [List.getLast_singleton] at hvw
    subst hvw
    simp [segment_same]
  | u :: v :: tl, _, w, rest, hvw => by
    have h' : (v :: tl).getLast (List.cons_ne_nil v tl) = w := by
      rw [← List.getLast_cons (a := u) (List.cons_ne_nil v tl)]; exact hvw
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_append (List.cons_ne_nil v tl) w rest h']
    exact (union_assoc _ _ _).symm

end Schoenflies
