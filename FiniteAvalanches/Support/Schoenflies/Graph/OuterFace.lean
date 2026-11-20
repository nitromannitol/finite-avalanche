/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/OuterFace.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.Graph.Drawing

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 





















open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

 

theorem isBounded_closedSquare (r : ℝ) :
    Bornology.IsBounded (Schoenflies.Plane.closedSquare 0 r) := by
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := Real.sqrt 2 * r)).subset ?_
  intro x hx
  have hsup : Schoenflies.Plane.supNorm x ≤ r := by
    simpa [Schoenflies.Plane.closedSquare] using hx
  have : ‖x‖ ≤ Real.sqrt 2 * r := by
    refine le_trans (Schoenflies.Plane.norm_le_sqrt_two_mul_supNorm x) ?_
    exact mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2)
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

 
theorem IsDrawing.exists_closedSquare [G.Finite] (h : IsDrawing G drawing) :
    ∃ r : ℝ, 0 ≤ r ∧ pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r :=
  Schoenflies.Plane.exists_closedSquare_of_isBounded h.isCompact_pointSet.isBounded

 
theorem beyondSquare_subset_exterior {r : ℝ}
    (hr : pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r) :
    Schoenflies.Plane.beyondSquare r ⊆ exterior G drawing := by
  rw [Schoenflies.Plane.beyondSquare_eq_compl]
  exact compl_subset_compl.2 hr

 

theorem beyondSquare_subset_face {r : ℝ}
    (hr : pointSet G drawing ⊆ Schoenflies.Plane.closedSquare 0 r) {base : Plane}
    (hbase : base ∈ Schoenflies.Plane.beyondSquare r) :
    Schoenflies.Plane.beyondSquare r ⊆ face G drawing base :=
  (Schoenflies.Plane.isConnected_beyondSquare r).isPreconnected.subset_connectedComponentIn
    hbase (beyondSquare_subset_exterior hr)

 
theorem not_isBounded_beyondSquare (r : ℝ) :
    ¬ Bornology.IsBounded (Schoenflies.Plane.beyondSquare r) := by
  intro hb
  obtain ⟨s, -, hs⟩ := Schoenflies.Plane.exists_closedSquare_of_isBounded hb
  
  
  set t : ℝ := max (max r s) 0 + 1 with ht
  have ht0 : 0 ≤ t := by
    have := le_max_right (max r s) 0; simp only [ht]; linarith
  have htr : r < t := by
    have h1 := le_max_left r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  have hts : s < t := by
    have h1 := le_max_right r s
    have h2 := le_max_left (max r s) 0
    simp only [ht]; linarith
  
  have hmem : Schoenflies.Plane.mk t 0 ∈ Schoenflies.Plane.beyondSquare r :=
    Or.inl (show r < |t| by rw [abs_of_nonneg ht0]; exact htr)
  have hin := hs hmem
  simp only [Schoenflies.Plane.closedSquare, mem_setOf_eq, Schoenflies.Plane.supDist_zero,
    Schoenflies.Plane.supNorm, max_le_iff] at hin
  have h1 : |t| ≤ s := hin.1
  rw [abs_of_nonneg ht0] at h1
  linarith

 
theorem exists_unbounded_face [G.Finite] (h : IsDrawing G drawing) :
    ∃ base ∈ exterior G drawing, ¬ Bornology.IsBounded (face G drawing base) := by
  obtain ⟨r, hr0, hr⟩ := h.exists_closedSquare
  have hmem : Schoenflies.Plane.mk (r + 1) 0 ∈ Schoenflies.Plane.beyondSquare r :=
    Or.inl (show r < |r + 1| by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ r + 1)]; linarith)
  refine ⟨Schoenflies.Plane.mk (r + 1) 0, beyondSquare_subset_exterior hr hmem, fun hb => ?_⟩
  exact not_isBounded_beyondSquare r (hb.subset (beyondSquare_subset_face hr hmem))

 

theorem unbounded_face_unique [G.Finite] (h : IsDrawing G drawing) {b c : Plane}
    (hbu : ¬ Bornology.IsBounded (face G drawing b))
    (hcu : ¬ Bornology.IsBounded (face G drawing c)) :
    face G drawing b = face G drawing c := by
  obtain ⟨r, hr0, hr⟩ := h.exists_closedSquare
  
  have escape : ∀ z : Plane, ¬ Bornology.IsBounded (face G drawing z) →
      ∃ w, w ∈ face G drawing z ∧ w ∈ Schoenflies.Plane.beyondSquare r := by
    intro z hz
    by_contra hcon
    push Not at hcon
    refine hz ((isBounded_closedSquare r).subset fun w hw => ?_)
    have hw' : w ∉ Schoenflies.Plane.beyondSquare r := hcon w hw
    rw [Schoenflies.Plane.beyondSquare_eq_compl] at hw'
    simpa using hw'
  obtain ⟨w, hwb, hwout⟩ := escape b hbu
  obtain ⟨v, hvc, hvout⟩ := escape c hcu
  
  have hbeyond_b : Schoenflies.Plane.beyondSquare r ⊆ face G drawing b := by
    have hsub := beyondSquare_subset_face (G := G) (drawing := drawing) hr hwout
    have hwe : face G drawing w = face G drawing b := (connectedComponentIn_eq hwb).symm
    rwa [hwe] at hsub
  have hbeyond_c : Schoenflies.Plane.beyondSquare r ⊆ face G drawing c := by
    have hsub := beyondSquare_subset_face (G := G) (drawing := drawing) hr hvout
    have hve : face G drawing v = face G drawing c := (connectedComponentIn_eq hvc).symm
    rwa [hve] at hsub
  obtain ⟨z, hz⟩ := (Schoenflies.Plane.isConnected_beyondSquare r).nonempty
  have e1 : face G drawing b = face G drawing z := connectedComponentIn_eq (hbeyond_b hz)
  have e2 : face G drawing c = face G drawing z := connectedComponentIn_eq (hbeyond_c hz)
  rw [e1, e2]

end Graph
