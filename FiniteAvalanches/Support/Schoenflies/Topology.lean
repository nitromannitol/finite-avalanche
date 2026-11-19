/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Topology.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Plane
import Mathlib.Topology.Connected.LocallyConnected

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 























open Metric Set

namespace Schoenflies

namespace Plane

variable {U K : Set Plane} {x : Plane}

 
theorem isOpen_connectedComponentIn (hU : IsOpen U) : IsOpen (connectedComponentIn U x) :=
  hU.connectedComponentIn

 




theorem frontier_connectedComponentIn_compl_subset (hK : IsClosed K) (x : Plane) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  set C := connectedComponentIn Kᶜ x with hC
  have hCopen : IsOpen C := isOpen_connectedComponentIn hK.isOpen_compl
  intro z hz
  by_contra hzK
  
  rw [hCopen.frontier_eq] at hz
  obtain ⟨hzclosure, hzC⟩ := hz
  
  have hxU : x ∈ Kᶜ := by
    by_contra hx
    rw [hC, connectedComponentIn_eq_empty hx] at hzclosure
    simp at hzclosure
  
  have hsub : C ∪ {z} ⊆ Kᶜ := by
    refine union_subset (connectedComponentIn_subset _ _) ?_
    simpa using hzK
  have hconn : IsPreconnected (C ∪ {z}) :=
    (isPreconnected_connectedComponentIn (F := Kᶜ) (x := x)).subset_closure
      subset_union_left (union_subset subset_closure (by simpa using hzclosure))
  have : C ∪ {z} ⊆ C :=
    hconn.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hxU)) hsub
  exact hzC (this (Or.inr rfl))

 
theorem continuousOn_union_of_isClosed {f : Plane → Plane} {s t : Set Plane}
    (hs : IsClosed s) (ht : IsClosed t) (hfs : ContinuousOn f s) (hft : ContinuousOn f t) :
    ContinuousOn f (s ∪ t) :=
  (continuousOn_union_iff_of_isClosed hs ht).2 ⟨hfs, hft⟩

end Plane

end Schoenflies
