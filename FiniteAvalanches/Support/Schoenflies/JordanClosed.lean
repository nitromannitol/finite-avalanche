/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/JordanClosed.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.SquareCycle
import FiniteAvalanches.Support.Schoenflies.PolyArcRealize
import FiniteAvalanches.Support.Schoenflies.Jordan

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 


































open Set

namespace Schoenflies

 
theorem arc_complement {A : Set Plane} (hA : IsArc A) : IsConnected Aᶜ :=
  isConnected_compl_arc hA squaresTwoConnected

 

theorem arc_complement_poly {A : Set Plane} (hA : IsArc A) {u w : Plane}
    (huw : u ≠ w) (hu : u ∉ A) (hw : w ∉ A) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P u w ∧ P ⊆ Aᶜ :=
  exists_simple_poly_compl_arc hA squaresTwoConnected huw hu hw

 






theorem jordan_curve_theorem {C : Set Plane} (hC : IsJordanCurve C) : IsSeparating C :=
  hC.isSeparating fun _ hA => arc_complement hA

 


theorem crosscut_theorem {C P A₁ A₂ : Set Plane} {p q : Plane}
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧ closure (inside (A₂ ∪ P)) ∩ C = A₂ :=
  general_crosscut' (fun _ hS => jordan_curve_theorem hS) h hcut

end Schoenflies
