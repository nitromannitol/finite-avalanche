/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/JordanSchoenflies.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.BoundaryAnchors

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 













open Set

namespace Schoenflies

 

theorem hasLimitHomeomorphism : HasLimitHomeomorphism := by
  intro C u v hC hu
  let T := prescribedJordanStageSequence hC u v hu
  exact ⟨prescribedSourceAnchorSet hC hu, T.limitTower.F, T.limitTower.inv,
    prescribedSourceAnchorSet_subset hC hu,
    prescribedSourceAnchorSet_dense hC hu,
    T.isHomeoOn_F,
    prescribedSourceAnchorSet_hasAnchorCrosscuts hC hu,
    prescribedSourceAnchorSet_hasSpokes hC hu⟩

 

theorem squareExtension : SquareExtension :=
  squareExtension_of_hasLimitHomeomorphism hasLimitHomeomorphism

variable {C C' : Set Plane}

 
theorem jordan_schoenflies {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G univ univ ∧ EqOn F f C :=
  jordan_schoenflies_of_squareExtension squareExtension hC hC' hfg

 

theorem jordan_schoenflies_homeomorph {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F : Plane ≃ₜ Plane, EqOn F f C :=
  jordan_schoenflies_homeomorph_of_squareExtension squareExtension hC hC' hfg

 

theorem jordan_schoenflies_of_homeomorph
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z :=
  jordan_schoenflies_of_homeomorph_of_squareExtension squareExtension hC hC' e

end Schoenflies
