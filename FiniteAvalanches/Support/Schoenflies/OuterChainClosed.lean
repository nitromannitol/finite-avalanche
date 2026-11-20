/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/OuterChainClosed.lean.
Modified for this project: comments removed and replaced by a one-line module docstring, and
imports renamed to `FiniteAvalanches.Support.Schoenflies`.
-/
import FiniteAvalanches.Support.Schoenflies.CrosscutExists
import FiniteAvalanches.Support.Schoenflies.CrosscutEncloses

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 






















open Set Schoenflies
open scoped Graph

namespace Graph

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {n : ℕ} {x : Plane}

namespace IsPlaneChain

 






theorem outer_chain' (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing ∧
      ¬ Bornology.IsBounded (face (chainUnion Γ 0 n) drawing x) :=
  h.outer_chain_of_crosscutExists hout h.crosscutExists

end IsPlaneChain

end Graph
