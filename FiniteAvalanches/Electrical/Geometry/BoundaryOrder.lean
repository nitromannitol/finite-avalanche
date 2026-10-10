import FiniteAvalanches.Electrical.Geometry.DiskDrawing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.GroupTheory.Perm.Basic

/-! Literal boundary-angle order and finite crossing predicates.
Exact declaration bodies extracted from the independently checked private support;
this module constructs no boundary angles from a drawing. -/
namespace FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical BigOperators
noncomputable section

/-- The six specified points occur counterclockwise on the actual unit circle. -/
def cyclic_order {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (drawing : Drawing J) (x : Fin 6 → V) : Prop :=
  ∃ θ : Fin 6 → ℝ, StrictMono θ ∧ θ 5 < θ 0 + 2 * Real.pi ∧
    ∀ i, drawing.point (x i) = (Real.cos (θ i),Real.sin (θ i))
end
end FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical

/-- Two chords cross exactly when their endpoints alternate in the cyclic order. -/
def chords_cross (a b c d : Fin 6) : Prop :=
  (min a b < min c d ∧ min c d < max a b ∧ max a b < max c d) ∨
  (min c d < min a b ∧ min a b < max c d ∧ max c d < max a b)

/-- A bijection between two ordered triples gives three chords, none of which cross. -/
def triple_noncrossing (U W : Fin 3 → Fin 6) (p : Equiv.Perm (Fin 3)) : Prop :=
  ∀ i j, i ≠ j → ¬chords_cross (U i) (W (p i)) (U j) (W (p j))
end FiniteAvalanches.Electrical
