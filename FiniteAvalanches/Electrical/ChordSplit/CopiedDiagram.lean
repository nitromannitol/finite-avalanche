import FiniteAvalanches.Electrical.Geometry.OrientedDrawing
import FiniteAvalanches.Electrical.SplitTerminal

/-! Copied split and contraction diagrams with retained loops and parallel IDs. -/

namespace FiniteAvalanches.Electrical.ChordSplit
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open scoped Classical
noncomputable section
variable {V E : Type}

/-- The existing split endpoints, with precisely the original E carrier. -/
def splitGraph (J : CopiedGraph V E) (alpha : V) (side : E → Bool) :
    CopiedGraph (SplitVertex alpha) E :=
  ⟨fun e => splitEndpoint alpha side (J.left e) e,
   fun e => splitEndpoint alpha side (J.right e) e⟩

/-- Normal forms after identifying alpha_0 with beta: all other vertices and
both Boolean tags remain explicit; false is the single identified ground. -/
abbrev GroundedSplitVertex (alpha beta : V) :=
  {v : V // v ≠ alpha ∧ v ≠ beta} ⊕ Bool

/-- Only beta and alpha_0 are identified. No edge IDs are changed. -/
def groundMap (alpha beta : V) : SplitVertex alpha → GroundedSplitVertex alpha beta
  | .inl x => if h : x.val = beta then .inr false else .inl ⟨x.val,x.property,h⟩
  | .inr k => .inr k

@[simp] theorem groundMap_alpha (alpha beta : V) (k : Bool) :
    groundMap alpha beta (.inr k) = .inr k := rfl

@[simp] theorem groundMap_beta (alpha beta : V) (hbeta : beta ≠ alpha) :
    groundMap alpha beta (.inl ⟨beta,hbeta⟩) = .inr false := by
  simp [groundMap]

/-- This is the split network with alpha_0 and beta identified, retaining E,
including the prefix copies which become loops. -/
def groundedSplitGraph (J : CopiedGraph V E) (alpha beta : V) (side : E → Bool) :
    CopiedGraph (GroundedSplitVertex alpha beta) E :=
  ⟨fun e => groundMap alpha beta ((splitGraph J alpha side).left e),
   fun e => groundMap alpha beta ((splitGraph J alpha side).right e)⟩

/-- Split H=H0+marked: the old marked edge is attached to alpha_0 and beta;
then insert the radial edge alpha_0--alpha_1. There are exactly TWO tagged IDs.
The outer tag denotes the radial edge, not the old marked edge. -/
def splitWithRadial (J : CopiedGraph V E) (alpha beta : V) (hbeta : beta ≠ alpha)
    (side : E → Bool) : CopiedGraph (SplitVertex alpha) ((E ⊕ Unit) ⊕ Unit) :=
  augmentedGraph
    (augmentedGraph (splitGraph J alpha side) (.inr false) (.inl ⟨beta,hbeta⟩))
    (.inr false) (.inr true)

/-- Contracting the radial edge and deleting ONLY its ID recovers the original
augmented primal H, on the identical E⊕Unit IDs and original orientations. -/
theorem contract_radial_recovers_augmented (J : CopiedGraph V E) (alpha beta : V)
    (hbeta : beta ≠ alpha) (side : E → Bool) (z : E ⊕ Unit) :
    collapse alpha ((splitWithRadial J alpha beta hbeta side).left (.inl z)) =
      (augmentedGraph J alpha beta).left z ∧
    collapse alpha ((splitWithRadial J alpha beta hbeta side).right (.inl z)) =
      (augmentedGraph J alpha beta).right z := by
  cases z with
  | inl e => exact ⟨collapse_splitEndpoint alpha side (J.left e) e,
      collapse_splitEndpoint alpha side (J.right e) e⟩
  | inr u => exact ⟨rfl,rfl⟩

/-- The retained-ID inclusion after deleting the OLD marked edge. -/
def afterMarkedDeletion : E ⊕ Unit → (E ⊕ Unit) ⊕ Unit
  | .inl e => .inl (.inl e)
  | .inr u => .inr u

/-- The old marked edge contracts to the single identified ground. -/
theorem marked_endpoints_identified (J : CopiedGraph V E) (alpha beta : V)
    (hbeta : beta ≠ alpha) (side : E → Bool) :
    groundMap alpha beta ((splitWithRadial J alpha beta hbeta side).left (.inl (.inr ()))) =
      (.inr false : GroundedSplitVertex alpha beta) ∧
    groundMap alpha beta ((splitWithRadial J alpha beta hbeta side).right (.inl (.inr ()))) =
      (.inr false : GroundedSplitVertex alpha beta) := by
  exact ⟨rfl,groundMap_beta alpha beta hbeta⟩

/-- Contracting the old marked edge and deleting ONLY its ID gives exactly the
identified split network PLUS the one radial ID, copy-by-copy. Every surviving original ID has its literal contracted endpoints. -/
theorem contract_marked_is_grounded_split_plus_radial
    (J : CopiedGraph V E) (alpha beta : V) (hbeta : beta ≠ alpha)
    (side : E → Bool) (z : E ⊕ Unit) :
    groundMap alpha beta ((splitWithRadial J alpha beta hbeta side).left
      (afterMarkedDeletion z)) =
      (augmentedGraph (groundedSplitGraph J alpha beta side) (.inr false) (.inr true)).left z ∧
    groundMap alpha beta ((splitWithRadial J alpha beta hbeta side).right
      (afterMarkedDeletion z)) =
      (augmentedGraph (groundedSplitGraph J alpha beta side) (.inr false) (.inr true)).right z := by
  cases z <;> exact ⟨rfl,rfl⟩

/-- Functions on the identified carrier pull back with exactly the same once-copy
energy. No positive-current assumption, loop deletion or denominator change occurs. -/
theorem identified_energy_pullback [Fintype E] (J : CopiedGraph V E) (alpha beta : V)
    (side : E → Bool) (f : GroundedSplitVertex alpha beta → ℝ) :
    energy (groundedSplitGraph J alpha beta side).left
      (groundedSplitGraph J alpha beta side).right f =
    energy (splitGraph J alpha side).left (splitGraph J alpha side).right
      (fun x => f (groundMap alpha beta x)) := rfl

/-- Three literal parallel copies, with a proper one-copy prefix. -/
def threeParallel : CopiedGraph Bool (Fin 3) := ⟨fun _ => false,fun _ => true⟩
def properSide (e : Fin 3) : Bool := decide (1 ≤ e.val)

/-- The prefix copy becomes a genuine retained loop. -/
theorem actual_retained_loop :
    (groundedSplitGraph threeParallel false true properSide).left 0 =
      (.inr false : GroundedSplitVertex false true) ∧
    (groundedSplitGraph threeParallel false true properSide).right 0 =
      (.inr false : GroundedSplitVertex false true) := by
  constructor <;> norm_num [groundedSplitGraph,splitGraph,splitEndpoint,groundMap,
    threeParallel,properSide]

/-- Distinct suffix IDs remain distinct parallel copies after the identification. -/
theorem actual_parallel_suffix :
    (groundedSplitGraph threeParallel false true properSide).left 1 = .inr true ∧
    (groundedSplitGraph threeParallel false true properSide).right 1 = .inr false ∧
    (groundedSplitGraph threeParallel false true properSide).left 2 = .inr true ∧
    (groundedSplitGraph threeParallel false true properSide).right 2 = .inr false := by
  norm_num [groundedSplitGraph,splitGraph,splitEndpoint,groundMap,threeParallel,properSide]

end
end FiniteAvalanches.Electrical.ChordSplit
