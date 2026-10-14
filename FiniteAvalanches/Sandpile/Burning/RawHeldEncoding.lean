import FiniteAvalanches.Sandpile.Burning.RawHeldClock
import FiniteAvalanches.Sandpile.Burning.HeldLayers

/-! Pointwise transport preserves every parallel step, graph, sink and held set. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

theorem raw_remainder_of_heights (h : Burning.SourceHeights G s)
    (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    rawParallelRemainder G s (fun x => ((h x).val : ℤ)) B n =
      Burning.heldParallelRemainder G s h B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rawParallelRemainder, Burning.heldParallelRemainder, ih]
    apply Finset.filter_congr
    intro x _
    exact or_congr Iff.rfl (by omega)

/-- NoFSC supplies NN and the unique degree-bounded encoding inside this application. -/
theorem source_clock_encoding (η : AllowedState G s)
    (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    sourceHeldParallelRemainder G s η.val B n =
      Burning.heldParallelRemainder G s (boundedHeights G s η) B n := by
  change rawParallelRemainder G s η.val.val B n = _
  have he : η.val.val = fun x => ((boundedHeights G s η x).val : ℤ) :=
    funext (fun x => (bounded_heights_value G s η x).symm)
  rw [he]
  exact raw_remainder_of_heights G s (boundedHeights G s η) B n

theorem source_terminal_eq_existing (η : AllowedState G s)
    (B : Finset (Burning.SourceVertex s)) :
    sourceHeldBurning G s η.val B =
      Burning.heldBurning G (Finset.univ.erase s) (boundedHeights G s η) B := by
  exact (source_clock_encoding G s η B (Fintype.card (Burning.SourceVertex s))).trans
    (Burning.held_parallel_final_eq G s (boundedHeights G s η) B)

/-- The field equivalence retains the entire integer field on its actual carrier. -/
theorem source_field_encoding_value (η : AllowedState G s) (x : Burning.SourceVertex s) :
    (((allowedFieldEquiv G s η).val x).val : ℤ) = η.val.val x :=
  bounded_heights_value G s η x

end
end FiniteAvalanches.Sandpile.RawGraph
