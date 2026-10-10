import FiniteAvalanches.Electrical.SplitStep.OriginalStreamBalanceWitness

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- The original marked face values retain the physical stream gauge, swapping precisely
when the original stored marked curve is reversed. Both retained and marked copies are covered. -/
theorem original_marked_stream_gauge_of_side_equations
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e)
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (faces : Face Q ≃ A.embedding.Face)
    (hfaces : ∀ e : Copy D P marked,
      faces ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
      faces ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e))
    (hmarked : if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
      faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.rightFace (.inr ()) ∧
      faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.leftFace (.inr ())
    else
      faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.leftFace (.inr ()) ∧
      faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.rightFace (.inr ()))
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi) :
    (∀ e : Copy D P marked,
      (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).right e) -
        (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).left e) =
      Repair8.voltage D P hD marked (copyA D P marked e) -
        Repair8.voltage D P hD marked (copyB D P marked e)) ∧
    (if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
      (psi ∘ faces) ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = 0 ∧
      (psi ∘ faces) ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) =
        Source.mass (originalGraph D P marked) (Repair8.voltage D P hD marked)
    else
      (psi ∘ faces) ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) =
        Source.mass (originalGraph D P marked) (Repair8.voltage D P hD marked) ∧
      (psi ∘ faces) ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = 0) := by
  refine ⟨original_stream_pullback_of_side_equations D P marked Q charts B A faces hfaces _ psi hpsi, ?_⟩
  by_cases ha : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P
  · rw [if_pos ha] at hmarked ⊢
    dsimp only [Function.comp_apply]
    rw [hmarked.1, hmarked.2]
    exact ⟨hpsi.2.2.1, hpsi.2.2.2⟩
  · rw [if_neg ha] at hmarked ⊢
    dsimp only [Function.comp_apply]
    rw [hmarked.1, hmarked.2]
    exact ⟨hpsi.2.2.2, hpsi.2.2.1⟩

end
end FiniteAvalanches.Electrical.SplitStep
