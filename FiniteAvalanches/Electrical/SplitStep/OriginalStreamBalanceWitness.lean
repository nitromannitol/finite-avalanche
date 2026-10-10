import FiniteAvalanches.Electrical.SplitStep.OriginalStreamBalance

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- The ordinary pullback constructs both missing electrical inputs on the supplied full face carrier.
Retained and marked side equations remain explicit geometric premises. -/
theorem original_stream_and_balance_of_side_equations
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
      faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.rightFace (.inr ())) :
    ∃ psi : A.embedding.Face → ℝ,
      Source.stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi ∧
      (∀ e : Copy D P marked,
        (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).right e) -
          (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).left e) =
        Repair8.voltage D P hD marked (copyA D P marked e) -
          Repair8.voltage D P hD marked (copyB D P marked e)) ∧
      ∀ (q : Vertex D P → ℝ) (F : Face Q),
        Plane.copyBoundary (sourceDualGraph D P Q charts).left (sourceDualGraph D P Q charts).right
          (Plane.copyGradient (LatticeDrawing.primalGraph D P).left (LatticeDrawing.primalGraph D P).right q) F = 0 := by
  obtain ⟨psi, hpsi, _⟩ := original_physical_stream_existsUnique D P hD marked B A
  exact ⟨psi, hpsi,
    original_stream_pullback_of_side_equations D P marked Q charts B A faces hfaces _ psi hpsi,
    original_face_balance_of_side_equations D P hD marked Q charts B A faces hfaces hmarked⟩

end
end FiniteAvalanches.Electrical.SplitStep
