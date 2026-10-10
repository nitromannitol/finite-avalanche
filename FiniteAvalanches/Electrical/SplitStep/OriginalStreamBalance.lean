import FiniteAvalanches.Electrical.Plane.FaceBoundaryPullback
import FiniteAvalanches.Electrical.SplitStep.OriginalMarkedAuxiliary
import FiniteAvalanches.Electrical.Geometry.PolarStream
import FiniteAvalanches.External.TwoPoleTopology
import FiniteAvalanches.Electrical.SplitStep.OriginalSignedTrial

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open scoped Classical
noncomputable section

/-- The physical stream exists uniquely on each supplied original marked outer arc. -/
theorem original_physical_stream_existsUnique
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (B : PlaneEmbedding (originalGraph D P marked))
    (A : OuterArc B (alpha D P) (beta D P)) :
    ∃! psi : A.embedding.Face → ℝ,
      Source.stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi := by
  have h := Source.existsUnique_polar_stream (originalGraph D P marked) B
    (Repair8.graph_connected D P hD marked).preconnected
    (alpha D P) (beta D P) (by intro he; cases he) A
  rw [original_physical_voltage_eq D P hD marked] at h
  exact h

/-- Pull the signed physical current back along the supplied equivalence of all faces. -/
theorem original_stream_pullback_of_side_equations
    (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (faces : Face Q ≃ A.embedding.Face)
    (hfaces : ∀ e : Copy D P marked,
      faces ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
      faces ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e))
    (phi : Vertex D P → ℝ) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec B (alpha D P) (beta D P) A phi psi) :
    ∀ e : Copy D P marked,
      (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).right e) -
        (psi ∘ faces) ((sourceDeletedDualGraph D P marked Q charts).left e) =
      phi (copyA D P marked e) - phi (copyB D P marked e) := by
  intro e
  dsimp only [Function.comp_apply]
  rw [(hfaces e).1, (hfaces e).2]
  exact hpsi.1 e

/-- Under the explicit retained and marked side equations, the universal physical
boundary law holds on every original full-graph face for every vertex function. -/
theorem original_face_balance_of_side_equations
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
    ∀ (q : Vertex D P → ℝ) (F : Face Q),
      Plane.copyBoundary (sourceDualGraph D P Q charts).left (sourceDualGraph D P Q charts).right
        (Plane.copyGradient (LatticeDrawing.primalGraph D P).left (LatticeDrawing.primalGraph D P).right q) F = 0 := by
  obtain ⟨finiteFaces, _, _, _, hcycle⟩ := External.finite_plane_two_pole_topology
    (originalGraph D P marked) B (Repair8.graph_connected D P hD marked).preconnected
    (alpha D P) (beta D P) (by intro he; cases he) A
  let copies := (augmentedOriginalCopyEquiv D P marked).symm
  have he : ∀ e : LatticeDrawing.PrimalCopy D P,
      ((LatticeDrawing.primalGraph D P).left e = (augmentedGraph (originalGraph D P marked) (alpha D P) (beta D P)).left (copies e) ∧
        (LatticeDrawing.primalGraph D P).right e = (augmentedGraph (originalGraph D P marked) (alpha D P) (beta D P)).right (copies e) ∧
        faces ((sourceDualGraph D P Q charts).left e) = (augmentedDual A).left (copies e) ∧
        faces ((sourceDualGraph D P Q charts).right e) = (augmentedDual A).right (copies e)) ∨
      ((LatticeDrawing.primalGraph D P).left e = (augmentedGraph (originalGraph D P marked) (alpha D P) (beta D P)).right (copies e) ∧
        (LatticeDrawing.primalGraph D P).right e = (augmentedGraph (originalGraph D P marked) (alpha D P) (beta D P)).left (copies e) ∧
        faces ((sourceDualGraph D P Q charts).left e) = (augmentedDual A).right (copies e) ∧
        faces ((sourceDualGraph D P Q charts).right e) = (augmentedDual A).left (copies e)) := by
    intro e
    obtain ⟨z, rfl⟩ := (augmentedOriginalCopyEquiv D P marked).surjective e
    simp only [copies, Equiv.symm_apply_apply]
    cases z with
    | inl z => exact Or.inl ⟨rfl, rfl, (hfaces z).1, (hfaces z).2⟩
    | inr z =>
      cases z
      rcases marked.property with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · change (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P at ha
        change (LatticeDrawing.primalGraph D P).right (markedPrimal D P marked) = beta D P at hb
        rw [if_pos ha] at hmarked
        exact Or.inl ⟨ha, hb, hmarked.1, hmarked.2⟩
      · change (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = beta D P at hb
        change (LatticeDrawing.primalGraph D P).right (markedPrimal D P marked) = alpha D P at ha
        have hn : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) ≠ alpha D P := by
          rw [hb]; intro h; cases h
        rw [if_neg hn] at hmarked
        exact Or.inr ⟨hb, ha, hmarked.1, hmarked.2⟩
  intro q F
  rw [Plane.copyBoundary_gradient_transport_of_per_edge_equations copies faces
    (LatticeDrawing.primalGraph D P).left (LatticeDrawing.primalGraph D P).right
    (augmentedGraph (originalGraph D P marked) (alpha D P) (beta D P)).left
    (augmentedGraph (originalGraph D P marked) (alpha D P) (beta D P)).right
    (sourceDualGraph D P Q charts).left (sourceDualGraph D P Q charts).right
    (augmentedDual A).left (augmentedDual A).right he q F]
  exact hcycle q (faces F)

end
end FiniteAvalanches.Electrical.SplitStep
