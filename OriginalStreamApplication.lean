import OriginalStreamExistence
import PrimitiveHeightGreen
import FiniteAvalanches.Electrical.Lovasz.PhysicalBounds
import FiniteAvalanches.Electrical.Green.Current
import FiniteAvalanches.Electrical.Green.Voltage

/-! The constructed stream, original copied face dictionary, and actual unit
Green characterization are consumed on one common physical witness. -/

namespace FiniteAvalanches.Electrical.LovaszApplication
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing SplitStep
open LovaszStream Source.CurrentTerminalHeight
open scoped Classical BigOperators
noncomputable section

/-- The ready noncircular constructor supplies one normalized physical field,
the same original field, all original side equations, and full face balance. -/
theorem original_stream_tiling_witness (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e) :
    ∃ B : PlaneEmbedding (originalGraph D P marked),
    ∃ A : OuterArc B (alpha D P) (beta D P),
    ∃ faces : Face Q ≃ A.embedding.Face,
      (∀ e : Copy D P marked,
        faces ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
        faces ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e)) ∧
      (if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
        faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.rightFace (.inr ()) ∧
        faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.leftFace (.inr ())
      else
        faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.leftFace (.inr ()) ∧
        faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.rightFace (.inr ())) ∧
    ∃ psi : A.embedding.Face → ℝ,
      stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi ∧
      originalStream D P hD marked Q charts = psi ∘ faces ∧
      (∀ (q : Vertex D P → ℝ) (F : Face Q),
        Plane.copyBoundary (sourceDualGraph D P Q charts).left (sourceDualGraph D P Q charts).right
          (Plane.copyGradient (LatticeDrawing.primalGraph D P).left
            (LatticeDrawing.primalGraph D P).right q) F = 0) ∧
      (∀ F, 0 ≤ psi F ∧ psi F ≤ mass (originalGraph D P marked) (Repair8.voltage D P hD marked)) ∧
      (∀ e f : Copy D P marked, e ≠ f → Disjoint
        (interior (edgeSquare B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi e))
        (interior (edgeSquare B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi f))) ∧
      (⋃ e : Copy D P marked,
        edgeSquare B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi e) =
        Set.Icc 0 1 ×ˢ Set.Icc 0 (mass (originalGraph D P marked) (Repair8.voltage D P hD marked)) := by
  obtain ⟨B, A, faces, hfaces, hmarked⟩ := original_marked_physical_geometry D P marked Q charts
  have hp := Repair8.voltage_spec D P hD marked
  let psi := physicalStream (originalGraph D P marked) B
    (Repair8.graph_connected D P hD marked).preconnected (alpha D P) (beta D P)
    (by intro h; cases h) A (Repair8.voltage D P hD marked) hp.1 hp.2.1 hp.2.2
  have hpsi := physicalStream_spec (originalGraph D P marked) B
    (Repair8.graph_connected D P hD marked).preconnected (alpha D P) (beta D P)
    (by intro h; cases h) A (Repair8.voltage D P hD marked) hp.1 hp.2.1 hp.2.2
  obtain ⟨hg, hs⟩ := original_poles_map D P marked Q charts B A faces hmarked
  have hspec : originalStreamSpec D P hD marked Q charts (psi ∘ faces) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e
      simp only [Function.comp_apply, (hfaces e).1, (hfaces e).2]
      exact hpsi.1 e
    · change psi (faces (originalGroundFace D P marked Q charts)) = 0
      rw [hg]
      exact hpsi.2.2.1
    · change psi (faces (originalSourceFace D P marked Q charts)) = _
      rw [hs]
      exact hpsi.2.2.2
  refine ⟨B, A, faces, hfaces, hmarked, psi, hpsi,
    (originalStream_unique D P hD marked Q charts _ hspec).symm, ?_, ?_⟩
  · exact original_face_balance_of_side_equations D P hD marked Q charts B A faces hfaces hmarked
  · exact Lovasz.physical_tiling_of_stream (originalGraph D P marked) B
      (Repair8.graph_connected D P hD marked).preconnected (alpha D P) (beta D P)
      (by intro h; cases h) A (Repair8.voltage D P hD marked) hp.1 hp.2.1 hp.2.2 psi hpsi

/-- The global signed/gauged original field is the negative actual Green row,
proved by the full copied Laplacian and unique grounded Poisson characterization. -/
theorem constructed_original_height_eq_neg_green (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    [Fintype (Face Q)] (v0 vm : Face Q)
    (hc : (supportGraph (sourceDeletedDualGraph D P marked Q charts).left
      (sourceDeletedDualGraph D P marked Q charts).right).Preconnected)
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vm) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vm)) :
    let eta := originalStream D P hD marked Q charts
    let J := sourceDeletedDualGraph D P marked Q charts
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ F : Face Q, sigma * (eta F - eta vm) = -groundedGreen J.left J.right vm hc v0 F := by
  obtain ⟨B, A, faces, hfaces, _hmarkedSides, psi, _hpsi, _heq, hbalance, _⟩ :=
    original_stream_tiling_witness D P hD marked Q charts
  exact original_height_eq_neg_green D P hD marked Q charts v0 vm hc hmarked
    (originalStream D P hD marked Q charts) (originalStream_spec D P hD marked Q charts).1
    (hbalance (Repair8.voltage D P hD marked))

/-- The current Green row has unit injection, not mass injection. Ground removal
is exactly minus one, independently of the original primal battery current. -/
theorem original_green_unit_laplacian (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) [Fintype (Face Q)] (v0 vm : Face Q)
    (hc : (supportGraph (sourceDeletedDualGraph D P marked Q charts).left
      (sourceDeletedDualGraph D P marked Q charts).right).Preconnected)
    (hne : v0 ≠ vm) (F : Face Q) :
    let J := sourceDeletedDualGraph D P marked Q charts
    laplacian J.left J.right (groundedGreen J.left J.right vm hc v0) F =
      (if F = v0 then 1 else 0) - (if F = vm then 1 else 0) := by
  dsimp only
  by_cases hF : F = vm
  · subst F
    rw [groundedGreen_laplacian_ground _ _ vm hc v0 hne, if_neg hne.symm, if_pos rfl]
    norm_num
  · rw [groundedGreen_laplacian _ _ vm hc v0 F hF, if_neg hF, sub_zero]

end
end FiniteAvalanches.Electrical.LovaszApplication

#print axioms FiniteAvalanches.Electrical.LovaszApplication.original_stream_tiling_witness
#print axioms FiniteAvalanches.Electrical.LovaszApplication.constructed_original_height_eq_neg_green
#print axioms FiniteAvalanches.Electrical.LovaszApplication.original_green_unit_laplacian
