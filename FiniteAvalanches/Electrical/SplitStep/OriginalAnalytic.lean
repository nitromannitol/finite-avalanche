import FiniteAvalanches.Electrical.SplitStep.ActualConnectivity
import FiniteAvalanches.Electrical.SplitStep.OriginalCurrent

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing
open FiniteAvalanches.Electrical.ChordSplit
open scoped Classical BigOperators
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D)
  (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
  (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
  (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
  (marked : MarkedCopy D P) (Q : Drawing (primalGraph D P))
  (charts : ∀ e, EdgeChart Q e) [finiteFaces : Fintype (Face Q)]
  {m : ℕ} (vertices : Fin (m + 1) → Face Q) (hinj : Function.Injective vertices)
  (copies : Fin m ≃ {e : Copy D P marked //
    copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
  (hpath : ∀ k : Fin m,
    ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
      (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
    ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
      (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ))
  (hmarked :
    ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
      (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
    ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
      (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m)))

include hinj hpath hmarked

/-- The closed analytic reduction on every supplied original drawing, full face carrier,
and full boundary order. The diagonal Green/total-response identification is separate. -/
theorem original_split_analytic (i : Fin (m + 1)) (hi0 : 0 < i.val) (him : i.val < m) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      @FiniteAvalanches.External.finite_plane_dual_connected
      @FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
    (supportGraph (actualSplit D P marked copies i.val).left
      (actualSplit D P marked copies i.val).right).Connected ∧
    (let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
        (boundarySide _ _ _ copies i.val);
      effectiveConductance K (.inr false) (.inr true) (grounded_terminals_ne D P)
        (actual_grounded_preconnected D P hD marked copies i.val hi0 him) =
          totalResponse D P hD marked copies i.val) ∧
    (-laplacian (actualSplit D P marked copies i.val).left
      (actualSplit D P marked copies i.val).right (splitVoltage D P hD marked) (.inr true) =
      G (vertices 0) (vertices i)) ∧
    ∀ f : SplitVertex (alpha D P) → ℝ, f (.inr false) = 0 → f (.inr true) = 1 →
      energy (actualSplit D P marked copies i.val).left
        (actualSplit D P marked copies i.val).right
        (fun x => (1 - splitVoltage D P hD marked x) * f x) =
        G (vertices 0) (vertices i) +
          weightedEnergy (actualSplit D P marked copies i.val).left
            (actualSplit D P marked copies i.val).right
            (fun x => 1 - splitVoltage D P hD marked x) f ∧
      totalResponse D P hD marked copies i.val - G (vertices 0) (vertices i) ≤
        ∑ e : Copy D P marked,
          (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i.val).left e)) *
          (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i.val).right e)) *
          (f ((actualSplit D P marked copies i.val).left e) -
            f ((actualSplit D P marked copies i.val).right e)) ^ 2 := by
  dsimp only
  refine ⟨actual_split_connected D P hD marked copies i.val hi0 him,
    actual_conductance_eq_totalResponse D P hD marked copies i.val hi0 him,
    actual_split_inflow_eq_original_green D P hD hDc hP marked Q charts
      vertices hinj copies hpath hmarked i, ?_⟩
  intro f hf0 hf1
  constructor
  · rw [actual_suffixCurrent_eq_original_green D P hD hDc hP marked Q charts
      vertices hinj copies hpath hmarked i]
    exact actual_split_ground_energy D P hD marked copies i.val f hf0 hf1
  · exact actual_split_response_sub_original_green_bound D P hD hDc hP marked Q charts
      vertices hinj copies hpath hmarked i f hf0 hf1

end
end FiniteAvalanches.Electrical.SplitStep
