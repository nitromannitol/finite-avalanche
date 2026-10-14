import OriginalStreamApplication

namespace FiniteAvalanches.Electrical.LovaszApplication
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing SplitStep
open LovaszStream
open scoped Classical BigOperators
noncomputable section

/-- The original marked sides are the same two physical poles, in either order. -/
theorem original_poles_order (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (v0 vm : Face Q)
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vm) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vm)) :
    (originalGroundFace D P marked Q charts = v0 ∧ originalSourceFace D P marked Q charts = vm) ∨
    (originalGroundFace D P marked Q charts = vm ∧ originalSourceFace D P marked Q charts = v0) := by
  by_cases ha : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P
  · simp only [originalGroundFace, originalSourceFace, if_pos ha]
    rcases hmarked with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  · simp only [originalGroundFace, originalSourceFace, if_neg ha]
    rcases hmarked with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl h

/-- Both original pole values are checked, without rescaling the face field. -/
theorem original_stream_pole_values (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (v0 vm : Face Q)
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vm) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vm)) :
    let eta := originalStream D P hD marked Q charts
    let M := mass (originalGraph D P marked) (Repair8.voltage D P hD marked)
    (eta v0 = 0 ∧ eta vm = M) ∨ (eta v0 = M ∧ eta vm = 0) := by
  dsimp only
  have hs := originalStream_spec D P hD marked Q charts
  rcases original_poles_order D P marked Q charts v0 vm hmarked with ⟨h0, hm⟩ | ⟨hm, h0⟩
  · exact Or.inl ⟨h0 ▸ hs.2.1, hm ▸ hs.2.2⟩
  · exact Or.inr ⟨h0 ▸ hs.2.2, hm ▸ hs.2.1⟩

/-- Unit dual injection and the primal mass agree through the proved endpoint
values. The only coordinate adjustment is a global sign and additive constant. -/
theorem constructed_original_green_normalization (D : Finset (Site 2)) (P : OneSet D)
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
    let G := groundedGreen J.left J.right vm hc v0
    let M := mass (originalGraph D P marked) (Repair8.voltage D P hD marked)
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      (∀ F : Face Q, sigma * (eta F - eta vm) = -G F) ∧ G v0 = M ∧ G vm = 0 ∧
      ((sigma = 1 ∧ eta v0 = 0 ∧ eta vm = M) ∨
        (sigma = -1 ∧ eta v0 = M ∧ eta vm = 0)) := by
  dsimp only
  let eta := originalStream D P hD marked Q charts
  let J := sourceDeletedDualGraph D P marked Q charts
  let G := groundedGreen J.left J.right vm hc v0
  let M := mass (originalGraph D P marked) (Repair8.voltage D P hD marked)
  obtain ⟨sigma, hsigma, hfield⟩ :=
    constructed_original_height_eq_neg_green D P hD marked Q charts v0 vm hc hmarked
  have hv := hfield v0
  change sigma * (eta v0 - eta vm) = -G v0 at hv
  have hnonneg : 0 ≤ G v0 := groundedGreen_diag_nonneg J.left J.right vm hc v0
  have hp := Repair8.voltage_spec D P hD marked
  have hM : 0 < M := Lovasz.mass_pos_of_normalized_boundary (originalGraph D P marked)
    (alpha D P) (beta D P) (Repair8.graph_connected D P hD marked).preconnected
    (Repair8.voltage D P hD marked) hp.1 hp.2.1
  have hground : G vm = 0 := groundedGreen_ground J.left J.right vm hc v0
  have hpoles := original_stream_pole_values D P hD marked Q charts v0 vm hmarked
  change (eta v0 = 0 ∧ eta vm = M) ∨ (eta v0 = M ∧ eta vm = 0) at hpoles
  refine ⟨sigma, hsigma, hfield, ?_⟩
  rcases hsigma with hs | hs <;> rcases hpoles with ⟨h0, hm⟩ | ⟨h0, hm⟩
  · rw [hs, h0, hm] at hv
    exact ⟨by linarith only [hv], hground, Or.inl ⟨hs, h0, hm⟩⟩
  · rw [hs, h0, hm] at hv
    linarith only [hv, hnonneg, hM]
  · rw [hs, h0, hm] at hv
    linarith only [hv, hnonneg, hM]
  · rw [hs, h0, hm] at hv
    exact ⟨by linarith only [hv], hground, Or.inr ⟨hs, h0, hm⟩⟩

end
end FiniteAvalanches.Electrical.LovaszApplication

#print axioms FiniteAvalanches.Electrical.LovaszApplication.original_poles_order
#print axioms FiniteAvalanches.Electrical.LovaszApplication.original_stream_pole_values
#print axioms FiniteAvalanches.Electrical.LovaszApplication.constructed_original_green_normalization
