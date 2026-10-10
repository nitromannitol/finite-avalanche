import FiniteAvalanches.Electrical.SplitStep.SignedBoundaryTrial
import FiniteAvalanches.Electrical.SplitStep.BoundaryPositive

/-! The physical trial on the literal original lattice copy and split carriers.
The original-face transport and boundary-step construction are separate conditional inputs. -/
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing PhysicalCharging
open scoped Classical BigOperators
noncomputable section

/-- Unique source voltages agree on the entire original vertex carrier. -/
theorem original_physical_voltage_eq (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P) :
    Source.voltage (originalGraph D P marked) (alpha D P) (beta D P)
        (Repair8.graph_connected D P hD marked).preconnected = Repair8.voltage D P hD marked :=
  Repair8.voltage_unique D P hD marked _
    (Source.voltage_spec _ _ _ (by intro h; cases h) _)

/-- Every alpha copy has exactly its positive original opposite-endpoint current as its side. -/
theorem original_alpha_abs_current_eq (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (e : {e : Copy D P marked // copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) :
    |Repair8.voltage D P hD marked (copyA D P marked e.val) -
        Repair8.voltage D P hD marked (copyB D P marked e.val)| =
      Repair8.voltage D P hD marked (if copyA D P marked e.val = alpha D P
        then copyB D P marked e.val else copyA D P marked e.val) := by
  have hp := boundary_voltage_pos_le_one D P hD marked e
  have ha := (Repair8.voltage_spec D P hD marked).1
  by_cases hl : copyA D P marked e.val = alpha D P
  · rw [if_pos hl] at hp ⊢
    rw [hl, ha, zero_sub, abs_neg, abs_of_pos hp.1]
  · have hr := e.property.resolve_left hl
    rw [if_neg hl] at hp ⊢
    rw [hr, ha, sub_zero, abs_of_pos hp.1]

/-- Sharp signed trial for each adjacent j on the original H0 copies and actualSplit.
The complete physical face order and coherent signed increments are ordinary conditional
geometry data; degree four and strict positivity are proved from the original lattice source. -/
theorem original_physical_signed_trial_of_boundary_steps
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi)
    {m : ℕ} (vertices : Fin (m + 1) → A.embedding.Face)
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (hends : ∀ k : Fin m,
      (A.embedding.leftFace (.inl (copies k).val) = vertices k.castSucc ∧
        A.embedding.rightFace (.inl (copies k).val) = vertices k.succ) ∨
      (A.embedding.rightFace (.inl (copies k).val) = vertices k.castSucc ∧
        A.embedding.leftFace (.inl (copies k).val) = vertices k.succ))
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (hstep : ∀ k : Fin m,
      sigma * (psi (vertices k.succ) - psi (vertices k.castSucc)) =
        Repair8.voltage D P hD marked (if copyA D P marked (copies k).val = alpha D P
          then copyB D P marked (copies k).val else copyA D P marked (copies k).val))
    (i : Fin (m + 1)) (j : Fin m) (hj : j.val + 1 = i.val ∨ j.val = i.val) :
    let p := Repair8.voltage D P hD marked (if copyA D P marked (copies j).val = alpha D P
      then copyB D P marked (copies j).val else copyA D P marked (copies j).val)
    let y0 := (psi (vertices j.castSucc) + psi (vertices j.succ)) / 2
    let f := signedSplitMidpointTrial (originalGraph D P marked) B (alpha D P) (beta D P) A
      (Repair8.voltage D P hD marked) psi sigma (p / 2) y0
    f (.inr false) = 0 ∧ f (.inr true) = 1 ∧
      f (.inl ⟨beta D P, by intro h; cases h⟩) = 0 ∧ (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧
      weightedEnergy (actualSplit D P marked copies i.val).left
        (actualSplit D P marked copies i.val).right (fun v => 1 - splitVoltage D P hD marked v) f ≤
          1 + 3888 * (1 + Real.log (2 / p)) := by
  intro p y0 f
  let J := originalGraph D P marked
  let hc := (Repair8.graph_connected D P hD marked).preconnected
  have hv := original_physical_voltage_eq D P hD marked
  have hpj : 0 < |Source.voltage J (alpha D P) (beta D P) hc (J.left (copies j).val) -
      Source.voltage J (alpha D P) (beta D P) hc (J.right (copies j).val)| := by
    rw [hv]
    change 0 < |Repair8.voltage D P hD marked (copyA D P marked (copies j).val) -
      Repair8.voltage D P hD marked (copyB D P marked (copies j).val)|
    rw [original_alpha_abs_current_eq D P hD marked (copies j)]
    exact (boundary_voltage_pos_le_one D P hD marked (copies j)).1
  have hps : Source.stream_spec B (alpha D P) (beta D P) A
      (Source.voltage J (alpha D P) (beta D P) hc) psi := by rw [hv]; exact hpsi
  have hsteps : ∀ k : Fin m,
      sigma * (psi (vertices k.succ) - psi (vertices k.castSucc)) =
        |Source.voltage J (alpha D P) (beta D P) hc (J.left (copies k).val) -
          Source.voltage J (alpha D P) (beta D P) hc (J.right (copies k).val)| := by
    intro k
    rw [hv]
    exact (hstep k).trans (original_alpha_abs_current_eq D P hD marked (copies k)).symm
  let copiesJ : Fin m ≃ {e : Copy D P marked // J.left e = alpha D P ∨ J.right e = alpha D P} := copies
  have h := physical_signed_trial_le_3888_of_boundary_steps J B hc
    (alpha D P) (beta D P) (by intro h; cases h) A psi hps (source_free_degree_bound D P marked)
    vertices copiesJ hends sigma hsigma hsteps i j hj hpj
  dsimp only at h
  rw [hv] at h
  have hcur : |Repair8.voltage D P hD marked (J.left (copiesJ j).val) -
      Repair8.voltage D P hD marked (J.right (copiesJ j).val)| = p :=
    original_alpha_abs_current_eq D P hD marked (copies j)
  rw [hcur] at h
  exact h

end
end FiniteAvalanches.Electrical.SplitStep
