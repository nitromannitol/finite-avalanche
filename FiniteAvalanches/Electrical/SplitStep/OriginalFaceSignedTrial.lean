import FiniteAvalanches.Electrical.SplitStep.OriginalSignedTrial
import FiniteAvalanches.Electrical.SplitStep.OriginalTerminalValues

/-! Conditional consumption on all original supplied faces. The face transport and
alpha-indicator balance remain explicit geometry obligations, never source closure. -/
namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing PhysicalCharging
open scoped Classical BigOperators
noncomputable section

/-- Given the ordinary physical transport and original indicator balance, one sign works
for every proper split and EACH adjacent j. All original faces and copy IDs are retained. -/
theorem original_physical_trial_of_face_transport_and_balance
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (Q : Drawing (LatticeDrawing.primalGraph D P))
    (charts : ∀ e, EdgeChart Q e) [finiteFaces : Fintype (Face Q)] {m : ℕ}
    (vertices : Fin (m + 1) → Face Q) (hinj : Function.Injective vertices)
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (hends : ∀ k : Fin m,
      ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
      ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
        (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ))
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m)))
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (faces : Face Q ≃ A.embedding.Face)
    (hfaces : ∀ e : Copy D P marked,
      faces ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
      faces ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e))
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi)
    (hbalance : ∀ F : Face Q,
      Plane.copyBoundary (sourceDualGraph D P Q charts).left (sourceDualGraph D P Q charts).right
        (Plane.copyGradient (LatticeDrawing.primalGraph D P).left (LatticeDrawing.primalGraph D P).right
          (fun x => if x = alpha D P then (1 : ℝ) else 0)) F = 0) :
    let J := sourceDeletedDualGraph D P marked Q charts
    let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
      FiniteAvalanches.External.finite_plane_dual_connected FiniteAvalanches.External.finite_plane_dual_bond_cycle
    let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ (i : Fin (m + 1)), 0 < i.val → i.val < m →
        ∀ (j : Fin m), (j.val + 1 = i.val ∨ j.val = i.val) →
          let p := G (vertices 0) (vertices j.castSucc) - G (vertices 0) (vertices j.succ)
          let y0 := (psi (faces (vertices j.castSucc)) + psi (faces (vertices j.succ))) / 2
          let f := signedSplitMidpointTrial (originalGraph D P marked) B (alpha D P) (beta D P) A
            (Repair8.voltage D P hD marked) psi sigma (p / 2) y0
          f (.inr false) = 0 ∧ f (.inr true) = 1 ∧
            f (.inl ⟨beta D P, by intro h; cases h⟩) = 0 ∧ (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧
            weightedEnergy (actualSplit D P marked copies i.val).left
              (actualSplit D P marked copies i.val).right
              (fun v => 1 - splitVoltage D P hD marked v) f ≤
                1 + 3888 * (1 + Real.log (2 / p)) := by
  intro J hc G
  let eta : Face Q → ℝ := fun F => psi (faces F)
  have hstream : ∀ e : Copy D P marked,
      eta ((sourceDeletedDualGraph D P marked Q charts).right e) -
        eta ((sourceDeletedDualGraph D P marked Q charts).left e) =
      Repair8.voltage D P hD marked (copyA D P marked e) -
        Repair8.voltage D P hD marked (copyB D P marked e) := by
    intro e
    dsimp only [eta]
    rw [(hfaces e).2, (hfaces e).1]
    exact hpsi.1 e
  have hphysicalEnds : ∀ k : Fin m,
      (A.embedding.leftFace (.inl (copies k).val) = faces (vertices k.castSucc) ∧
        A.embedding.rightFace (.inl (copies k).val) = faces (vertices k.succ)) ∨
      (A.embedding.rightFace (.inl (copies k).val) = faces (vertices k.castSucc) ∧
        A.embedding.leftFace (.inl (copies k).val) = faces (vertices k.succ)) := by
    intro k
    rcases hends k with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact Or.inr ⟨(hfaces _).1.symm.trans (congrArg faces hl),
        (hfaces _).2.symm.trans (congrArg faces hr)⟩
    · exact Or.inl ⟨(hfaces _).2.symm.trans (congrArg faces hr),
        (hfaces _).1.symm.trans (congrArg faces hl)⟩
  by_cases hm : 0 < m
  · obtain ⟨sigma, hsigma, hgreen, _⟩ := original_terminal_values_of_stream_and_balance
      D P hD hDc hP marked Q charts vertices hinj copies hends hmarked hm hbalance eta hstream
    refine ⟨sigma, hsigma, ?_⟩
    intro i _hi0 _him j hj
    have hsteps : ∀ k : Fin m,
        sigma * (psi (faces (vertices k.succ)) - psi (faces (vertices k.castSucc))) =
          Repair8.voltage D P hD marked (if copyA D P marked (copies k).val = alpha D P
            then copyB D P marked (copies k).val else copyA D P marked (copies k).val) := by
      intro k
      exact (hgreen k).trans (original_boundary_voltage_eq_green_drop D P hD hDc hP marked Q charts
        vertices hinj copies hends hmarked k).symm
    have h := original_physical_signed_trial_of_boundary_steps D P hD marked B A psi hpsi
      (faces ∘ vertices) copies hphysicalEnds sigma hsigma hsteps i j hj
    dsimp only
    rw [← original_boundary_voltage_eq_green_drop D P hD hDc hP marked Q charts
      vertices hinj copies hends hmarked j]
    exact h
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro i hi0 him
    omega

end
end FiniteAvalanches.Electrical.SplitStep
