import CurrentSource.PhysicalHeightCanonical
import CurrentSource.GaugedMinimumSquares
import CurrentSource.MinimumTrialCharacterization
import CurrentSource.SplitCurrentScalar
import CurrentSource.SplitWeightedEnergy
import FiniteAvalanches.Electrical.SplitStep.OriginalSignedTrial
import ActualS7Consumer

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing ChordSplit Geometry
open FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
open FiniteAvalanches.Electrical.Source.CurrentTerminalHeight
open scoped Classical BigOperators
noncomputable section

/-- The current chosen minimum-face trial, with every geometric placement proved internally. -/
theorem current_whole_weighted_minimum_trial_of_original_cutoff :
∀ (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P),
  (∀ q : Plane → Plane, Continuous q →
    ∀ Q : Drawing (FiniteAvalanches.Electrical.LatticeDrawing.primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) →
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) →
      ∀ charts : ∀ e, EdgeChart Q e,
      ∀ finiteFaces : Fintype (Face Q),
        letI : Fintype (Face Q) := finiteFaces
        ∀ m : ℕ, ∀ vertices : Fin (m + 1) → Face Q,
          Function.Injective vertices →
          ∀ copies : Fin m ≃ {e : Copy D P marked //
            copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P},
            (∀ k : Fin m,
              ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
                (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
              ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
                (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) →
            (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
                (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
              ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
                (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) →
            let J := sourceDeletedDualGraph D P marked Q charts
            let hc := source_deleted_dual_preconnected_of_classical
              D P hD hDc hP marked Q charts
              @FiniteAvalanches.External.finite_plane_dual_connected
              @FiniteAvalanches.External.finite_plane_dual_bond_cycle
            let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
            ∀ R : Copy D P marked → Square,
              (∀ e, (R e).carrier = BSST.copiedSquare (originalGraph D P marked)
                (Repair8.voltage D P hD marked) (fun F => -G (vertices 0) F) J.left J.right e) →
              (∀ j : Fin m, ∀ hp : 0 < G (vertices 0) (vertices j.castSucc) - G (vertices 0) (vertices j.succ),
                (∑ e : Copy D P marked, ((R e).angularOsc
                  ((G (vertices 0) (vertices j.castSucc)-G (vertices 0) (vertices j.succ))/2)
                  (-(G (vertices 0) (vertices j.castSucc)+G (vertices 0) (vertices j.succ))/2)
                  1 (by norm_num) (by linarith only [hp]))^2) ≤
                    16*(1+Real.log (2/(G (vertices 0) (vertices j.castSucc)-G (vertices 0) (vertices j.succ))))) →
            ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
              ∀ j : Fin m, (j.val + 1 = i.val ∨ j.val = i.val) →
                ∃ f : SplitVertex (alpha D P) → ℝ,
                  f (.inr false) = 0 ∧ f (.inr true) = 1 ∧
                  weightedEnergy (actualSplit D P marked copies i.val).left
                    (actualSplit D P marked copies i.val).right
                    (fun x => 1 - splitVoltage D P hD marked x) f ≤
                  1 + 336 * (1 + Real.log
                    (2 / (G (vertices 0) (vertices j.castSucc) -
                      G (vertices 0) (vertices j.succ))))) := by
  intro D P hD hDc hP marked _q _hq Q _hpoint _hcurve charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends hmarked
  obtain ⟨B,A,faces,hfaces,psi,_hpsi,sigma,_hsigma,hglobal,hterminal⟩ :=
    source_height_terminal_canonical D P hD hDc hP marked Q charts
      vertices hinj copies hends hmarked
  let gauge := psi (faces (vertices (Fin.last m)))
  let H := fun F => sigma*(psi F-gauge)
  dsimp only
  intro R hR hcutoff i _hi0 _him j hj
  let J := sourceDeletedDualGraph D P marked Q charts
  let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
    FiniteAvalanches.External.finite_plane_dual_connected
    FiniteAvalanches.External.finite_plane_dual_bond_cycle
  let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
  let p := G (vertices 0) (vertices j.castSucc)-G (vertices 0) (vertices j.succ)
  let y0 := (H (faces (vertices j.castSucc))+H (faces (vertices j.succ)))/2
  let phi := Repair8.voltage D P hD marked
  let side := boundarySide (copyA D P marked) (copyB D P marked) (alpha D P) copies i.val
  let f := splitMinimumTrial D P marked B A phi H (p/2) y0
  have ht := hterminal i j hj
  change 0 < p/2 ∧ p/2 ≤ 1/2 ∧ _ at ht
  have hp : 0 < p := by linarith only [ht.1]
  have he : 0 < p/2 := ht.1
  have hheight (e : Copy D P marked) (hex : e ≠ (copies j).val)
      (healpha : copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P) :
      if side e then y0+p/2 ≤ max (H (A.embedding.leftFace (.inl e)))
        (H (A.embedding.rightFace (.inl e)))
      else min (H (A.embedding.leftFace (.inl e)))
        (H (A.embedding.rightFace (.inl e))) ≤ y0-p/2 := by
    obtain ⟨k,hk⟩ := copies.surjective ⟨e,healpha⟩
    have hke : (copies k).val = e := congrArg Subtype.val hk
    rw [← hke] at hex ⊢
    have hkj : k ≠ j := by intro h; apply hex; rw [h]
    have hkterm := (ht.2.2.2.2.2.2 k hkj).2
      (A.embedding.leftFace (.inl (copies k).val)) (Or.inl rfl)
    by_cases hik : i.val ≤ k.val
    · rw [show side (copies k).val = true from boundarySide_suffix _ _ _ copies i.val k hik]
      simp only [if_true]
      have hh := hkterm.2.2.1 hik
      change p/2 ≤ H (A.embedding.leftFace (.inl (copies k).val))-y0 at hh
      linarith only [hh,le_max_left (H (A.embedding.leftFace (.inl (copies k).val)))
        (H (A.embedding.rightFace (.inl (copies k).val)))]
    · have hki : k.val < i.val := Nat.lt_of_not_ge hik
      rw [show side (copies k).val = false from boundarySide_prefix _ _ _ copies i.val k hki]
      simp only [Bool.false_eq_true,if_false]
      have hh := hkterm.2.1 hki
      change H (A.embedding.leftFace (.inl (copies k).val))-y0 ≤ -(p/2) at hh
      linarith only [hh,min_le_left (H (A.embedding.leftFace (.inl (copies k).val)))
        (H (A.embedding.rightFace (.inl (copies k).val)))]
  have h21 := source_split_transfer21_of_terminal_corners D P marked hD B A H side
    (copies j).val (p/2) y0 he hheight
  have hH (F : Face Q) : H (faces F) = -G (vertices 0) F := hglobal F
  have hcenter : y0 = -(G (vertices 0) (vertices j.castSucc)+G (vertices 0) (vertices j.succ))/2 := by
    dsimp only [y0]
    rw [hH,hH]
    ring
  have hcarrier (e : Copy D P marked) :
      edgeSquare B (alpha D P) (beta D P) A phi H e = (R e).carrier := by
    rw [hR e]
    unfold edgeSquare BSST.copiedSquare
    rw [← (hfaces e).1,← (hfaces e).2,hH,hH]
    simp only [min_comm,max_comm]
    rfl
  have hosc (e : Copy D P marked) :
      edgeOsc D P marked B A phi H (p/2) y0 he e =
        (R e).angularOsc (p/2) y0 1 (by norm_num) he := by
    unfold edgeOsc Square.angularOsc Geometry.oscillation
    rw [Physical.Undilated.square_dilate_one,hcarrier]
  have h16 : (∑ e, (edgeOsc D P marked B A phi H (p/2) y0 he e)^2) ≤
      16*(1+Real.log (2/p)) := by
    simp only [hosc]
    rw [hcenter]
    exact hcutoff j hp
  have hweight : weightedEnergy (actualSplit D P marked copies i.val).left
      (actualSplit D P marked copies i.val).right (fun x => 1-splitVoltage D P hD marked x) f =
      ∑ e, (1-phi (copyA D P marked e))*(1-phi (copyB D P marked e))*
        (f (splitEndpoint (alpha D P) side (copyA D P marked e) e)-
          f (splitEndpoint (alpha D P) side (copyB D P marked e) e))^2 := by
    simp only [phi,side,weightedEnergy,actualSplit,splitGraph,originalGraph,splitVoltage,
      collapse_splitEndpoint]
  refine ⟨f,by simp [f,splitMinimumTrial],by simp [f,splitMinimumTrial],?_⟩
  dsimp only at h21
  let S := ∑ e, (edgeOsc D P marked B A phi H (p/2) y0 he e)^2
  have hs : S ≤ 16*(1+Real.log (2/p)) := h16
  have hw : weightedEnergy (actualSplit D P marked copies i.val).left
      (actualSplit D P marked copies i.val).right (fun x => 1-splitVoltage D P hD marked x) f ≤
      1+21*S := by
    rw [hweight]
    exact h21
  have hfinal : weightedEnergy (actualSplit D P marked copies i.val).left
      (actualSplit D P marked copies i.val).right (fun x => 1-splitVoltage D P hD marked x) f ≤
      1+336*(1+Real.log (2/p)) := by
    linarith only [hw,hs]
  exact hfinal


/-- The current chosen minimum-face trial, with every geometric placement proved internally. -/
theorem current_whole_weighted_minimum_trial :
∀ (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P),
  (∀ q : Plane → Plane, Continuous q →
    ∀ Q : Drawing (FiniteAvalanches.Electrical.LatticeDrawing.primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) →
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) →
      ∀ charts : ∀ e, EdgeChart Q e,
      ∀ finiteFaces : Fintype (Face Q),
        letI : Fintype (Face Q) := finiteFaces
        ∀ m : ℕ, ∀ vertices : Fin (m + 1) → Face Q,
          Function.Injective vertices →
          ∀ copies : Fin m ≃ {e : Copy D P marked //
            copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P},
            (∀ k : Fin m,
              ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
                (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
              ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
                (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) →
            (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
                (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
              ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
                (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) →
            let J := sourceDeletedDualGraph D P marked Q charts
            let hc := source_deleted_dual_preconnected_of_classical
              D P hD hDc hP marked Q charts
              @FiniteAvalanches.External.finite_plane_dual_connected
              @FiniteAvalanches.External.finite_plane_dual_bond_cycle
            let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
            ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
              ∀ j : Fin m, (j.val + 1 = i.val ∨ j.val = i.val) →
                ∃ f : SplitVertex (alpha D P) → ℝ,
                  f (.inr false) = 0 ∧ f (.inr true) = 1 ∧
                  weightedEnergy (actualSplit D P marked copies i.val).left
                    (actualSplit D P marked copies i.val).right
                    (fun x => 1 - splitVoltage D P hD marked x) f ≤
                  1 + 336 * (1 + Real.log
                    (2 / (G (vertices 0) (vertices j.castSucc) -
                      G (vertices 0) (vertices j.succ))))) := by
  intro D P hD hDc hP marked q hq Q hpoints hcurves charts finiteFaces
  letI : Fintype (Face Q) := finiteFaces
  intro m vertices hinj copies hends hmarked
  let J := sourceDeletedDualGraph D P marked Q charts
  let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
    FiniteAvalanches.External.finite_plane_dual_connected FiniteAvalanches.External.finite_plane_dual_bond_cycle
  let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
  obtain ⟨R,hcoords,_hd,_hcover,_hzero,hsum⟩ :=
    LovaszApplication.constructed_original_square_family D P hD marked Q charts
      (vertices 0) (vertices (Fin.last m)) hc hmarked
  apply current_whole_weighted_minimum_trial_of_original_cutoff D P hD hDc hP marked
    q hq Q hpoints hcurves charts finiteFaces m vertices hinj copies hends hmarked R
    (fun e => (hcoords e).2.2.2)
  intro j hp
  have hp1 := original_green_drop_pos_le_one D P hD hDc hP marked Q charts vertices hinj copies hends hmarked j
  have he : 0 < (G (vertices 0) (vertices j.castSucc)-G (vertices 0) (vertices j.succ))/2 := by linarith only [hp]
  have he1 : (G (vertices 0) (vertices j.castSucc)-G (vertices 0) (vertices j.succ))/2 ≤ 1 := by linarith only [hp1.2]
  simpa only [Source.CurrentSplit.log_inv_half_current] using hsum _ _ he he1

end
end FiniteAvalanches.Electrical.SplitStep
