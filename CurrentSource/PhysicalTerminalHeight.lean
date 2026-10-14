import CurrentSource.TerminalCorners
import CurrentSource.HeightGreen
import FiniteAvalanches.Electrical.Physical.CurrentRegularStar
import FiniteAvalanches.Electrical.Physical.Undilated.Meaning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Electrical.Source.CurrentTerminalHeight
open LatticeProb StatementGeometry BSST Plane.SourceLattice LatticeDrawing SplitStep
open Plane.SourceLattice.CurrentRegularPhysical
open scoped Classical BigOperators
noncomputable section

/-- The actual alpha endpoint of the kth original copy is the prefix/suffix terminal.
Every original copy ID, including parallel copies, is retained by the split. -/
theorem actual_alpha_endpoint
    (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) {m : ℕ}
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (i : ℕ) (k : Fin m) :
    (if copyA D P marked (copies k).val = alpha D P then
      (actualSplit D P marked copies i).left (copies k).val else
      (actualSplit D P marked copies i).right (copies k).val) =
        .inr (decide (i ≤ k.val)) := by
  by_cases ha : copyA D P marked (copies k).val = alpha D P
  · rw [if_pos ha]
    change splitEndpoint (alpha D P)
      (boundarySide (copyA D P marked) (copyB D P marked) (alpha D P) copies i)
      (copyA D P marked (copies k).val) (copies k).val = _
    rw [splitEndpoint, dif_pos ha, boundarySide_copy]
  · rw [if_neg ha]
    have hb := (copies k).property.resolve_left ha
    change splitEndpoint (alpha D P)
      (boundarySide (copyA D P marked) (copyB D P marked) (alpha D P) copies i)
      (copyB D P marked (copies k).val) (copies k).val = _
    rw [splitEndpoint, dif_pos hb, boundarySide_copy]

/-- A retained copy incident to beta has zero actual source weight after every split. -/
theorem actual_beta_weight_zero
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ}
    (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P})
    (i : ℕ) (e : Copy D P marked)
    (he : copyA D P marked e = beta D P ∨ copyB D P marked e = beta D P) :
    (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i).left e)) *
      (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i).right e)) = 0 := by
  change (1 - Repair8.voltage D P hD marked
      (collapse (alpha D P) (splitEndpoint (alpha D P)
        (boundarySide _ _ _ copies i) (copyA D P marked e) e))) *
    (1 - Repair8.voltage D P hD marked
      (collapse (alpha D P) (splitEndpoint (alpha D P)
        (boundarySide _ _ _ copies i) (copyB D P marked e) e))) = 0
  rw [collapse_splitEndpoint, collapse_splitEndpoint]
  rcases he with he | he
  · rw [he, (Repair8.voltage_spec D P hD marked).2.1, sub_self, zero_mul]
  · rw [he, (Repair8.voltage_spec D P hD marked).2.1, sub_self, mul_zero]

/-- The current source drawing and path produce the global physical height and both
alpha corners at the selected half-current scale. Stream, balance, orientation,
terminal bounds and Green correspondence are conclusions of the body. -/
theorem original_source_height_terminal
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
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m))) :
    ∃ B : PlaneEmbedding (originalGraph D P marked),
    ∃ A : OuterArc B (alpha D P) (beta D P),
    ∃ faces : Face Q ≃ A.embedding.Face,
      (∀ e : Copy D P marked,
        faces ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
        faces ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e)) ∧
    ∃ psi : A.embedding.Face → ℝ,
      Source.stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi ∧
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      let H := fun F => sigma * (psi F - psi (faces (vertices (Fin.last m))))
      let J := sourceDeletedDualGraph D P marked Q charts
      let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
        FiniteAvalanches.External.finite_plane_dual_connected
        FiniteAvalanches.External.finite_plane_dual_bond_cycle
      let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
      (∀ F : Face Q, H (faces F) = -G (vertices 0) F) ∧
      ∀ (i : Fin (m + 1)) (j : Fin m), (j.val + 1 = i.val ∨ j.val = i.val) →
        let p := G (vertices 0) (vertices j.castSucc) - G (vertices 0) (vertices j.succ)
        let y0 := (H (faces (vertices j.castSucc)) + H (faces (vertices j.succ))) / 2
        0 < p / 2 ∧ p / 2 ≤ 1 / 2 ∧
        H (faces (vertices j.castSucc)) - y0 = -(p / 2) ∧
        H (faces (vertices j.succ)) - y0 = p / 2 ∧
        retainedPrimal D P marked (copies j).val ≠ markedPrimal D P marked ∧
        (∀ z : ℝ × ℝ, Geometry.angular (p / 2) y0 z =
          1 / 2 + ((2 / p) * (z.2 - y0)) /
            (2 * max 1 (max |(2 / p) * z.1| |(2 / p) * (z.2 - y0)|))) ∧
        ∀ k : Fin m, k ≠ j →
          (if copyA D P marked (copies k).val = alpha D P then
            (actualSplit D P marked copies i.val).left (copies k).val else
            (actualSplit D P marked copies i.val).right (copies k).val) =
              .inr (decide (i.val ≤ k.val)) ∧
          ∀ F : A.embedding.Face,
            (F = A.embedding.leftFace (.inl (copies k).val) ∨
              F = A.embedding.rightFace (.inl (copies k).val)) →
            (0, H F) ∈ Source.edgeSquare B (alpha D P) (beta D P) A
              (Repair8.voltage D P hD marked) H (copies k).val ∧
            (k.val < i.val → H F - y0 ≤ -(p / 2)) ∧
            (i.val ≤ k.val → p / 2 ≤ H F - y0) ∧
            Geometry.angular (p / 2) y0 (0, H F) = if k.val < i.val then 0 else 1 := by
  obtain ⟨B,A,faces,hfaces,_hmarkedSides,psi,hpsi,hstream,_hgauge,hbalance⟩ :=
    original_source_full_stream_balance_lovasz D P hD marked Q charts
  let J := sourceDeletedDualGraph D P marked Q charts
  let hc := source_deleted_dual_preconnected_of_classical D P hD hDc hP marked Q charts
    FiniteAvalanches.External.finite_plane_dual_connected
    FiniteAvalanches.External.finite_plane_dual_bond_cycle
  let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
  obtain ⟨sigma,hsigma,hheight⟩ := original_height_eq_neg_green D P hD marked Q charts
    (vertices 0) (vertices (Fin.last m)) hc hmarked (psi ∘ faces) hstream
    (hbalance (Repair8.voltage D P hD marked))
  refine ⟨B,A,faces,hfaces,psi,hpsi,sigma,hsigma,?_⟩
  intro H _J _hc _G
  have hH (F : Face Q) : H (faces F) = -G (vertices 0) F := hheight F
  refine ⟨hH,?_⟩
  let y := fun r : Fin (m + 1) => H (faces (vertices r))
  let p := fun k : Fin m => G (vertices 0) (vertices k.castSucc) - G (vertices 0) (vertices k.succ)
  have hp (k : Fin m) : 0 < p k ∧ p k ≤ 1 :=
    original_green_drop_pos_le_one D P hD hDc hP marked Q charts
      vertices hinj copies hends hmarked k
  have hstep (k : Fin m) : y k.succ - y k.castSucc = p k := by
    dsimp only [y,p]
    rw [hH,hH]
    ring
  intro i j hj _p y0
  refine ⟨half_pos (hp j).1,by linarith only [(hp j).2],?_,?_,
    retainedPrimal_ne_marked D P marked (copies j).val,?_,?_⟩
  · change y j.castSucc - (y j.castSucc + y j.succ) / 2 = -(p j / 2)
    linarith only [hstep j]
  · change y j.succ - (y j.castSucc + y j.succ) / 2 = p j / 2
    linarith only [hstep j]
  · exact Physical.Undilated.angular_half_current_eq_literal_scaled (p j) y0 (hp j).1
  · intro k hkj
    refine ⟨actual_alpha_endpoint D P marked copies i.val k,?_⟩
    intro F hF
    have hmem := incident_face_square_corner D P marked B A (Repair8.voltage D P hD marked)
      H (alpha D P) (copies k).val (copies k).property F
      ((physical_edgeFaces_iff D P marked B A (copies k).val F).mpr hF)
    rw [(Repair8.voltage_spec D P hD marked).1] at hmem
    refine ⟨hmem,?_⟩
    have hpair : F = faces (vertices k.castSucc) ∨ F = faces (vertices k.succ) := by
      rcases hF with rfl | rfl
      · rw [← (hfaces _).2]
        rcases hends k with ⟨_hl,hr⟩ | ⟨hr,_hl⟩
        · exact Or.inr (congrArg faces hr)
        · exact Or.inl (congrArg faces hr)
      · rw [← (hfaces _).1]
        rcases hends k with ⟨hl,_hr⟩ | ⟨_hr,hl⟩
        · exact Or.inl (congrArg faces hl)
        · exact Or.inr (congrArg faces hl)
    have hb := terminal_corner_bounds y p (fun r => (hp r).1.le) hstep i j hj k hkj
    have ha := terminal_corner_angular y p (fun r => (hp r).1) hstep i j hj k hkj
    rcases hpair with rfl | rfl
    · exact ⟨fun h => (hb.1 h).1,fun h => (hb.2 h).1,ha.1⟩
    · exact ⟨fun h => (hb.1 h).2,fun h => (hb.2 h).2,ha.2⟩

end
end FiniteAvalanches.Electrical.Source.CurrentTerminalHeight
