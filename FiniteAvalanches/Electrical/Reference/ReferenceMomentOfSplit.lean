import FiniteAvalanches.Electrical.Source.ArcVariance
import FiniteAvalanches.Electrical.Reference.FirstMoment
import FiniteAvalanches.Electrical.Reference.BoundaryCardinality
import FiniteAvalanches.Electrical.Reference.PathProbabilities
import FiniteAvalanches.Electrical.Reference.SplitVarianceAssembly

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Source.Reference
open LatticeProb
open FiniteAvalanches.Electrical.LatticeDrawing
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical BigOperators
noncomputable section

/-- The complete source reference conclusion conditional only on the complete
closed split proposition, on all compatible original geometries. -/
theorem reference_moment_of_split (hsplit :
  ∀ (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P),
  (∃ q : Plane → Plane, Continuous q ∧
    ∃ Q : Drawing (FiniteAvalanches.Electrical.LatticeDrawing.primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) ∧
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) ∧
      ∃ charts : ∀ e, EdgeChart Q e,
      ∃ _finiteFaces : Fintype (Face Q),
      ∃ m : ℕ, ∃ vertices : Fin (m + 1) → Face Q,
        Function.Injective vertices ∧
        ∃ copies : Fin m ≃ {e : Copy D P marked //
          copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P},
          (∀ k : Fin m,
            ((sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.castSucc ∧
              (sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.succ) ∨
            ((sourceDeletedDualGraph D P marked Q charts).right (copies k).val = vertices k.castSucc ∧
              (sourceDeletedDualGraph D P marked Q charts).left (copies k).val = vertices k.succ)) ∧
          (((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices (Fin.last m)) ∨
            ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vertices 0 ∧
              (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vertices (Fin.last m)))) ∧
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
              FiniteAvalanches.External.finite_plane_dual_connected
              FiniteAvalanches.External.finite_plane_dual_bond_cycle
            let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
            ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
              ∀ j : Fin m, (j.val + 1 = i.val ∨ j.val = i.val) →
                G (vertices i) (vertices i) - G (vertices 0) (vertices i) ≤
                  1 + 3888 * (1 + Real.log
                    (2 / (G (vertices 0) (vertices j.castSucc) -
                      G (vertices 0) (vertices j.succ)))))) :
    ∃ C : ℝ, ∀ (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (_hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (_hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P),
    let a := copyA D P marked
    let b := copyB D P marked
    let J := StatementTypes.graph D P marked
    let F := J.RootedForest ({alpha D P, beta D P} : Set (Vertex D P))
    letI : Nonempty F := Repair8.forest_nonempty D P hD marked
    let phi := Repair8.voltage D P hD marked
    let Y : F → ℝ := fun f => ∑ z : Plane.Dart (Copy D P marked),
      if Plane.tail a b z = alpha D P ∧ J.reaches f.val (Plane.head a b z) (beta D P)
      then 1 else 0
    let mean := (∑ f : F, Y f)/(Fintype.card F : ℝ)
    let variance := (∑ f : F, (Y f-mean)^2)/(Fintype.card F : ℝ)
    let M := energy a b phi
    let m := ((domainCopies D).filter fun e =>
      (originalA e ∈ D ∧ originalB e ∉ D) ∨ (originalB e ∈ D ∧ originalA e ∉ D)).card-1
    mean = M ∧ variance ≤ C*mean*(1+Real.log ((m : ℝ) / mean)) := by
  refine ⟨40000, ?_⟩
  intro D P hD hDc hP marked a b J0 F phi Y mean variance M boundaryCount
  have hmean : mean = ReferenceMoment.forestMean D P marked := rfl
  have henergy : mean = M := ReferenceMoment.mean_eq_energy D P marked hD
  refine ⟨henergy, ?_⟩
  have hmeanpos : 0 < mean := by
    rw [henergy]
    exact Repair8.voltage_energy_pos D P hD marked
  obtain ⟨hgeometry, hsplit_bound⟩ := hsplit D P hD hDc hP marked
  obtain ⟨q, hq, Q, hpoints, hcurves, charts, finiteFaces, m, vertices,
    hinj, copies, hends, hmarked⟩ := hgeometry
  letI : Fintype (Face Q) := finiteFaces
  let J := sourceDeletedDualGraph D P marked Q charts
  let hc := source_deleted_dual_preconnected_of_classical
    D P hD hDc hP marked Q charts
    FiniteAvalanches.External.finite_plane_dual_connected
    FiniteAvalanches.External.finite_plane_dual_bond_cycle
  let G := groundedGreen J.left J.right (vertices (Fin.last m)) hc
  let p := fun k : Fin m => G (vertices 0) (vertices k.castSucc) -
    G (vertices 0) (vertices k.succ)
  let W := fun k : Fin (m + 1) => G (vertices k) (vertices k) - G (vertices 0) (vertices k)
  have hcard : m = boundaryCount := by
    have h := Fintype.card_congr copies
    rw [Fintype.card_fin, ReferenceMoment.retained_boundary_card D P marked] at h
    exact h
  have hprob := source_path_probability_bounds D P hD hDc hP marked Q charts
    finiteFaces m vertices hinj copies hends hmarked
  change (∀ k, 0 ≤ p k ∧ p k ≤ 1) ∧ (∑ k, p k) = ReferenceMoment.forestMean D P marked at hprob
  have hsum : (∑ k, p k) = mean := hprob.2.trans hmean.symm
  have hsplit_local := hsplit_bound q hq Q hpoints hcurves charts finiteFaces
    m vertices hinj copies hends hmarked
  change ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
    ∀ j : Fin m, (j.val + 1 = i.val ∨ j.val = i.val) →
      W i ≤ 1 + 3888 * (1 + Real.log (2 / p j)) at hsplit_local
  have hw0 : W 0 = 0 := sub_self _
  have hwm : W (Fin.last m) = 0 := by
    dsimp only [W, G]
    rw [groundedGreen_ground, groundedGreen_ground, sub_self]
  have harc := (arc_variance D P hD hDc hP marked).2
    q hq Q hpoints hcurves charts finiteFaces m vertices hinj copies hends hmarked
  simp only [add_sub_assoc] at harc
  change variance ≤ mean + 3 * ∑ k : Fin m, p k * (W k.castSucc + W k.succ) at harc
  rw [← hsum] at harc
  have hfinal := FiniteAvalanches.Electrical.Reference.split_arc_variance_le p W variance
    (fun k => (hprob.1 k).1) (fun k => (hprob.1 k).2)
    (hsum.symm ▸ hmeanpos) hw0 hwm hsplit_local harc
  rw [hsum, hcard] at hfinal
  exact hfinal

end
end FiniteAvalanches.Electrical.Source.Reference
