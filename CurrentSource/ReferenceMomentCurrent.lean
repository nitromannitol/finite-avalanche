import FiniteAvalanchesCurrent.ArcMomentV7
import CurrentSource.CurrentSplitAssembly
import FiniteAvalanches.Electrical.Reference.ReferenceMomentOfSplit

namespace FiniteAvalanches.Electrical.Source.Reference
open LatticeProb
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.LatticeDrawing FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

/-- Exact reference-moment conclusion through current minimum-face21, square16, weighted Green and arc/Jensen. -/
theorem reference_moment_current :
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
  obtain ⟨sourceWitness,hfamily⟩ := LovaszApplication.current_S7_original_family_cutoff D P hD hDc hP marked
  letI : Fintype (Face sourceWitness.Q) := sourceWitness.finiteFaces
  obtain ⟨R,hR,_hdisjoint,_hzero,hcutoff⟩ := hfamily
  let q := sourceWitness.q
  let Q := sourceWitness.Q
  let charts := sourceWitness.charts
  let finiteFaces := sourceWitness.finiteFaces
  let m := sourceWitness.m
  let vertices := sourceWitness.vertices
  let copies := sourceWitness.copies
  have hq := sourceWitness.continuous_q
  have hpoints := sourceWitness.point_eq
  have hcurves := sourceWitness.curve_eq
  have hinj := sourceWitness.injective_vertices
  have hends := sourceWitness.copy_ends
  have hmarked := sourceWitness.marked_ends
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
  have hsplit_local : ∀ i : Fin (m + 1), 0 < i.val → i.val < m →
      ∀ j : Fin m, (j.val + 1 = i.val ∨ j.val = i.val) →
        W i ≤ 1+3888*(1+Real.log (2/p j)) := by
    intro i hi0 him j hj
    obtain ⟨f,hf0,hf1,hw⟩ := SplitStep.current_whole_weighted_minimum_trial_of_original_cutoff
      D P hD hDc hP marked q hq Q hpoints hcurves charts finiteFaces m vertices hinj
      copies hends hmarked R hR
      (fun k _hp => (hcutoff k).choose_spec.2.2.2) i hi0 him j hj
    have hg := Source.CurrentSplit.current_split_weighted_energy D P hD hDc hP marked q hq Q
      hpoints hcurves charts finiteFaces m vertices hinj copies hends hmarked i hi0 him f hf0 hf1
    have hp := hcutoff j
    have hL := Source.CurrentSplit.one_le_log_factor (p j) hp.choose hp.choose_spec.1
    dsimp only [W,p] at hg ⊢
    linarith only [hg,hw,hL]
  have hw0 : W 0 = 0 := sub_self _
  have hwm : W (Fin.last m) = 0 := by
    dsimp only [W, G]
    rw [groundedGreen_ground, groundedGreen_ground, sub_self]
  have harc := (FiniteAvalanches.Electrical.CurrentSourceRoots.arc_variance D P hD hDc hP marked).2
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
