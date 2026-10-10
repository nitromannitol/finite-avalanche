import FiniteAvalanches.Electrical.Reference.ReferenceMomentOfSplit
import FiniteAvalanchesFrozen.ElectricalSplitEstimateV2
import FiniteAvalanches.Electrical.Reference.Voltage

set_option autoImplicit false
namespace FiniteAvalanchesProofs.ElectricalReferenceMomentV4
open FiniteAvalanches.Electrical
open LatticeProb
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical BigOperators

theorem reference_moment_v4 :
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
  exact FiniteAvalanches.Electrical.Source.Reference.reference_moment_of_split
    FiniteAvalanches.Electrical.Source.split_estimate_v2

end FiniteAvalanchesProofs.ElectricalReferenceMomentV4
