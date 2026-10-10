import FiniteAvalanches.Wilson.Lattice.LocalComparison.LocalComparison
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ReferenceMomentBound
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ContactSupport
import FiniteAvalanches.Wilson.Lattice.LocalComparison.SourceLossComparison
import FiniteAvalanches.Wilson.Lattice.LocalComparison.EnergyUpper
import FiniteAvalanches.Wilson.Lattice.LocalComparison.CopiedEnergy
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ContactOrder

set_option autoImplicit false
namespace LocalComparisonActualConsumer
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.Plane.SourceLattice MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

/-- The whole source local comparison, still conditional on the entire open reference proposition. -/
theorem actual_local_comparison
    (hReference :

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
    mean = M ∧ variance ≤ C*mean*(1+Real.log ((m : ℝ) / mean))
    ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℕ) (_hr : 10^30 ≤ r) (R : RootPair)
      (_hcofinite : (R.zero ∪ R.one)ᶜ.Finite)
      (_h0 : (0 : Site 2) ∈ R.zero)
      (_hneigh : ∃ b ∈ R.one, (lattice 2).Adj 0 b)
      (_hZero : ((lattice 2).induce R.zero).Connected)
      (_hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
      (_hOne : ((lattice 2).induce R.one).Connected)
      (_hmeet : ∃ y ∈ R.one, siteRadius 0 y = r),
      ε ≤ (wilsonColorLaw R).real
        (localContactEvent R.zero 0 (2*r) (Real.log (r : ℝ)/8)) := by
  exact LocalReferenceComparison.conditional_local_comparison hReference

end
end LocalComparisonActualConsumer
