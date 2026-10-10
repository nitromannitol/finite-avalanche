import FiniteAvalanches.Wilson.Lattice.RevealedRoots.Probability
import FiniteAvalanches.Wilson.Lattice.LocalComparison.SourceComparison

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.SourceTargets
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

/-- Shared-epsilon source conclusion under the entire current reference proposition. -/
theorem local_comparison_and_revealed_roots_of_reference_v3
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
    (∃ ε : ℝ, 0 < ε ∧
  (∀ (r : ℕ), 10 ^ 30 ≤ r → ∀ (R : RootPair),
    (R.zero ∪ R.one)ᶜ.Finite →
    0 ∈ R.zero →
    (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
    ((lattice 2).induce R.zero).Connected →
    (∃ x ∈ R.zero, 2 * r ≤ siteRadius 0 x) →
    ((lattice 2).induce R.one).Connected →
    (∃ y ∈ R.one, siteRadius 0 y = r) →
    ε ≤ (wilsonColorLaw R).real
      (localContactEvent R.zero 0 (2 * r) ((1 / 8 : ℝ) * Real.log (r : ℝ)))) ∧
  (∃ κ : ℕ, 30 ≤ κ ∧
    ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
      ((lattice 2).induce (K : Set (Site 2))).Connected →
      0 ∈ K → Disjoint (K : Set (Site 2)) γ →
      ((lattice 2).induce γ).Connected → γᶜ.Finite →
      (∃ b ∈ γ, (lattice 2).Adj 0 b) →
      ∀ (h r : ℕ), 10 ≤ h → h ^ κ ≤ r →
      16 * r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
      ∀ (R : RootPair), (K : Set (Site 2)) ⊆ R.zero →
        R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
        γ ⊆ R.one →
        ε / 2 ≤ (wilsonColorLaw R).real
          (kContactEvent K (3 * (r : ℝ)) ((1 / 16 : ℝ) * Real.log (r : ℝ))))) := by
  obtain ⟨ε,hε,hlocal⟩ := LocalComparisonActualConsumer.actual_local_comparison hReference
  obtain ⟨κ,hκ,hrevealed⟩ := Revealed19.revealed_of_local ε hε hlocal
  refine ⟨ε,hε,?_,κ,hκ,?_⟩
  · intro r hr R hcf h0 hn h0c hfar h1c hmeet
    simpa only [show (1/8 : ℝ)*Real.log (r : ℝ) = Real.log (r : ℝ)/8 by ring] using
      hlocal r hr R hcf h0 hn h0c hfar h1c hmeet
  · intro K γ hK h0 hd hγc hγf hn h r hh hr hdiam R hRK hRbox hRγ
    simpa only [show (1/16 : ℝ)*Real.log (r : ℝ) = Real.log (r : ℝ)/16 by ring] using
      hrevealed K γ hK h0 hd hγc hγf hn h r hh hr hdiam R hRK hRbox hRγ

end
end FiniteAvalanches.Wilson.Lattice.SourceTargets
