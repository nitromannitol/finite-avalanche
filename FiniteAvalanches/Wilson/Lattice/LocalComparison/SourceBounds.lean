import FiniteAvalanches.Wilson.Lattice.LocalComparison.CopiedEnergy
import FiniteAvalanches.Wilson.Lattice.LocalComparison.EnergyNumeric

set_option autoImplicit false
namespace LocalSourceBounds
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

/-- The local circuit bounds on a network constructed from the source roots.
The original exit count and the once-per-copy conductance are unchanged. -/
theorem exists_bounded_network (r : ℕ) (hr : 10^30 ≤ r) (R : RootPair)
    (_hcofinite : (R.zero ∪ R.one)ᶜ.Finite)
    (h0 : (0 : Site 2) ∈ R.zero) (hneigh : ∃ b ∈ R.one, (lattice 2).Adj 0 b)
    (hZero : ((lattice 2).induce R.zero).Connected)
    (hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
    (hOne : ((lattice 2).induce R.one).Connected)
    (hmeet : ∃ y ∈ R.one, siteRadius 0 y = r) :
    ∃ (D : Finset (Site 2)) (P : OneSet D)
      (hD : ((lattice 2).induce (D : Set (Site 2))).Connected)
      (marked : MarkedCopy D P) (b y : Site 2) (q : (lattice 2).Walk b y),
      b ∈ R.one ∧ (lattice 2).Adj 0 b ∧
      ((lattice 2).induce (D : Set (Site 2))ᶜ).Connected ∧
      ((lattice 2).induce (P.val.image Subtype.val : Set (Site 2))).Connected ∧
      P.val.image Subtype.val = q.support.toFinset ∧ q.IsPath ∧ siteRadius 0 y = r ∧
      (∀ x ∈ q.support, x ∈ R.one ∧ x ∈ boxSites r) ∧
      (∀ x ∈ q.support, x ≠ y → siteRadius 0 x < r) ∧
      ((originalA marked.val = 0 ∧ originalB marked.val = b) ∨
        (originalA marked.val = b ∧ originalB marked.val = 0)) ∧
      b ∈ D ∧ (0 : Site 2) ∉ D ∧ R.zero ⊆ (D : Set (Site 2))ᶜ ∧
      (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)) ∧
      (∀ phi : Vertex D P → ℝ, phi (alpha D P) = 0 → phi (beta D P) = 1 →
        Real.log (r : ℝ)/2 ≤ energy (copyA D P marked) (copyB D P marked) phi) ∧
      (let M := energy (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked)
       let m := ((domainCopies D).filter fun e =>
         (originalA e ∈ D ∧ originalB e ∉ D) ∨ (originalB e ∈ D ∧ originalA e ∉ D)).card-1
       Real.log (r : ℝ)/2 ≤ M ∧ 32 ≤ M ∧ M ≤ (m : ℝ) ∧ m ≤ r^3) ∧
      ∀ x ∈ D, ∀ z, z ∉ D → z ∉ R.zero → (lattice 2).Adj x z → z ∉ boxSites (2*r-1) := by
  obtain ⟨b,hb,hadj⟩ := hneigh
  obtain ⟨D,P,hD,marked,y,q,hDc,hP,hPQ,hq,hy,hqroots,hqfirst,hmark,hbD,h0D,hZD,hDB,
    hm,hupper,hexit⟩ := LocalSourceNetwork.exists_network r hr R h0 b hb hadj hZero hfar hOne hmeet
  have hlower (phi : Vertex D P → ℝ) (hp0 : phi (alpha D P) = 0) (hp1 : phi (beta D P) = 1) :
      Real.log (r : ℝ)/2 ≤ energy (copyA D P marked) (copyB D P marked) phi :=
    (LocalEnergyNumeric.log_half_le_harmonic_half r).trans
      (LocalCopiedEnergy.admissible_energy_lower r R h0 hZero hfar b y hadj q hy D P hZD hPQ
        marked hmark phi hp0 hp1)
  have hs := Repair8.voltage_spec D P hD marked
  have hl := hlower (Repair8.voltage D P hD marked) hs.1 hs.2.1
  exact ⟨D,P,hD,marked,b,y,q,hb,hadj,hDc,hP,hPQ,hq,hy,hqroots,hqfirst,hmark,hbD,h0D,
    hZD,hDB,hlower,⟨hl,(LocalEnergyNumeric.thirty_two_le_log_half r hr).trans hl,hupper,hm⟩,hexit⟩

end
end LocalSourceBounds
