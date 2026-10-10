import FiniteAvalanches.Wilson.Lattice.LocalComparison.SourceLoss

set_option autoImplicit false
namespace LocalActualLossConsumer
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.Lattice MeasureTheory
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical ENNReal
noncomputable section

theorem loss_bound (r : ℕ) (hr : 10^30 ≤ r) (R : RootPair)
    (_hcofinite : (R.zero ∪ R.one)ᶜ.Finite)
    (h0 : (0 : Site 2) ∈ R.zero)
    (hneigh : ∃ b ∈ R.one, (lattice 2).Adj 0 b)
    (hZero : ((lattice 2).induce R.zero).Connected)
    (hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
    (hOne : ((lattice 2).induce R.one).Connected)
    (hmeet : ∃ y ∈ R.one, siteRadius 0 y = r) :
    ∃ (D : Finset (Site 2)) (P : OneSet D)
      (_hD : ((lattice 2).induce (D : Set (Site 2))).Connected)
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
      (∃ hbU : b ∈ (boxSites (2*r-1)).filter (fun x => x ∉ R.zero),
        D = JointFiniteComponent.componentSites ((boxSites (2*r-1)).filter (fun x => x ∉ R.zero)) ⟨b,hbU⟩) ∧
      (∀ x ∈ D, ∀ z, z ∉ D → z ∉ R.zero → (lattice 2).Adj x z → z ∉ boxSites (2*r-1)) ∧
      (∀ᵐ σ ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P),
        (∀ x ∉ D, σ x = false) ∧
        LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ =
          (localContacts ((D : Set (Site 2))ᶜ \ R.zero) 0 (2*r) σ : ℝ≥0∞)) ∧
      Integrable (fun σ => (LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ).toReal)
        (wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ∧
      (∫⁻ σ, LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ
        ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ≤ 16 ∧
      (∫ σ, (LocalFullContacts.full ((D : Set (Site 2))ᶜ \ R.zero) σ).toReal
        ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P)) ≤ 16 := by
  exact LocalSourceLoss.exists_local_loss_bound r hr R _hcofinite h0 hneigh hZero hfar hOne hmeet

end
end LocalActualLossConsumer
