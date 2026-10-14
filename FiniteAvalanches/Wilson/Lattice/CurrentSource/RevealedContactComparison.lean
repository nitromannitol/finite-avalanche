import FiniteAvalanches.Wilson.Lattice.CurrentSource.RevealedGeometry
import FiniteAvalanches.Wilson.Lattice.CurrentSource.RootChangeEvents

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentRevealedGeometry
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

/-- The same actual infinite-component root witness supplies every geometric
hypothesis and the corrected contact comparison, before any threshold is chosen. -/
theorem exists_revealed_roots_with_contact_comparison (κ : ℕ) (hκ : 30 ≤ κ)
    (K : Finset (Site 2)) (γ : Set (Site 2))
    (hK : ((lattice 2).induce (K : Set (Site 2))).Connected)
    (h0 : (0 : Site 2) ∈ K) (hd : Disjoint (K : Set (Site 2)) γ)
    (hγc : ((lattice 2).induce γ).Connected) (hγf : γᶜ.Finite)
    (hn : ∃ b ∈ γ, (lattice 2).Adj 0 b)
    (h r : ℕ) (hh : 10 ≤ h) (hr : h^κ ≤ r)
    (hdiam : 16*r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)))
    (R : RootPair) (hRK : (K : Set (Site 2)) ⊆ R.zero)
    (hRbox : R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)))
    (hRγ : γ ⊆ R.one) :
    ∃ (w : Site 2) (Z : Finset (Site 2)) (Q : RootPair),
      Q.zero = ((K ∪ Z : Finset (Site 2)) : Set (Site 2)) ∧
      (Z : Set (Site 2)) ⊆ box 2 (2*h) ∧ R.zero ⊆ Q.zero ∧ Q.one ⊆ R.one ∧
      Q.one ⊆ (box 2 (2*h))ᶜ ∧ (R.zero ∪ R.one)ᶜ.Finite ∧ (Q.zero ∪ Q.one)ᶜ.Finite ∧
      10^30 ≤ r ∧ siteRadius 0 w ≤ r ∧
      ((Translation.roots Q (-w)).zero ∪ (Translation.roots Q (-w)).one)ᶜ.Finite ∧
      0 ∈ (Translation.roots Q (-w)).zero ∧
      (∃ b ∈ (Translation.roots Q (-w)).one, (lattice 2).Adj 0 b) ∧
      ((lattice 2).induce (Translation.roots Q (-w)).zero).Connected ∧
      (∃ x ∈ (Translation.roots Q (-w)).zero, 2*r ≤ siteRadius 0 x) ∧
      ((lattice 2).induce (Translation.roots Q (-w)).one).Connected ∧
      (∃ y ∈ (Translation.roots Q (-w)).one, siteRadius 0 y = r) ∧
      Needle.wiredConductance (2*h)
        (Finset.univ.filter (fun x : FiniteWired.Active (2*h) => FiniteWired.site x ∈ Z)) ≤
          2304 * Real.log h ∧ Q.one.Infinite ∧
      (∃ c : ↥(γ \ box 2 (2*h)), Q.one = JointExterior.component (γ \ box 2 (2*h)) c) ∧
      (∀ d : ↥(γ \ box 2 (2*h)),
        (JointExterior.component (γ \ box 2 (2*h)) d).Infinite →
          JointExterior.component (γ \ box 2 (2*h)) d = Q.one) ∧
      ∀ t : ℝ, (wilsonColorLaw Q).real (kContactEvent K (3*(r : ℝ)) t) ≤
        (wilsonColorLaw R).real (kContactEvent K (3*(r : ℝ)) t) := by
  obtain ⟨w,Z,Q,hQ0,hZo,hRQ,hQR,hQout,hRcf,hQcf,hrscale,hwrle,
    hsf,hs0,hsn,hsc0,hsfar,hsc1,hsmeet,hbudget,hQinf,hQcomponent,hQunique⟩ :=
    CurrentRevealedGeometry.exists_revealed_roots κ hκ K γ hK h0 hd hγc hγf hn
      h r hh hr hdiam R hRK hRbox hRγ
  refine ⟨w,Z,Q,hQ0,hZo,hRQ,hQR,hQout,hRcf,hQcf,hrscale,hwrle,
    hsf,hs0,hsn,hsc0,hsfar,hsc1,hsmeet,hbudget,hQinf,hQcomponent,hQunique,?_⟩
  intro t
  apply CurrentRootChanges.color_event_mono_cofinite R Q hRcf hQcf hRQ hQR _
    (isClopen_kContactEvent K (3*(r : ℝ)) t).isClosed.measurableSet
  intro p hp q hpq
  change t ≤ (kContacts K (3*(r : ℝ)) p : ℝ) at hp
  change t ≤ (kContacts K (3*(r : ℝ)) q : ℝ)
  exact hp.trans (Nat.cast_le.mpr (JointContactOrder.contacts_mono _ p q hpq))

end
end FiniteAvalanches.Wilson.Lattice.CurrentRevealedGeometry
