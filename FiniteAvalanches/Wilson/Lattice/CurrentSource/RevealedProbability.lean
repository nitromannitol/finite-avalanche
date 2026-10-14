import FiniteAvalanches.Wilson.Lattice.CurrentSource.RevealedContactComparison
import FiniteAvalanches.Wilson.Lattice.RevealedRoots.Probability
import FiniteAvalanches.Wilson.Lattice.CurrentSource.ScaleGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentRevealedProbability
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

                                                                               
                                                                                 
                                                                            
theorem revealed_of_local (ε : ℝ) (hε : 0 < ε)
    (hlocal : ∀ (r : ℕ), 10^30 ≤ r → ∀ R : RootPair,
      (R.zero ∪ R.one)ᶜ.Finite → 0 ∈ R.zero →
      (∃ b ∈ R.one, (lattice 2).Adj 0 b) →
      ((lattice 2).induce R.zero).Connected →
      (∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x) →
      ((lattice 2).induce R.one).Connected →
      (∃ y ∈ R.one, siteRadius 0 y = r) →
      ε ≤ (wilsonColorLaw R).real
        (localContactEvent R.zero 0 (2*r) (Real.log (r : ℝ)/8))) :
    ∃ κ : ℕ, 30 ≤ κ ∧ 73728 ≤ ε*(κ : ℝ) ∧
      ∀ (K : Finset (Site 2)) (γ : Set (Site 2)),
        ((lattice 2).induce (K : Set (Site 2))).Connected →
        0 ∈ K → Disjoint (K : Set (Site 2)) γ →
        ((lattice 2).induce γ).Connected → γᶜ.Finite →
        (∃ b ∈ γ, (lattice 2).Adj 0 b) →
        ∀ h r : ℕ, 10 ≤ h → h^κ ≤ r →
        16*r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) →
        ∀ R : RootPair, (K : Set (Site 2)) ⊆ R.zero →
          R.zero ⊆ (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) →
          γ ⊆ R.one →
          ε/2 ≤ (wilsonColorLaw R).real
            (kContactEvent K (3*(r : ℝ)) (Real.log (r : ℝ)/16)) := by
  obtain ⟨κ,hκ,hpaid,hscale⟩ := CurrentScaleGeometry.exists_uniform_kappa ε hε
  refine ⟨κ,hκ,hpaid,?_⟩
  intro K γ hK h0 hd hγc hγf hn h r hh hr hdiam R hRK hRbox hRγ
  obtain ⟨w,Z,Q,hQ0,hZo,_hRQ,_hQR,hQout,_hRcf,_hQcf,
    hrscale,hwrle,hsf,hs0,hsn,hsc0,hsfar,hsc1,hsmeet,hbudget,_hQinf,_hQcomponent,_hQunique,hcomparison⟩ :=
    CurrentRevealedGeometry.exists_revealed_roots_with_contact_comparison κ hκ K γ hK h0 hd hγc hγf hn h r hh hr hdiam R hRK hRbox hRγ
  have hlocShift := hlocal r hrscale (Translation.roots Q (-w))
    hsf hs0 hsn hsc0 hsfar hsc1 hsmeet
  rw [Revealed19.local_probability_translate] at hlocShift
  obtain ⟨_hrscale,_htwo,_hlog,hpay⟩ := hscale h r hh hr
  have hmean : (∫ σ, (contacts (Z \ K) σ : ℝ) ∂wilsonColorLaw Q) ≤
      2304 * Real.log h :=
    (Revealed19.added_mean_le_conductance Q K Z (2*h) hQ0 hZo hQout).trans hbudget
  have hrpos : (1 : ℝ) < r := by
    exact_mod_cast (by omega : 1 < r)
  have ht : 0 < Real.log (r : ℝ)/16 := div_pos (Real.log_pos hrpos) (by norm_num)
  have hbad := Revealed19.added_markov Q K Z (Real.log (r : ℝ)/16) (ε/2) ht (hmean.trans hpay)
  have hloc : ε ≤ (wilsonColorLaw Q).real
      (localContactEvent Q.zero w (2*r) (2*(Real.log (r : ℝ)/16))) := by
    rw [show 2*(Real.log (r : ℝ)/16) = Real.log (r : ℝ)/8 by ring]
    exact hlocShift
  have hKloc := Revealed19.local_subtract_added Q K Z hQ0 w (2*r) (Real.log (r : ℝ)/16) ε hloc hbad
  have hbox : localContactEvent (K : Set (Site 2)) w (2*r) (Real.log (r : ℝ)/16) ⊆
      kContactEvent K (3*(r : ℝ)) (Real.log (r : ℝ)/16) := by
    intro σ hσ
    change Real.log (r : ℝ)/16 ≤ (localContacts (K : Set (Site 2)) w (2*r) σ : ℝ) at hσ
    change Real.log (r : ℝ)/16 ≤ (kContacts K (3*(r : ℝ)) σ : ℝ)
    exact hσ.trans (Nat.cast_le.mpr (JointScaleGeometry.shifted_contacts_le K w r hwrle σ))
  exact (hKloc.trans (measureReal_mono hbox (by finiteness))).trans
    (hcomparison (Real.log (r : ℝ)/16))


end
end FiniteAvalanches.Wilson.Lattice.CurrentRevealedProbability
