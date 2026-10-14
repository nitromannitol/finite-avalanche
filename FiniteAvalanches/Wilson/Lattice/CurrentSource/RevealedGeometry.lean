import FiniteAvalanches.Wilson.Lattice.CurrentSource.InfiniteComponent
import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.Path
import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.Translation
import FiniteAvalanches.Wilson.Lattice.CurrentSource.NeedleGeometry
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ScaleGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CurrentRevealedGeometry
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- The actual path and needle construction, retaining the unique infinite
exterior component and every translated local-comparison datum in one witness. -/
theorem exists_revealed_roots (κ : ℕ) (hκ : 30 ≤ κ)
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
      ∀ d : ↥(γ \ box 2 (2*h)),
        (JointExterior.component (γ \ box 2 (2*h)) d).Infinite →
          JointExterior.component (γ \ box 2 (2*h)) d = Q.one := by
  obtain ⟨c,b,w,z,_P,_q₀,e,q₁,hcf,_hb,_hadj,_hP,_hPγ,_hdecomp,hw,_hwγ,hq⟩ :=
    JointRevealedPath.exists_revealed_path γ hγc hγf hn h hh
  let Γ' := JointExterior.component (γ \ box 2 (2*h)) c
  obtain ⟨hΓinf, hΓunique⟩ :=
    CurrentInfiniteComponent.cofinite_component_is_unique_infinite _ c hcf
  have hΓU : Γ' ⊆ γ \ box 2 (2*h) := JointExterior.component_subset _ c
  have hΓγ : Γ' ⊆ γ := fun _ hx => (hΓU hx).1
  have hΓout : Γ' ⊆ (box 2 (2*h))ᶜ := fun _ hx => (hΓU hx).2
  have hΓc : ((lattice 2).induce Γ').Connected := JointExterior.component_connected _ c
  have hzΓ : z ∈ Γ' := hq z q₁.start_mem_support
  obtain ⟨Z,hZc,hZo,hZi,hwZ,hAc,hdisj,hbudget⟩ :=
    CurrentNeedleGeometry.exists_needle_enlargement h hh w hw K hK h0 γ Γ' hd hΓγ hΓout
  let Q : RootPair :=
    { zero := ((K ∪ Z : Finset (Site 2)) : Set (Site 2))
      one := Γ'
      disjoint := hdisj
      zero_nonempty := ⟨0,Finset.mem_union_left _ h0⟩
      one_nonempty := hΓinf.nonempty }
  have hRQ : R.zero ⊆ Q.zero :=
    JointNeedleGeometry.enlargement_contains_current_zero K Z h hZi R hRbox
  have hKQ : (K : Set (Site 2)) ⊆ Q.zero := hRK.trans hRQ
  have hrscale : 10^30 ≤ r :=
    (Nat.pow_le_pow_left hh 30).trans ((Nat.pow_le_pow_right (by omega) hκ).trans hr)
  have htwo : 2*h ≤ r := by
    have hh2 : 2*h ≤ h^2 := by nlinarith only [hh]
    exact hh2.trans ((Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ κ)).trans hr)
  have hrpos : 0 < r := (by norm_num : 0 < 10^30).trans_le hrscale
  have hwr : siteRadius 0 w = 2*h := by
    exact_mod_cast (JointMetricGeometry.radius_cast w).trans hw
  have hwrle : siteRadius 0 w ≤ r := hwr ▸ htwo
  have hwQ : w ∈ Q.zero := Finset.mem_union_right K hwZ
  have hfar : ∃ x ∈ Q.zero, 2*r ≤ siteRadius w x := by
    obtain ⟨x,hx,he⟩ := JointMetricGeometry.large_extent K r hrpos hdiam w
    exact ⟨x,hKQ hx,he⟩
  have hnQ : ∃ z ∈ Q.one, (lattice 2).Adj w z := ⟨z,hzΓ,e⟩
  have hmeet : ∃ y ∈ Q.one, siteRadius w y = r :=
    JointMetricGeometry.connected_cofinite_meets_radius Γ' hΓc hcf w r (by omega) hnQ
  have hRcf := JointContactOrder.union_roots_cofinite R γ hγf hRγ
  have hQcf := JointNeedleGeometry.enlargement_union_cofinite K Z Γ' hcf
  obtain ⟨hsf,hs0,hsn,hsc0,hsfar,hsc1,hsmeet⟩ :=
    JointTranslatedGeometry.translated_local_hypotheses Q w r hcf hwQ hnQ hAc hfar hΓc hmeet
  exact ⟨w,Z,Q,rfl,hZo,hRQ,hΓγ.trans hRγ,hΓout,hRcf,hQcf,hrscale,hwrle,
    hsf,hs0,hsn,hsc0,hsfar,hsc1,hsmeet,hbudget,hΓinf,⟨c,rfl⟩,hΓunique⟩

end
end FiniteAvalanches.Wilson.Lattice.CurrentRevealedGeometry
