import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.Path
import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.NeedleEnlargement
import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.Translation

set_option autoImplicit false
namespace JointSourceGeometry
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

theorem source_scales (κ h r : ℕ) (hκ : 30 ≤ κ) (hh : 10 ≤ h) (hr : h^κ ≤ r) :
    10^30 ≤ r ∧ 2*h ≤ r := by
  constructor
  · calc
      10^30 ≤ h^30 := Nat.pow_le_pow_left hh 30
      _ ≤ h^κ := Nat.pow_le_pow_right (by omega) hκ
      _ ≤ r := hr
  · calc
      2*h ≤ h^2 := by nlinarith only [hh]
      _ ≤ h^κ := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ r := hr

/-- The revealed-root geometric construction, using only the original source
hypotheses. Its local-comparison geometry uses the same r and the exact shift -w. -/
theorem exists_root_geometry (κ : ℕ) (hκ : 30 ≤ κ)
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
    ∃ (c : ↥(γ \ box 2 (2*h))) (w : Site 2) (Z : Finset (Site 2)) (R' : RootPair),
      R'.zero = ((K ∪ Z : Finset (Site 2)) : Set (Site 2)) ∧
      R'.one = JointExterior.component (γ \ box 2 (2*h)) c ∧
      (∃ (b z : Site 2) (P : (lattice 2).Walk b c.val)
        (q₀ : (lattice 2).Walk b w) (e : (lattice 2).Adj w z)
        (q₁ : (lattice 2).Walk z c.val),
        b ∈ γ ∧ (lattice 2).Adj 0 b ∧ P.IsPath ∧
        (∀ x ∈ P.support, x ∈ γ) ∧ P = q₀.append (.cons e q₁) ∧
        (∀ x ∈ q₁.support, x ∈ R'.one)) ∧
      Needle.radius w = 2*h ∧ siteRadius 0 w = 2*h ∧ w ∈ γ ∧
      ((lattice 2).induce (Z : Set (Site 2))).Connected ∧
      (Z : Set (Site 2)) ⊆ box 2 (2*h) ∧ box 2 h ⊆ (Z : Set (Site 2)) ∧ w ∈ Z ∧
      R.zero ⊆ R'.zero ∧ (K : Set (Site 2)) ⊆ R'.zero ∧ R'.one ⊆ R.one ∧
      R'.one ⊆ γ ∧ R'.one ⊆ (box 2 (2*h))ᶜ ∧ R'.oneᶜ.Finite ∧
      (R.zero ∪ R.one)ᶜ.Finite ∧ (R'.zero ∪ R'.one)ᶜ.Finite ∧
      ((lattice 2).induce R'.zero).Connected ∧ w ∈ R'.zero ∧
      (∃ x ∈ R'.zero, 2*r ≤ siteRadius w x) ∧
      ((lattice 2).induce R'.one).Connected ∧
      (∃ z ∈ R'.one, (lattice 2).Adj w z) ∧
      (∃ y ∈ R'.one, siteRadius w y = r) ∧
      10^30 ≤ r ∧ siteRadius 0 w ≤ r ∧ window w (2*r) ⊆ boxSites (3*r) ∧
      ((Translation.roots R' (-w)).zero ∪ (Translation.roots R' (-w)).one)ᶜ.Finite ∧
      0 ∈ (Translation.roots R' (-w)).zero ∧
      (∃ b ∈ (Translation.roots R' (-w)).one, (lattice 2).Adj 0 b) ∧
      ((lattice 2).induce (Translation.roots R' (-w)).zero).Connected ∧
      (∃ x ∈ (Translation.roots R' (-w)).zero, 2*r ≤ siteRadius 0 x) ∧
      ((lattice 2).induce (Translation.roots R' (-w)).one).Connected ∧
      (∃ y ∈ (Translation.roots R' (-w)).one, siteRadius 0 y = r) ∧
      Needle.wiredConductance (2*h)
        (Finset.univ.filter (fun x : FiniteWired.Active (2*h) => FiniteWired.site x ∈ Z)) ≤
          107 * Real.log h := by
  obtain ⟨c,b,w,z,P,q₀,e,q₁,hcf,hb,hadj,hP,hPγ,hdecomp,hw,hwγ,hq⟩ :=
    JointRevealedPath.exists_revealed_path γ hγc hγf hn h hh
  let Γ' := JointExterior.component (γ \ box 2 (2*h)) c
  have hΓU : Γ' ⊆ γ \ box 2 (2*h) := JointExterior.component_subset _ c
  have hΓγ : Γ' ⊆ γ := fun _ hx => (hΓU hx).1
  have hΓout : Γ' ⊆ (box 2 (2*h))ᶜ := fun _ hx => (hΓU hx).2
  have hΓc : ((lattice 2).induce Γ').Connected := JointExterior.component_connected _ c
  have hzΓ : z ∈ Γ' := hq z q₁.start_mem_support
  obtain ⟨Z,hZc,hZo,hZi,hwZ,hAc,hdisj,hbudget⟩ :=
    JointNeedleEnlargement.exists_needle_enlargement h hh w hw K hK h0 γ Γ' hd hΓγ hΓout
  let R' : RootPair :=
    { zero := ((K ∪ Z : Finset (Site 2)) : Set (Site 2))
      one := Γ'
      disjoint := hdisj
      zero_nonempty := ⟨0,Finset.mem_union_left _ h0⟩
      one_nonempty := ⟨c.val,JointExterior.base_mem_component _ c⟩ }
  have hRR' : R.zero ⊆ R'.zero :=
    JointNeedleEnlargement.enlargement_contains_current_zero K Z h hZi R hRbox
  have hKR' : (K : Set (Site 2)) ⊆ R'.zero := hRK.trans hRR'
  have hR'R : R'.one ⊆ R.one := hΓγ.trans hRγ
  obtain ⟨hrscale,htwo⟩ := source_scales κ h r hκ hh hr
  have hrpos : 0 < r := (by norm_num : 0 < 10^30).trans_le hrscale
  have hwr : siteRadius 0 w = 2*h := by
    have he := (JointMetricGeometry.radius_cast w).trans hw
    exact_mod_cast he
  have hwrle : siteRadius 0 w ≤ r := hwr ▸ htwo
  have hwA : w ∈ R'.zero := Finset.mem_union_right _ hwZ
  have hfar : ∃ x ∈ R'.zero, 2*r ≤ siteRadius w x := by
    obtain ⟨x,hx,he⟩ := JointMetricGeometry.large_extent K r hrpos hdiam w
    exact ⟨x,hKR' hx,he⟩
  have hneighbor : ∃ z ∈ R'.one, (lattice 2).Adj w z := ⟨z,hzΓ,e⟩
  have hmeet : ∃ y ∈ R'.one, siteRadius w y = r :=
    JointMetricGeometry.connected_cofinite_meets_radius Γ' hΓc hcf w r (by omega) hneighbor
  have hRfinite : (R.zero ∪ R.one)ᶜ.Finite :=
    hγf.subset (fun _ hx hy => hx (Or.inr (hRγ hy)))
  have hR'finite : (R'.zero ∪ R'.one)ᶜ.Finite :=
    hcf.subset (fun _ hx hy => hx (Or.inr hy))
  obtain ⟨hsf,hs0,hsn,hsc0,hsfar,hsc1,hsmeet⟩ :=
    JointTranslatedGeometry.translated_local_hypotheses R' w r hcf hwA hneighbor hAc hfar hΓc hmeet
  refine ⟨c,w,Z,R',rfl,rfl,?_,hw,hwr,hwγ,hZc,hZo,hZi,hwZ,hRR',hKR',hR'R,hΓγ,hΓout,
    hcf,hRfinite,hR'finite,hAc,hwA,hfar,hΓc,hneighbor,hmeet,hrscale,hwrle,
    JointMetricGeometry.translated_window_subset w r hwrle,
    hsf,hs0,hsn,hsc0,hsfar,hsc1,hsmeet,hbudget⟩
  exact ⟨b,z,P,q₀,e,q₁,hb,hadj,hP,hPγ,hdecomp,hq⟩

end
end JointSourceGeometry
