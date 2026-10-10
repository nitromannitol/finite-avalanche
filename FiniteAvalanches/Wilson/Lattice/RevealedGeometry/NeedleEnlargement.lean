import FiniteAvalanches.Needle.Sharp.Proof
import FiniteAvalanches.Wilson.Lattice.ForestEvents
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false
namespace JointNeedleEnlargement
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches (siteRadius siteRadius_le_iff)
open FiniteWired (site)
open scoped Classical
noncomputable section

/-- The actual connected box/path enlargement, including its original-copy budget. -/
theorem exists_needle_enlargement (h : ℕ) (hh : 10 ≤ h) (w : Point)
    (hw : radius w = 2 * h) (K : Finset Point)
    (hK : ((lattice 2).induce (K : Set Point)).Connected) (h0 : (0 : Point) ∈ K)
    (γ Γ' : Set Point) (hd : Disjoint (K : Set Point) γ)
    (hΓ : Γ' ⊆ γ) (hout : Γ' ⊆ (box 2 (2*h))ᶜ) :
    ∃ Z : Finset Point,
      ((lattice 2).induce (Z : Set Point)).Connected ∧
      (Z : Set Point) ⊆ box 2 (2*h) ∧ box 2 h ⊆ (Z : Set Point) ∧ w ∈ Z ∧
      ((lattice 2).induce ((K ∪ Z : Finset Point) : Set Point)).Connected ∧
      Disjoint ((K ∪ Z : Finset Point) : Set Point) Γ' ∧
      wiredConductance (2*h)
        (Finset.univ.filter (fun x : FiniteWired.Active (2*h) => FiniteWired.site x ∈ Z)) ≤
          107 * Real.log h := by
  obtain ⟨Z, hZc, hZo, hZi, hwZ, hZe⟩ := Needle107Target.connected_set_conductance_107 h hh w hw
  refine ⟨Z, hZc, hZo, hZi, hwZ, ?_, ?_, hZe⟩
  · have h0Z : (0 : Point) ∈ (Z : Set Point) := hZi (by simp [box])
    have hc := SimpleGraph.induce_union_connected hK.preconnected hZc.preconnected
      (show ((K : Set Point) ∩ (Z : Set Point)).Nonempty from ⟨0, h0, h0Z⟩)
    have he : ((K ∪ Z : Finset Point) : Set Point) = (K : Set Point) ∪ (Z : Set Point) := by
      ext x
      exact Finset.mem_union
    rw [he]
    exact hc
  · apply Set.disjoint_left.mpr
    intro x hx hxΓ
    rcases Finset.mem_union.mp hx with hxK | hxZ
    · exact Set.disjoint_left.mp hd hxK (hΓ hxΓ)
    · exact hout hxΓ (hZo hxZ)

theorem enlargement_contains_current_zero (K Z : Finset Point) (h : ℕ)
    (hZi : box 2 h ⊆ (Z : Set Point)) (R : RootPair)
    (hR : R.zero ⊆ (K : Set Point) ∪ (boxSites h : Set Point)) :
    R.zero ⊆ ((K ∪ Z : Finset Point) : Set Point) := by
  intro x hx
  rcases hR hx with hxK | hxb
  · exact Finset.mem_union_left _ hxK
  · exact Finset.mem_union_right _ (hZi ((FiniteWired.inBox_iff h x).mp ((mem_box_sites h x).mp hxb)))

/-- Cofiniteness required for global monotonicity follows from the actual one roots. -/
theorem enlargement_union_cofinite (K Z : Finset Point) (Γ' : Set Point)
    (hΓ : Γ'ᶜ.Finite) :
    (((K ∪ Z : Finset Point) : Set Point) ∪ Γ')ᶜ.Finite := by
  apply hΓ.subset
  intro x hx hxΓ
  exact hx (Or.inr hxΓ)

end
end JointNeedleEnlargement
