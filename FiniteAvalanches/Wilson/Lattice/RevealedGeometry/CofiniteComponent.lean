import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.Exterior

set_option autoImplicit false
namespace JointCofiniteComponent
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem box_finite (N : ℕ) : (box 2 N).Finite := by
  apply (boxSites N).finite_toSet.subset
  intro x hx
  apply (mem_box_sites N x).mpr
  intro i
  exact abs_le.mp (hx i)

theorem box_radius (x : Site 2) (N : ℕ) : x ∈ box 2 N ↔ siteRadius 0 x ≤ N := by
  rw [siteRadius_le_iff]
  simp only [box, Set.mem_setOf_eq, Pi.zero_apply, sub_zero]

/-- A cofinite component is constructed from an exterior-square anchor. -/
theorem exists_cofinite_component (γ : Set (Site 2)) (hf : γᶜ.Finite) (n : ℕ) :
    ∃ c : ↥(γ \ box 2 n),
      (JointExterior.component (γ \ box 2 n) c)ᶜ.Finite := by
  let N := max n (hf.toFinset.sup (siteRadius 0))
  have hNU : (box 2 N)ᶜ ⊆ γ \ box 2 n := by
    intro x hx
    constructor
    · by_contra hn
      have hm : x ∈ hf.toFinset := hf.mem_toFinset.mpr hn
      have hr : siteRadius 0 x ≤ N := (Finset.le_sup hm).trans (le_max_right _ _)
      exact hx ((box_radius x N).mpr hr)
    · intro hb
      apply hx
      exact (box_radius x N).mpr (((box_radius x n).mp hb).trans (le_max_left _ _))
  let a : Site 2 := fun _ => (N : ℤ)+1
  have ha : a ∈ (box 2 N)ᶜ := by
    intro hb
    have h := hb 0
    simp only [a, abs_of_nonneg (by omega : 0 ≤ (N : ℤ)+1)] at h
    omega
  let c : ↥(γ \ box 2 n) := ⟨a,hNU ha⟩
  have hE : (box 2 N)ᶜ ⊆ JointExterior.component (γ \ box 2 n) c := by
    let f : (lattice 2).induce (box 2 N)ᶜ →g (lattice 2).induce (γ \ box 2 n) :=
      { toFun := fun x => ⟨x.val,hNU x.property⟩
        map_rel' := fun h => h }
    intro x hx
    exact JointExterior.reachable_mem_component _ c ⟨x,hNU hx⟩
      (((JointExterior.exterior_connected N).preconnected ⟨a,ha⟩ ⟨x,hx⟩).map f)
  refine ⟨c,(box_finite N).subset ?_⟩
  intro x hx
  by_contra hn
  exact hx (hE hn)

end
end JointCofiniteComponent
