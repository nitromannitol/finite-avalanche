import FiniteAvalanches.Wilson.Lattice.LocalComparison.FiniteComponent
import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.Exterior
import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.Metric

set_option autoImplicit false
namespace LocalComplement
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- A walk from another component attaches to the connected removed set without
passing through the selected component. -/
theorem walk_to_removed (U : Finset (Site 2)) (b : U)
    (hS : ((lattice 2).induce (U : Set (Site 2))ᶜ).Connected)
    (z : Site 2) (hz : z ∉ U) {x : Site 2} (p : (lattice 2).Walk x z)
    (hx : x ∉ JointFiniteComponent.componentSites U b) :
    ((lattice 2).induce (JointFiniteComponent.componentSites U b : Set (Site 2))ᶜ).Reachable
      ⟨x,hx⟩ ⟨z,fun h => hz (JointFiniteComponent.component_subset U b h)⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z e p ih =>
    by_cases hxU : x ∈ U
    · have hy : y ∉ JointFiniteComponent.componentSites U b := by
        intro hyD
        exact hx (JointFiniteComponent.neighbor_in_component U b y x hyD hxU e.symm)
      exact (SimpleGraph.Adj.reachable
        (show ((lattice 2).induce (JointFiniteComponent.componentSites U b : Set (Site 2))ᶜ).Adj
          ⟨x,hx⟩ ⟨y,hy⟩ from e)).trans (ih hz hy)
    · let f : (lattice 2).induce (U : Set (Site 2))ᶜ →g
          (lattice 2).induce (JointFiniteComponent.componentSites U b : Set (Site 2))ᶜ :=
        { toFun := fun v => ⟨v.val, fun hv => v.property
            (JointFiniteComponent.component_subset U b hv)⟩
          map_rel' := fun h => h }
      exact (hS.preconnected ⟨x,hxU⟩ ⟨z,hz⟩).map f

theorem component_complement_connected (U : Finset (Site 2)) (b : U)
    (hS : ((lattice 2).induce (U : Set (Site 2))ᶜ).Connected) :
    ((lattice 2).induce (JointFiniteComponent.componentSites U b : Set (Site 2))ᶜ).Connected := by
  obtain ⟨z,hz⟩ := hS.nonempty
  have hzD : z ∉ JointFiniteComponent.componentSites U b :=
    fun h => hz (JointFiniteComponent.component_subset U b h)
  have hr (x : Site 2) (hx : x ∉ JointFiniteComponent.componentSites U b) :
      ((lattice 2).induce (JointFiniteComponent.componentSites U b : Set (Site 2))ᶜ).Reachable
        ⟨x,hx⟩ ⟨z,hzD⟩ := by
    obtain ⟨p⟩ := (Graph.Zd.latticeConnected 2).preconnected x z
    exact walk_to_removed U b hS z hz p hx
  exact { preconnected := fun x y => (hr x.val x.property).trans (hr y.val y.property).symm
          nonempty := ⟨⟨z,hzD⟩⟩ }

theorem boxSites_eq_box (N : ℕ) : (boxSites N : Set (Site 2)) = box 2 N := by
  ext x
  simp only [Finset.mem_coe, mem_box_sites, FiniteWired.inBox, box, Set.mem_setOf_eq, abs_le]

/-- The zero roots meet the exterior, so their union is the actual connected blocker. -/
theorem blocker_connected (r : ℕ) (hr : 1 ≤ r) (A : Set (Site 2))
    (hA : ((lattice 2).induce A).Connected)
    (hfar : ∃ x ∈ A, 2*r ≤ siteRadius 0 x) :
    ((lattice 2).induce (A ∪ (boxSites (2*r-1) : Set (Site 2))ᶜ)).Connected := by
  obtain ⟨x,hx,hfar⟩ := hfar
  have hxout : x ∉ boxSites (2*r-1) := by
    intro hbox
    have hrad : siteRadius 0 x ≤ 2*r-1 := by
      apply (siteRadius_le_iff _ _ _).mpr
      intro i
      simpa only [Pi.zero_apply,sub_zero,abs_le] using (mem_box_sites _ _).mp hbox i
    omega
  exact SimpleGraph.induce_union_connected hA.preconnected
    (by rw [boxSites_eq_box]; exact (JointExterior.exterior_connected _).preconnected)
    ⟨x,hx,hxout⟩

theorem filtered_box_complement_connected (r : ℕ) (hr : 1 ≤ r) (A : Set (Site 2))
    (hA : ((lattice 2).induce A).Connected)
    (hfar : ∃ x ∈ A, 2*r ≤ siteRadius 0 x) :
    ((lattice 2).induce (((boxSites (2*r-1)).filter (fun x => x ∉ A)) : Set (Site 2))ᶜ).Connected := by
  have he : ((((boxSites (2*r-1)).filter (fun x => x ∉ A)) : Set (Site 2))ᶜ) =
      A ∪ (boxSites (2*r-1) : Set (Site 2))ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_filter, Set.mem_union]
    tauto
  rw [he]
  exact blocker_connected r hr A hA hfar

end
end LocalComplement
