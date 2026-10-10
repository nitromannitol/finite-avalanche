import FiniteAvalanches.Wilson.Lattice.ForestEvents
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false
namespace JointFiniteComponent
open LatticeProb
open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- The actual induced component, returned on the original finite site carrier. -/
def componentSites (U : Finset (Site 2)) (b : U) : Finset (Site 2) :=
  U.filter (fun x => ∃ hx : x ∈ U,
    ((lattice 2).induce (U : Set (Site 2))).connectedComponentMk ⟨x,hx⟩ =
      ((lattice 2).induce (U : Set (Site 2))).connectedComponentMk b)

theorem mem_componentSites (U : Finset (Site 2)) (b : U) (x : Site 2) :
    x ∈ componentSites U b ↔ ∃ hx : x ∈ U,
      ⟨x,hx⟩ ∈ (((lattice 2).induce (U : Set (Site 2))).connectedComponentMk b).supp := by
  simp only [componentSites, Finset.mem_filter, SimpleGraph.ConnectedComponent.mem_supp_iff]
  constructor
  · rintro ⟨_, hx, he⟩
    exact ⟨hx, he⟩
  · rintro ⟨hx, he⟩
    exact ⟨hx, hx, he⟩

theorem component_subset (U : Finset (Site 2)) (b : U) : componentSites U b ⊆ U :=
  Finset.filter_subset _ _

theorem base_mem_component (U : Finset (Site 2)) (b : U) : b.val ∈ componentSites U b :=
  (mem_componentSites U b b.val).mpr ⟨b.property, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

theorem component_connected (U : Finset (Site 2)) (b : U) :
    ((lattice 2).induce (componentSites U b : Set (Site 2))).Connected := by
  let C := ((lattice 2).induce (U : Set (Site 2))).connectedComponentMk b
  let f : C.toSimpleGraph →g (lattice 2).induce (componentSites U b : Set (Site 2)) :=
    { toFun := fun x => ⟨x.val.val, (mem_componentSites U b x.val.val).mpr ⟨x.val.property, x.property⟩⟩
      map_rel' := fun h => h }
  apply C.connected_toSimpleGraph.map f
  intro x
  obtain ⟨hx, hxC⟩ := (mem_componentSites U b x.val).mp x.property
  exact ⟨⟨⟨x.val,hx⟩,hxC⟩, Subtype.ext rfl⟩

theorem connected_subset_component (U P : Finset (Site 2)) (b : U)
    (hP : ((lattice 2).induce (P : Set (Site 2))).Connected)
    (hPU : P ⊆ U) (hb : b.val ∈ P) : P ⊆ componentSites U b := by
  intro x hx
  let f : (lattice 2).induce (P : Set (Site 2)) →g
      (lattice 2).induce (U : Set (Site 2)) :=
    { toFun := fun y => ⟨y.val,hPU y.property⟩
      map_rel' := fun h => h }
  have hr := (hP.preconnected ⟨b.val,hb⟩ ⟨x,hx⟩).map f
  apply (mem_componentSites U b x).mpr
  refine ⟨hPU hx, ?_⟩
  change ((lattice 2).induce (U : Set (Site 2))).connectedComponentMk ⟨x,hPU hx⟩ =
    ((lattice 2).induce (U : Set (Site 2))).connectedComponentMk b
  exact Quot.sound hr.symm

/-- No edge can leave this component and remain in the ambient finite domain. -/
theorem neighbor_in_component (U : Finset (Site 2)) (b : U) (x y : Site 2)
    (hx : x ∈ componentSites U b) (hy : y ∈ U) (hxy : (lattice 2).Adj x y) :
    y ∈ componentSites U b := by
  obtain ⟨hxU, hxC⟩ := (mem_componentSites U b x).mp hx
  apply (mem_componentSites U b y).mpr
  refine ⟨hy, ?_⟩
  exact SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _ hxC
    (show ((lattice 2).induce (U : Set (Site 2))).Adj ⟨x,hxU⟩ ⟨y,hy⟩ from hxy)

/-- The unwanted side of a local-component exit lies outside the actual outer box. -/
theorem unwanted_neighbor_outside (N : ℕ) (A : Set (Site 2))
    (b : (boxSites N).filter (fun x => x ∉ A)) (x y : Site 2)
    (hx : x ∈ componentSites ((boxSites N).filter (fun x => x ∉ A)) b)
    (hyD : y ∉ componentSites ((boxSites N).filter (fun x => x ∉ A)) b)
    (hyA : y ∉ A) (hxy : (lattice 2).Adj x y) : y ∉ boxSites N := by
  intro hyB
  exact hyD (neighbor_in_component _ b x y hx (Finset.mem_filter.mpr ⟨hyB,hyA⟩) hxy)

end
end JointFiniteComponent
