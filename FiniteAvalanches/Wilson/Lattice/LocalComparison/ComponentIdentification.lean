import FiniteAvalanches.Wilson.Lattice.LocalComparison.FullContacts

set_option autoImplicit false
namespace LocalComponentIdentification
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- The constructor's proved connectedness and neighbor closure identify D as the actual component. -/
theorem component_eq (N : ℕ) (A : Set (Site 2)) (b : Site 2) (D : Finset (Site 2))
    (hD : ((lattice 2).induce (D : Set (Site 2))).Connected) (hbD : b ∈ D)
    (hDB : (D : Set (Site 2)) ⊆ (boxSites N : Set (Site 2)))
    (hA : A ⊆ (D : Set (Site 2))ᶜ)
    (hExit : ∀ x ∈ D, ∀ z, z ∉ D → z ∉ A → (lattice 2).Adj x z → z ∉ boxSites N) :
    ∃ hbU : b ∈ (boxSites N).filter (fun x => x ∉ A),
      D = JointFiniteComponent.componentSites ((boxSites N).filter (fun x => x ∉ A)) ⟨b,hbU⟩ := by
  let U := (boxSites N).filter (fun x => x ∉ A)
  have hDU : D ⊆ U := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hDB hx,fun hxA => hA hxA hx⟩
  let bU : U := ⟨b,hDU hbD⟩
  refine ⟨hDU hbD,Finset.Subset.antisymm
    (JointFiniteComponent.connected_subset_component U D bU hD hDU hbD) ?_⟩
  have hstay {u v : U} (p : ((lattice 2).induce (U : Set (Site 2))).Walk u v)
      (hu : u.val ∈ D) : v.val ∈ D := by
    induction p with
    | nil => exact hu
    | @cons u w v e p ih =>
      apply ih
      by_contra hw
      exact hExit u.val hu w.val hw (Finset.mem_filter.mp w.property).2 e
        (Finset.mem_filter.mp w.property).1
  intro x hx
  obtain ⟨hxU,hxC⟩ := (JointFiniteComponent.mem_componentSites U bU x).mp hx
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff,SimpleGraph.ConnectedComponent.eq] at hxC
  obtain ⟨p⟩ := hxC.symm
  exact hstay p hbD

end
end LocalComponentIdentification
