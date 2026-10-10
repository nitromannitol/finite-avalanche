import FiniteAvalanches.Wilson.Lattice.LocalComparison.StoppedPath
import FiniteAvalanches.Wilson.Lattice.LocalComparison.EnergyUpper

set_option autoImplicit false
namespace LocalSourceNetwork
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

/-- Construct the actual stopped path, domain, and distinguished source copy. -/
theorem exists_network (r : ℕ) (hr : 10^30 ≤ r) (R : RootPair)
    (h0 : (0 : Site 2) ∈ R.zero) (b : Site 2) (hb : b ∈ R.one)
    (hadj : (lattice 2).Adj 0 b)
    (hZero : ((lattice 2).induce R.zero).Connected)
    (hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius 0 x)
    (hOne : ((lattice 2).induce R.one).Connected)
    (hmeet : ∃ y ∈ R.one, siteRadius 0 y = r) :
    ∃ (D : Finset (Site 2)) (P : OneSet D)
      (hD : ((lattice 2).induce (D : Set (Site 2))).Connected)
      (marked : MarkedCopy D P) (y : Site 2) (q : (lattice 2).Walk b y),
      ((lattice 2).induce (D : Set (Site 2))ᶜ).Connected ∧
      ((lattice 2).induce (P.val.image Subtype.val : Set (Site 2))).Connected ∧
      P.val.image Subtype.val = q.support.toFinset ∧ q.IsPath ∧ siteRadius 0 y = r ∧
      (∀ x ∈ q.support, x ∈ R.one ∧ x ∈ boxSites r) ∧
      (∀ x ∈ q.support, x ≠ y → siteRadius 0 x < r) ∧
      ((originalA marked.val = 0 ∧ originalB marked.val = b) ∨
        (originalA marked.val = b ∧ originalB marked.val = 0)) ∧
      b ∈ D ∧ (0 : Site 2) ∉ D ∧ R.zero ⊆ (D : Set (Site 2))ᶜ ∧
      (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)) ∧
      (latticeExits D).card-1 ≤ r^3 ∧
      energy (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked) ≤
        ((latticeExits D).card-1 : ℕ) ∧
      ∀ x ∈ D, ∀ z, z ∉ D → z ∉ R.zero → (lattice 2).Adj x z → z ∉ boxSites (2*r-1) := by
  have hr1 : 1 ≤ r := (by norm_num : 1 ≤ 10^30).trans hr
  have hr100 : 100 ≤ r := (by norm_num : 100 ≤ 10^30).trans hr
  obtain ⟨y,q,hq,hy,hqroots,hqfirst⟩ := LocalStoppedPath.exists_stopped_path r hr1 R b hb hadj hOne hmeet
  let Q := q.support.toFinset
  have hQc : ((lattice 2).induce (Q : Set (Site 2))).Connected := by
    have he : (Q : Set (Site 2)) = {x | x ∈ q.support} := by
      ext x; exact List.mem_toFinset
    rw [he]
    exact q.connected_induce_support
  have hbQ : b ∈ Q := List.mem_toFinset.mpr q.start_mem_support
  have hQne : Q.Nonempty := ⟨b,hbQ⟩
  have hbBox : b ∈ boxSites (2*r-1) := by
    have hbr := (hqroots b q.start_mem_support).2
    apply (mem_box_sites _ _).mpr
    intro i
    have hc := (mem_box_sites _ _).mp hbr i
    constructor <;> omega
  have hbzero : b ∉ R.zero := fun hz => Set.disjoint_left.mp R.disjoint hz hb
  let U := (boxSites (2*r-1)).filter (fun x => x ∉ R.zero)
  let bU : U := ⟨b,Finset.mem_filter.mpr ⟨hbBox,hbzero⟩⟩
  let D := JointFiniteComponent.componentSites U bU
  have hDU : D ⊆ U := JointFiniteComponent.component_subset U bU
  have hQU : Q ⊆ U := by
    intro x hx
    obtain ⟨hxOne,hxBox⟩ := hqroots x (List.mem_toFinset.mp hx)
    refine Finset.mem_filter.mpr ⟨?_, fun hz => Set.disjoint_left.mp R.disjoint hz hxOne⟩
    apply (mem_box_sites _ _).mpr
    intro i
    have hc := (mem_box_sites _ _).mp hxBox i
    constructor <;> omega
  have hQD : Q ⊆ D := JointFiniteComponent.connected_subset_component U Q bU hQc hQU hbQ
  let P := LocalStoppedPath.oneSet D Q hQD hQne
  have hPQ : P.val.image Subtype.val = Q := LocalStoppedPath.oneSet_image D Q hQD hQne
  have hD : ((lattice 2).induce (D : Set (Site 2))).Connected :=
    JointFiniteComponent.component_connected U bU
  have hDc : ((lattice 2).induce (D : Set (Site 2))ᶜ).Connected :=
    LocalComplement.component_complement_connected U bU
      (LocalComplement.filtered_box_complement_connected r hr1 R.zero hZero hfar)
  have h0D : (0 : Site 2) ∉ D := fun hx => (Finset.mem_filter.mp (hDU hx)).2 h0
  have hbP : b ∈ P.val.image Subtype.val := hPQ ▸ hbQ
  obtain ⟨marked,hmark⟩ := LocalStoppedPath.exists_origin_mark D P h0D b hbP hadj
  have hDB : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)) :=
    fun x hx => (Finset.mem_filter.mp (hDU hx)).1
  refine ⟨D,P,hD,marked,y,q,hDc,?_,hPQ,hq,hy,hqroots,hqfirst,hmark,
    hQD hbQ,h0D,?_,hDB,JointBoundarySize.reference_boundary_le_cube r hr100 D hDB,
    LocalEnergyUpper.voltage_energy_le_original_exits D P hD marked,?_⟩
  · rw [hPQ]; exact hQc
  · intro x hx hxD
    exact (Finset.mem_filter.mp (hDU hxD)).2 hx
  · intro x hx z hzD hzzero hxz
    exact JointFiniteComponent.unwanted_neighbor_outside (2*r-1) R.zero bU x z hx hzD hzzero hxz

end
end LocalSourceNetwork
