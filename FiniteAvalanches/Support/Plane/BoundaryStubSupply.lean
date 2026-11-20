import FiniteAvalanches.Support.Plane.RootStubSupply
import FiniteAvalanches.Support.Plane.EndpointLocalConnectivity

/-!
# Root stubs avoiding boundary accesses

A root and an arbitrary finite supply of stubs can be chosen in a nonempty
open plane set while avoiding finitely many simple paths and points.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A nonempty open plane set contains a finite root-stub family disjoint
from prescribed simple paths and a finite set. -/
theorem exists_root_stub_supply_avoiding_paths
    {ι : Type*} {U S : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (hS : S.Finite) (s : Finset ι) {x y : ι → ℝ × ℝ} (a : ∀ i, Path (x i) (y i))
    (ha : ∀ i ∈ s, Function.Injective (a i)) (n : ℕ) :
    ∃ (r : ℝ × ℝ) (q : Fin n → ℝ × ℝ) (p : ∀ i, Path (q i) r),
      r ∈ U \ (S ∪ ⋃ i ∈ s, range (a i)) ∧
      (∀ i, q i ≠ r) ∧
      (∀ i, Function.Injective (p i)) ∧
      (∀ i, range (p i) ⊆ U \ (S ∪ ⋃ i ∈ s, range (a i))) ∧
      (∀ i j, i ≠ j → range (p i) ∩ range (p j) = {r}) := by
  classical
  have hdense : Dense (⋃ i ∈ s, range (a i))ᶜ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have hiDense := dense_compl_range_injective_path (a i) (ha i (Finset.mem_insert_self i s))
      have hiOpen : IsOpen (range (a i))ᶜ := (isCompact_range (a i).continuous).isClosed.isOpen_compl
      have hsDense := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.mem_insert, iUnion_or, iUnion_union_distrib,
        iUnion_iUnion_eq_left, compl_union] using hiDense.inter_of_isOpen_left hsDense hiOpen
  have hclosed : IsClosed (⋃ i ∈ s, range (a i)) :=
    ((s.isCompact_biUnion fun i _ => isCompact_range (a i).continuous)).isClosed
  have hSdense : Dense Sᶜ := by
    rw [Set.compl_eq_univ_sdiff]
    exact dense_univ.sdiff_finite hS
  have hd : Dense (S ∪ ⋃ i ∈ s, range (a i))ᶜ := by
    rw [compl_union]
    exact hSdense.inter_of_isOpen_right hdense hclosed.isOpen_compl
  obtain ⟨r, hrU, hravoid⟩ := hd.inter_open_nonempty U hU hUne
  let W := U \ (S ∪ ⋃ i ∈ s, range (a i))
  have hW : IsOpen W := hU.sdiff (hS.isClosed.union hclosed)
  have hr : r ∈ W := ⟨hrU, hravoid⟩
  obtain ⟨q, p, hqr, hp, hpW, hpair⟩ := exists_root_stub_supply hW hr n
  exact ⟨r, q, p, hr, hqr, hp, hpW, hpair⟩

end FiniteAvalanches.Electrical.StatementGeometry
