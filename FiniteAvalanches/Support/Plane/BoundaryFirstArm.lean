import FiniteAvalanches.Support.Plane.BoundaryStubSupply
import FiniteAvalanches.Support.Plane.BoundaryProtectedAccess

/-!
# An initial boundary arm with reserved stubs

The first arm of a boundary family can be attached while retaining any
prescribed finite number of separated stubs at its root.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- One boundary access admits an arm whose root retains any requested number
of separated stubs, while the arm avoids the remaining accesses. -/
theorem exists_first_boundary_arm_with_stubs
    {ι : Type*} [DecidableEq ι] {U S : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (a : ∀ i, Path (x i) (y i))
    (ha : ∀ i ∈ s, Function.Injective (a i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (a i) ∩ U) (range (a j)))
    (haU : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → a i t ∈ U)
    (hy : ∀ i ∈ s, y i ∉ U) (hS : S.Finite)
    (haS : ∀ i ∈ s, Disjoint (range (a i)) S)
    {i : ι} (hi : i ∈ s) (n : ℕ) :
    ∃ (r : ℝ × ℝ) (q : Fin n → ℝ × ℝ)
      (p : ∀ j, Path (q j) r) (w : Path r (y i)),
      r ∈ (U \ ⋃ j ∈ s, range (a j)) \ S ∧
      Function.Injective w ∧ range w ⊆ (U ∪ {y i}) \ S ∧
      (∀ j, q j ≠ r ∧ Function.Injective (p j) ∧
        range (p j) ⊆ (U \ ⋃ k ∈ s, range (a k)) \ S ∧
        range (p j) ∩ range w = {r}) ∧
      (∀ j k, j ≠ k → range (p j) ∩ range (p k) = {r}) ∧
      Disjoint (range w ∩ U) (⋃ j ∈ s.erase i, range (a j)) ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (v : unitInterval) (hv : ((u : ℝ) + 1) / 2 ≤ (v : ℝ)),
          w v = a i ⟨2 * (v : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [v.property.2]⟩ := by
  classical
  obtain ⟨r, q, p, hr, hqr, hp, hpU, hpair⟩ :=
    exists_root_stub_supply_avoiding_paths hU hUne hS s a ha (n + 1)
  let q' : Fin n → ℝ × ℝ := fun j => q j.castSucc
  let p' : ∀ j, Path (q' j) r := fun j => p j.castSucc
  let v := p (Fin.last n)
  have hr' : r ∈ (U \ ⋃ j ∈ s, range (a j)) \ S := by
    exact ⟨⟨hr.1, fun h => hr.2 (Or.inr h)⟩, fun h => hr.2 (Or.inl h)⟩
  have hpsub : ∀ j, range (p' j) ⊆ (U \ ⋃ k ∈ s, range (a k)) \ S := by
    intro j z hz
    have hh := hpU j.castSucc hz
    exact ⟨⟨hh.1, fun h => hh.2 (Or.inr h)⟩, fun h => hh.2 (Or.inl h)⟩
  have hvsub : range v ⊆ (U \ ⋃ k ∈ s, range (a k)) \ S := by
    intro z hz
    have hh := hpU (Fin.last n) hz
    exact ⟨⟨hh.1, fun h => hh.2 (Or.inr h)⟩, fun h => hh.2 (Or.inl h)⟩
  have hpsingle : ∀ j, range (p' j) ∩ {r} = {r} := by
    intro j
    exact inter_eq_right.mpr (singleton_subset_iff.mpr (p' j).target_mem_range)
  have hvsingle : range v ∩ {r} = {r} :=
    inter_eq_right.mpr (singleton_subset_iff.mpr v.target_mem_range)
  have hneq : ∀ j : Fin n, Fin.last n ≠ j.castSucc := by
    intro j h
    have hh := congrArg Fin.val h
    exact (Nat.ne_of_lt j.isLt) hh.symm
  have hvp : ∀ j, range v ∩ range (p' j) = {r} := by
    intro j
    exact hpair (Fin.last n) j.castSucc (hneq j)
  have hq : q (Fin.last n) ∉ {r} ∪ ⋃ j ∈ (Finset.univ : Finset (Fin n)), range (p' j) := by
    rintro (h | h)
    · exact hqr (Fin.last n) (mem_singleton_iff.mp h)
    · obtain ⟨j, _, hj⟩ := mem_iUnion₂.mp h
      have hmeet : q (Fin.last n) ∈ range v ∩ range (p' j) := ⟨v.source_mem_range, hj⟩
      rw [hvp j] at hmeet
      exact hqr (Fin.last n) (mem_singleton_iff.mp hmeet)
  obtain ⟨w, hw, hwU, _, hprotect, havoid, u, hu, htail⟩ :=
    exists_boundary_path_with_protected_stubs_avoiding_accesses hU hconn
      (IsFiniteArcTree.singleton : IsFiniteArcTree r {r}) s a ha hd haU hy hS haS
      (singleton_subset_iff.mpr hr'.1) (Finset.univ : Finset (Fin n)) p'
      (fun j _ => hp j.castSucc) (fun j _ => hpsub j) (fun j _ => hpsingle j)
      (fun j _ k _ hjk => hpair j.castSucc k.castSucc (fun h => hjk (Fin.castSucc_injective n h)))
      v (hp (Fin.last n)) hvsub hvsingle (fun j _ => hvp j) hq hi
  refine ⟨r, q', p', w, hr', hw, hwU, ?_, ?_, havoid, u, hu, htail⟩
  · intro j
    refine ⟨hqr j.castSucc, hp j.castSucc, hpsub j, ?_⟩
    have h := hprotect j (Finset.mem_univ j)
    apply subset_antisymm
    · exact (inter_subset_inter_right _ subset_union_left).trans h.le
    · exact singleton_subset_iff.mpr ⟨(p' j).target_mem_range, w.source_mem_range⟩
  · intro j k hjk
    exact hpair j.castSucc k.castSucc (fun h => hjk (Fin.castSucc_injective n h))

end FiniteAvalanches.Electrical.StatementGeometry
