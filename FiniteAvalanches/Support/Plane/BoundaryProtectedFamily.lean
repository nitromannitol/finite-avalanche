import FiniteAvalanches.Support.Plane.BoundaryRootTails

/-!
# Boundary extension with protected root stubs

A finite family of root stubs can be protected while a boundary access is
attached to an arc tree.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A finite family of arcs meeting a tree and each other only at its root
can be attached to the tree. -/
theorem IsFiniteArcTree.attach_finset_root_paths
    {ι : Type*} {r : ℝ × ℝ} {K : Set (ℝ × ℝ)} (hK : IsFiniteArcTree r K)
    (hr : r ∈ K) (s : Finset ι) {x : ι → ℝ × ℝ} (p : ∀ i, Path (x i) r)
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hpK : ∀ i ∈ s, range (p i) ∩ K = {r})
    (hpp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (p i) ∩ range (p j) = {r}) :
    IsFiniteArcTree r (K ∪ ⋃ i ∈ s, range (p i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hK
  | @insert i s hi ih =>
      have htree := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
        (fun j hj => hpK j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hne => hpp j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) hne)
      have hmeet : range (p i) ∩ (K ∪ ⋃ j ∈ s, range (p j)) = {r} := by
        apply subset_antisymm
        · rintro z ⟨hzi, hzk | hzu⟩
          · exact (hpK i (Finset.mem_insert_self i s)).le ⟨hzi, hzk⟩
          · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzu
            exact (hpp i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
              (fun h => hi (h ▸ hj))).le ⟨hzi, hzj⟩
        · exact singleton_subset_iff.mpr ⟨(p i).target_mem_range, Or.inl hr⟩
      have ht := htree.attach (p i) (hp i (Finset.mem_insert_self i s)) hmeet
      convert ht using 1
      ext z
      simp only [mem_union, mem_iUnion, Finset.mem_insert]
      aesop

/-- An auxiliary stub allows an access path to be attached while every stub
in a finite protected family remains disjoint from the enlarged tree away from
the root. -/
theorem exists_boundary_path_to_root_with_protected_family
    {ι : Type*} {U K S : Set (ℝ × ℝ)} {r q x b : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hK : IsFiniteArcTree r K)
    (hKU : K ⊆ U) (hS : S.Finite) (s : Finset ι)
    {z : ι → ℝ × ℝ} (p : ∀ i, Path (z i) r)
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hpU : ∀ i ∈ s, range (p i) ⊆ U \ S)
    (hpK : ∀ i ∈ s, range (p i) ∩ K = {r})
    (hpp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (p i) ∩ range (p j) = {r})
    (v : Path q r) (hv : Function.Injective v) (hvU : range v ⊆ U \ S)
    (hvK : range v ∩ K = {r})
    (hvp : ∀ i ∈ s, range v ∩ range (p i) = {r})
    (hq : q ∉ K ∪ ⋃ i ∈ s, range (p i))
    (a : Path x b) (ha : Function.Injective a)
    (haU : ∀ t : unitInterval, t ≠ 1 → a t ∈ U) (hb : b ∉ U)
    (haS : Disjoint (range a) S)
    (haK : Disjoint (range a) ((K ∪ ⋃ i ∈ s, range (p i)) ∪ range v)) :
    ∃ w : Path r b, Function.Injective w ∧ range w ⊆ (U ∪ {b}) \ S ∧
      IsFiniteArcTree r (range w ∪ K) ∧
      (∀ i ∈ s, range (p i) ∩ (range w ∪ K) = {r}) ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = a ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩ := by
  have hrK : r ∈ K := by
    have h : r ∈ range v ∩ K := by rw [hvK]; exact mem_singleton r
    exact h.2
  let L := K ∪ ⋃ i ∈ s, range (p i)
  have hL : IsFiniteArcTree r L := hK.attach_finset_root_paths hrK s p hp hpK hpp
  have hLU : L ⊆ U := union_subset hKU (iUnion₂_subset (fun i hi =>
    (hpU i hi).trans (sdiff_subset)))
  have hvL : range v ∩ L = {r} := by
    apply subset_antisymm
    · rintro y ⟨hy, hyK | hyP⟩
      · exact hvK.le ⟨hy, hyK⟩
      · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hyP
        exact (hvp i hi).le ⟨hy, hyi⟩
    · exact singleton_subset_iff.mpr ⟨v.target_mem_range, Or.inl hrK⟩
  obtain ⟨w, hw, hwU, hwL, u, hu, htail⟩ :=
    exists_boundary_path_to_root_of_stub_with_tail hU hconn hL hLU hS v hv hvU hvL hq
      a ha haU hb haS haK
  have hwK : range w ∩ K = {r} := by
    apply subset_antisymm
    · intro y hy
      exact hwL.le ⟨hy.1, Or.inl hy.2⟩
    · exact singleton_subset_iff.mpr ⟨w.source_mem_range, hrK⟩
  have hwrev : Function.Injective w.symm := by
    intro t t' h
    exact unitInterval.symm_involutive.injective (hw h)
  have htree : IsFiniteArcTree r (range w ∪ K) := by
    have ht := hK.attach w.symm hwrev (by simpa only [Path.symm_range, Path.source] using hwK)
    simpa only [Path.symm_range] using ht
  refine ⟨w, hw, hwU, htree, ?_, u, hu, htail⟩
  intro i hi
  apply subset_antisymm
  · rintro y ⟨hyi, hyw | hyK⟩
    · exact hwL.le ⟨hyw, Or.inr (mem_iUnion₂.mpr ⟨i, hi, hyi⟩)⟩
    · exact (hpK i hi).le ⟨hyi, hyK⟩
  · exact singleton_subset_iff.mpr ⟨(p i).target_mem_range, Or.inl w.source_mem_range⟩

end FiniteAvalanches.Electrical.StatementGeometry
