import FiniteAvalanches.Support.Plane.BoundaryFirstArm

/-!
# The complement of an initial boundary arm

The first boundary arm, the remaining accesses, and the reserved stubs have
connected complement inside the original region.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Removing a simple boundary access preserves preconnectedness. -/
theorem isPreconnected_sdiff_boundary_path
    {U : Set (ℝ × ℝ)} {x y : ℝ × ℝ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (p : Path x y) (hp : Function.Injective p)
    (hinside : ∀ t : unitInterval, t ≠ 1 → p t ∈ U) (hy : y ∉ U) :
    IsPreconnected (U \ range p) := by
  have h := isPreconnected_sdiff_finset_paths_of_disjoint_inside hU hconn
    (Finset.univ : Finset Unit) (fun _ => p) (by simpa using hp)
    (by simp) (by simpa using isPreconnected_range_inter_compl_of_mem_except_target p hinside hy)
  simpa only [Finset.mem_univ, iUnion_true, iUnion_const] using h

/-- An initial boundary arm can be chosen so that removing it, all unused
accesses, and the reserved stubs leaves a preconnected region. -/
theorem exists_first_boundary_arm_with_connected_complement
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
      (∃ u : unitInterval, u ≠ 1 ∧
        ∀ (v : unitInterval) (hv : ((u : ℝ) + 1) / 2 ≤ (v : ℝ)),
          w v = a i ⟨2 * (v : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [v.property.2]⟩) ∧
      IsPreconnected (((U \ range w) \ (⋃ j ∈ s.erase i, range (a j))) \
        (⋃ j, range (p j))) := by
  classical
  obtain ⟨r, q, p, w, hr, hw, hwU, hp, hpair, havoid, htail⟩ :=
    exists_first_boundary_arm_with_stubs hU hconn hUne s a ha hd haU hy hS haS hi n
  refine ⟨r, q, p, w, hr, hw, hwU, hp, hpair, havoid, htail, ?_⟩
  have hwinside : ∀ t : unitInterval, t ≠ 1 → w t ∈ U := by
    intro t ht
    rcases (hwU ⟨t, rfl⟩).1 with hz | hz
    · exact hz
    · have heq : w t = w 1 := (mem_singleton_iff.mp hz).trans w.target.symm
      exact (ht (hw heq)).elim
  let W := U \ range w
  have hW : IsOpen W := hU.sdiff (isCompact_range w.continuous).isClosed
  have hWconn : IsPreconnected W :=
    isPreconnected_sdiff_boundary_path hU hconn w hw hwinside (hy i hi)
  have haW : ∀ j ∈ s.erase i, ∀ t : unitInterval, t ≠ 1 → a j t ∈ W := by
    intro j hj t ht
    have hjs : j ∈ s := (Finset.mem_erase.mp hj).2
    refine ⟨haU j hjs t ht, ?_⟩
    intro hz
    exact disjoint_left.mp havoid ⟨hz, haU j hjs t ht⟩
      (mem_iUnion₂.mpr ⟨j, hj, ⟨t, rfl⟩⟩)
  have hyW : ∀ j ∈ s.erase i, y j ∉ W := by
    intro j hj hz
    exact hy j (Finset.mem_erase.mp hj).2 hz.1
  have hconn' : IsPreconnected (W \ ⋃ j ∈ s.erase i, range (a j)) := by
    apply isPreconnected_sdiff_finset_paths_of_disjoint_inside hW hWconn (s.erase i) a
    · intro j hj
      exact ha j (Finset.mem_erase.mp hj).2
    · intro j hj k hk hjk
      apply (hd j (Finset.mem_erase.mp hj).2 k (Finset.mem_erase.mp hk).2 hjk).mono_left
      exact inter_subset_inter_right _ sdiff_subset
    · intro j hj
      exact isPreconnected_range_inter_compl_of_mem_except_target (a j) (haW j hj) (hyW j hj)
  let Z := W \ ⋃ j ∈ s.erase i, range (a j)
  have hZ : IsOpen Z := hW.sdiff
    (s.erase i |>.isCompact_biUnion (fun j _ => isCompact_range (a j).continuous)).isClosed
  have hrZ : r ∉ Z := fun hz => hz.1.2 w.source_mem_range
  have hpZ : ∀ j, ∀ t : unitInterval, t ≠ 1 → p j t ∈ Z := by
    intro j t ht
    have hmem := (hp j).2.2.1 ⟨t, rfl⟩
    refine ⟨⟨hmem.1.1, ?_⟩, ?_⟩
    · intro hz
      have h : p j t ∈ range (p j) ∩ range w := ⟨⟨t, rfl⟩, hz⟩
      rw [(hp j).2.2.2] at h
      have heq : p j t = p j 1 := (mem_singleton_iff.mp h).trans (p j).target.symm
      exact ht ((hp j).2.1 heq)
    · intro hz
      apply hmem.1.2
      obtain ⟨k, hk, h⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨k, (Finset.mem_erase.mp hk).2, h⟩
  have hresult := isPreconnected_sdiff_finset_paths_of_disjoint_inside hZ hconn'
    (Finset.univ : Finset (Fin n)) p
    (fun j _ => (hp j).2.1)
    (by
      intro j _ k _ hjk
      apply disjoint_left.mpr
      rintro z ⟨hz, hzZ⟩ hzk
      have h : z ∈ range (p j) ∩ range (p k) := ⟨hz, hzk⟩
      rw [hpair j k hjk] at h
      exact hrZ ((mem_singleton_iff.mp h) ▸ hzZ))
    (fun j _ => isPreconnected_range_inter_compl_of_mem_except_target (p j) (hpZ j) hrZ)
  simpa [Z, W] using hresult

end FiniteAvalanches.Electrical.StatementGeometry
