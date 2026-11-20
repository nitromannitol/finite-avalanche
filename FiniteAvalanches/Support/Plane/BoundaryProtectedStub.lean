import FiniteAvalanches.Support.Plane.BoundaryRootTails

/-!
# Boundary extension with a protected root stub

A boundary access can be attached to a rooted arc tree while retaining both its
terminal parametrization and a second stub at the root.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Two stubs at a root allow a boundary access to be attached while one stub
remains disjoint from the enlarged tree away from the root. -/
theorem exists_boundary_path_to_root_with_protected_stub
    {U K S : Set (ℝ × ℝ)} {r q q' x b : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hK : IsFiniteArcTree r K)
    (hKU : K ⊆ U) (hS : S.Finite)
    (p : Path q r) (p' : Path q' r) (hp : Function.Injective p)
    (hp' : Function.Injective p') (hpU : range p ⊆ U \ S)
    (hp'U : range p' ⊆ U \ S) (hpK : range p ∩ K = {r})
    (hp'K : range p' ∩ K = {r}) (hpp' : range p ∩ range p' = {r})
    (hq : q ∉ K ∪ range p')
    (a : Path x b) (ha : Function.Injective a)
    (haU : ∀ t : unitInterval, t ≠ 1 → a t ∈ U) (hb : b ∉ U)
    (haS : Disjoint (range a) S)
    (haK : Disjoint (range a) (K ∪ range p ∪ range p')) :
    ∃ w : Path r b, Function.Injective w ∧ range w ⊆ (U ∪ {b}) \ S ∧
      IsFiniteArcTree r (range w ∪ K) ∧
      range p' ∩ (range w ∪ K) = {r} ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = a ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩ := by
  let L := range p' ∪ K
  have hL : IsFiniteArcTree r L := hK.attach p' hp' hp'K
  have hLU : L ⊆ U := union_subset (fun z hz => (hp'U hz).1) hKU
  have hpL : range p ∩ L = {r} := by
    simp only [L, inter_union_distrib_left, hpp', hpK, union_self]
  have hqL : q ∉ L := by simpa only [L, union_comm] using hq
  have haL : Disjoint (range a) (L ∪ range p) := by
    simpa only [L, union_assoc, union_comm, union_left_comm] using haK
  obtain ⟨w, hw, hwU, hwL, u, hu, htail⟩ :=
    exists_boundary_path_to_root_of_stub_with_tail hU hconn hL hLU hS p hp hpU hpL hqL
      a ha haU hb haS haL
  have hrK : r ∈ K := by
    have h : r ∈ range p ∩ K := by rw [hpK]; exact mem_singleton r
    exact h.2
  have hwK : range w ∩ K = {r} := by
    apply subset_antisymm
    · intro z hz
      exact hwL.le ⟨hz.1, Or.inr hz.2⟩
    · exact singleton_subset_iff.mpr ⟨w.source_mem_range, hrK⟩
  have hwp' : range w ∩ range p' = {r} := by
    apply subset_antisymm
    · intro z hz
      exact hwL.le ⟨hz.1, Or.inl hz.2⟩
    · exact singleton_subset_iff.mpr ⟨w.source_mem_range, p'.target_mem_range⟩
  have hwrev : Function.Injective w.symm := by
    intro s t h
    exact unitInterval.symm_involutive.injective (hw h)
  have htree : IsFiniteArcTree r (range w ∪ K) := by
    have ht := hK.attach w.symm hwrev (by simpa only [Path.symm_range, Path.source] using hwK)
    simpa only [Path.symm_range] using ht
  refine ⟨w, hw, hwU, htree, ?_, u, hu, htail⟩
  simp only [inter_union_distrib_left, inter_comm (range p') (range w), hwp', hp'K, union_self]

end FiniteAvalanches.Electrical.StatementGeometry
