import FiniteAvalanches.Support.Plane.TreePaths

/-!
# Splicing disjoint path stars

An access path may meet its own branch several times. Cutting at the first
meeting and extracting the path in the resulting arc tree gives a simple branch.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Two simple paths with a common endpoint contain a simple path between their
other endpoints whenever the initial point of the second path avoids the first. -/
theorem exists_injective_path_in_union {r b x : ℝ × ℝ}
    (p : Path b r) (w : Path x b) (hp : Function.Injective p)
    (hw : Function.Injective w) (hx : x ∉ range p) :
    ∃ q : Path r x, Function.Injective q ∧ range q ⊆ range p ∪ range w := by
  have htree : IsFiniteArcTree r (range p) := by
    have ht := IsFiniteArcTree.attach p
      (IsFiniteArcTree.singleton : IsFiniteArcTree r {r}) hp (by
        exact inter_eq_right.mpr (singleton_subset_iff.mpr p.target_mem_range))
    simpa only [union_eq_left.mpr (singleton_subset_iff.mpr p.target_mem_range)] using ht
  obtain ⟨z, _, a, ha, hasub, hameet⟩ :=
    exists_initial_path_first_hit w hw (isCompact_range p.continuous).isClosed hx p.source_mem_range
  have ht : IsFiniteArcTree r (range a ∪ range p) := htree.attach a ha hameet
  have hr : r ∈ range a ∪ range p := Or.inr p.target_mem_range
  have hxm : x ∈ range a ∪ range p := Or.inl a.source_mem_range
  have hrx : r ≠ x := fun heq => hx (heq ▸ p.target_mem_range)
  obtain ⟨q, hq, hqsub⟩ := ht.exists_injective_path hr hxm hrx
  exact ⟨q, hq, hqsub.trans (union_subset_union hasub (Subset.refl _)) |>.trans (by
    rw [union_comm])⟩

/-- Pairwise disjoint access paths can be spliced into a disjoint star when each
access avoids every other branch, even if it overlaps its own branch. -/
theorem exists_disjoint_star_of_spliced_paths {ι : Type*} (s : Finset ι)
    {r : ℝ × ℝ} {b x : ι → ℝ × ℝ}
    (p : ∀ i, Path (b i) r) (w : ∀ i, Path (x i) (b i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hw : ∀ i ∈ s, Function.Injective (w i))
    (hx : ∀ i ∈ s, x i ∉ range (p i))
    (hpp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (p i) ∩ range (p j) = {r})
    (hww : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (w i)) (range (w j)))
    (hwp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (w i)) (range (p j))) :
    ∃ q : ∀ i, Path r (x i),
      (∀ i ∈ s, Function.Injective (q i)) ∧
      (∀ i ∈ s, range (q i) ⊆ range (p i) ∪ range (w i)) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (q i) ∩ range (q j) = {r}) := by
  classical
  have hex : ∀ i, ∃ q : Path r (x i), i ∈ s →
      Function.Injective q ∧ range q ⊆ range (p i) ∪ range (w i) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨q, hq, hsub⟩ := exists_injective_path_in_union (p i) (w i)
        (hp i hi) (hw i hi) (hx i hi)
      exact ⟨q, fun _ => ⟨hq, hsub⟩⟩
    · exact ⟨Path.segment r (x i), fun h => (hi h).elim⟩
  choose q hq using hex
  refine ⟨q, fun i hi => (hq i hi).1, fun i hi => (hq i hi).2, ?_⟩
  intro i hi j hj hij
  apply subset_antisymm
  · intro z hz
    rcases (hq i hi).2 hz.1 with hpi | hwi
    · rcases (hq j hj).2 hz.2 with hpj | hwj
      · rw [← hpp i hi j hj hij]
        exact ⟨hpi, hpj⟩
      · exact (disjoint_left.mp (hwp j hj i hi hij.symm) hwj hpi).elim
    · rcases (hq j hj).2 hz.2 with hpj | hwj
      · exact (disjoint_left.mp (hwp i hi j hj hij) hwi hpj).elim
      · exact (disjoint_left.mp (hww i hi j hj hij) hwi hwj).elim
  · exact singleton_subset_iff.mpr ⟨(q i).source_mem_range, (q j).source_mem_range⟩

end FiniteAvalanches.Electrical.StatementGeometry
