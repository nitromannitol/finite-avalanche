import FiniteAvalanches.Support.Plane.BoundaryPairFamily

/-!
# Small families of boundary arms

Families of at most two boundary accesses admit uniformly parametrized rooted
arms, including the empty family and shared boundary endpoints.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- At most two boundary accesses admit rooted arms with exact terminal speed,
separated except at their root and shared boundary endpoints. -/
theorem exists_boundary_arm_family_of_card_le_two
    {ι : Type*} {U S : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hUne : U.Nonempty) (s : Finset ι) (hcard : s.card ≤ 2) {x y : ι → ℝ × ℝ}
    (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U) (hS : S.Finite)
    (hobs : ∀ i ∈ s, Disjoint (range (p i)) S) :
    ∃ r ∈ U, ∃ w : ∀ i, Path r (y i),
      (∀ i ∈ s, Function.Injective (w i)) ∧
      (∀ i ∈ s, Disjoint (range (w i)) S) ∧
      (∀ i ∈ s, range (w i) ∩ Uᶜ = {y i}) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ z ∈ range (w i) ∩ range (w j),
        z = r ∨ z = y i ∧ y i = y j) ∧
      (∀ i ∈ s, ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w i t = p i ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
  classical
  by_cases htwo : s.card = 2
  · exact exists_boundary_arm_family_of_card_eq_two hU hconn s htwo p hp hd
      hinside hout hS hobs
  have hsmall : s.card ≤ 1 := by omega
  by_cases hempty : s = ∅
  · obtain ⟨r, hr⟩ := hUne
    refine ⟨r, hr, fun i => Path.segment r (y i), ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hempty, Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hs : s = {i} := by
      apply Finset.Subset.antisymm
      · intro j hj
        have hji : j = i := Finset.card_le_one.mp hsmall j hj i hi
        simpa only [Finset.mem_singleton, hji]
      · simpa only [Finset.singleton_subset_iff] using hi
    have htail : range ((p i).subpath 0 1) ⊆ range (p i) := by
      rw [Path.range_subpath_of_le _ _ _ (show (0 : unitInterval) ≤ 1 from bot_le)]
      exact image_subset_range _ _
    obtain ⟨q, hq, hqsub, u, hu, huspeed⟩ :=
      exists_path_with_parametrized_retained_tail (p i) (p i) (hp i hi) (hp i hi)
        (t := 0) (by norm_num) htail
    have hr : x i ∈ U := by simpa only [Path.source] using hinside i hi 0 (by norm_num)
    let arm : ∀ j, Path (x i) (y j) := fun j =>
      if hj : j = i then hj.symm ▸ q else Path.segment (x i) (y j)
    have harm : arm i = q := by simp [arm]
    have hcase : ∀ j ∈ s, j = i := by
      intro j hj
      simpa only [hs, Finset.mem_singleton] using hj
    have hqU : range q ∩ Uᶜ = {y i} := by
      apply subset_antisymm
      · have hpU := range_inter_compl_of_mem_except_target (p i) (hinside i hi) (hout i hi)
        exact (inter_subset_inter_left _ hqsub).trans hpU.le
      · exact singleton_subset_iff.mpr ⟨q.target_mem_range, hout i hi⟩
    refine ⟨x i, hr, arm, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have hji := hcase j hj
      subst j
      simpa only [harm] using hq
    · intro j hj
      have hji := hcase j hj
      subst j
      simpa only [harm] using (hobs i hi).mono_left hqsub
    · intro j hj
      have hji := hcase j hj
      subst j
      simpa only [harm] using hqU
    · intro j hj k hk hjk
      exact (hjk ((hcase j hj).trans (hcase k hk).symm)).elim
    · intro j hj
      have hji := hcase j hj
      subst j
      exact ⟨u, hu, by simpa only [harm] using huspeed⟩

end FiniteAvalanches.Electrical.StatementGeometry
