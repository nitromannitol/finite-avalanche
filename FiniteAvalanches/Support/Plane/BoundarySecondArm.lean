import FiniteAvalanches.Support.Plane.BoundarySecondConnector
import FiniteAvalanches.Support.Plane.RetainedTailReparam

/-!
# A second boundary arm with protected stubs

A connector from a reserved root stub to an unused access gives a second arm
with the prescribed terminal parametrization and the remaining stubs protected.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A reserved stub extends to a second boundary arm with exact terminal
speed, avoiding the first arm, the other stubs and the other accesses. -/
theorem exists_second_boundary_arm_with_protected_stubs
    {ι : Type*} [DecidableEq ι] {U S : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hS : S.Finite) (s : Finset ι)
    {x y : ι → ℝ × ℝ} (a : ∀ i, Path (x i) (y i))
    (ha : ∀ i ∈ s, Function.Injective (a i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (a i) ∩ U) (range (a j)))
    (haU : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → a i t ∈ U)
    (hy : ∀ i ∈ s, y i ∉ U) (haS : ∀ i ∈ s, Disjoint (range (a i)) S)
    {i : ι} {r : ℝ × ℝ} {n : ℕ} {q : Fin n → ℝ × ℝ}
    (p : ∀ k, Path (q k) r) (w : Path r (y i))
    (hwU : range w ⊆ U ∪ {y i})
    (hp : ∀ k, q k ≠ r ∧ Function.Injective (p k) ∧
      range (p k) ⊆ (U \ ⋃ l ∈ s, range (a l)) \ S ∧
      range (p k) ∩ range w = {r})
    (hpair : ∀ k l, k ≠ l → range (p k) ∩ range (p l) = {r})
    (havoid : Disjoint (range w ∩ U) (⋃ j ∈ s.erase i, range (a j)))
    (hconn : IsPreconnected (((U \ range w) \ (⋃ j ∈ s.erase i, range (a j))) \
      (⋃ k, range (p k))))
    {j : ι} (hj : j ∈ s.erase i) (k : Fin n) :
    ∃ v : Path r (y j), Function.Injective v ∧ range v ⊆ (U ∪ {y j}) \ S ∧
      (∀ z ∈ range v ∩ range w, z = r ∨ z = y j ∧ y j = y i) ∧
      (∀ l, l ≠ k → range (p l) ∩ range v = {r}) ∧
      Disjoint (range v ∩ U) (⋃ l ∈ (s.erase i).erase j, range (a l)) ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          v t = a j ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩ := by
  classical
  have hjS : j ∈ s := (Finset.mem_erase.mp hj).2
  obtain ⟨c, hc, hcU, hcp, hca, hcw, hcl, hcA⟩ :=
    exists_connector_of_first_boundary_arm hU hS s a ha hd haU haS p w hp hpair havoid hconn hj k
  have hpc : range (p k).symm ∩ range c = {q k} := by
    rw [Path.symm_range, inter_comm, hcp]
  have hpain : Disjoint (range (p k)) (range (a j)) := by
    apply disjoint_left.mpr
    intro z hz ha'
    exact ((hp k).2.2.1 hz).1.2 (mem_iUnion₂.mpr ⟨j, hjS, ha'⟩)
  let b : Path r (x j) := (p k).symm.trans c
  have hb : Function.Injective b := by
    apply LatticeProb.Topology.path_trans_injective _ hc hpc
    intro u v h
    exact unitInterval.symm_involutive.injective ((hp k).2.1 h)
  have hbRange : range b = range (p k) ∪ range c := by
    simp only [b, Path.trans_range, Path.symm_range]
  have hba : range b ∩ range (a j) = {x j} := by
    rw [hbRange, union_inter_distrib_right, disjoint_iff_inter_eq_empty.mp hpain, empty_union, hca]
  let d : Path r (y j) := b.trans (a j)
  have hd' : Function.Injective d := LatticeProb.Topology.path_trans_injective hb (ha j hjS) hba
  have hdRange : range d = range (p k) ∪ range c ∪ range (a j) := by
    rw [show range d = range b ∪ range (a j) from Path.trans_range _ _, hbRange]
  have htail : range ((a j).subpath 0 1) ⊆ range d := by
    rw [Path.range_subpath_of_le _ _ _ (show (0 : unitInterval) ≤ 1 from bot_le)]
    exact (image_subset_range _ _).trans (hdRange ▸ subset_union_right)
  obtain ⟨v, hv, hvsub, u, hu, huspeed⟩ :=
    exists_path_with_parametrized_retained_tail d (a j) hd' (ha j hjS) (t := 0) (by norm_num) htail
  have hvsub' : range v ⊆ range (p k) ∪ range c ∪ range (a j) := hdRange ▸ hvsub
  have haout : range (a j) ∩ Uᶜ = {y j} :=
    range_inter_compl_of_mem_except_target (a j) (haU j hjS) (hy j hjS)
  refine ⟨v, hv, ?_, ?_, ?_, ?_, u, hu, huspeed⟩
  · intro z hz
    rcases hvsub' hz with (hz | hz) | hz
    · have h := (hp k).2.2.1 hz
      exact ⟨Or.inl h.1.1, h.2⟩
    · exact ⟨Or.inl (hcU hz).1, (hcU hz).2⟩
    · refine ⟨?_, fun hs => disjoint_left.mp (haS j hjS) hz hs⟩
      by_cases hzU : z ∈ U
      · exact Or.inl hzU
      · exact Or.inr (haout ▸ ⟨hz, hzU⟩)
  · intro z hz
    rcases hvsub' hz.1 with (hpz | hcz) | haz
    · left
      exact mem_singleton_iff.mp ((hp k).2.2.2 ▸ ⟨hpz, hz.2⟩)
    · exact (disjoint_left.mp hcw hcz hz.2).elim
    · by_cases hzU : z ∈ U
      · exact (disjoint_left.mp havoid ⟨hz.2, hzU⟩
          (mem_iUnion₂.mpr ⟨j, hj, haz⟩)).elim
      · have hzy : z = y j := mem_singleton_iff.mp (haout ▸ ⟨haz, hzU⟩)
        right
        refine ⟨hzy, ?_⟩
        rcases hwU hz.2 with h | h
        · exact (hzU h).elim
        · exact hzy.symm.trans (mem_singleton_iff.mp h)
  · intro l hl
    apply subset_antisymm
    · intro z hz
      rcases hvsub' hz.2 with (hpz | hcz) | haz
      · rw [← hpair l k hl]
        exact ⟨hz.1, hpz⟩
      · exact (disjoint_left.mp (hcl l hl) hcz hz.1).elim
      · exact (((hp l).2.2.1 hz.1).1.2 (mem_iUnion₂.mpr ⟨j, hjS, haz⟩)).elim
    · exact singleton_subset_iff.mpr ⟨(p l).target_mem_range, v.source_mem_range⟩
  · apply disjoint_left.mpr
    rintro z ⟨hz, hzU⟩ hobs
    obtain ⟨l, hl, hlz⟩ := mem_iUnion₂.mp hobs
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hls : l ∈ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).2
    rcases hvsub' hz with (hpz | hcz) | haz
    · exact ((hp k).2.2.1 hpz).1.2 (mem_iUnion₂.mpr ⟨l, hls, hlz⟩)
    · exact disjoint_left.mp hcA hcz hobs
    · exact disjoint_left.mp (hd j hjS l hls hlj.symm) ⟨haz, hzU⟩ hlz

end FiniteAvalanches.Electrical.StatementGeometry
