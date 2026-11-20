import FiniteAvalanches.Support.Plane.TreePaths

/-!
# Joining boundary access arcs

Two disjoint simple access arcs to the boundary of a connected open plane region
can be joined inside that region by a simple arc.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Classical

/-- An access path meets the complement of its open region only at its endpoint. -/
theorem range_inter_compl_eq_endpoint {U : Set (ℝ × ℝ)} {x y : ℝ × ℝ}
    (p : Path x y) (hinside : ∀ t : unitInterval, t ≠ 1 → p t ∈ U) (hy : y ∉ U) :
    range p ∩ Uᶜ = {y} := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    have ht1 : t = 1 := by
      by_contra h
      exact ht (hinside t h)
    simp only [mem_singleton_iff, ht1, Path.target]
  · intro hz
    have hz' : z = y := mem_singleton_iff.mp hz
    subst z
    exact ⟨p.target_mem_range, hy⟩

/-- Two disjoint simple access paths can be joined by a simple path whose only
points outside the region are their boundary endpoints. -/
theorem exists_injective_path_between_boundary_accesses {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) {r a s b : ℝ × ℝ}
    (p : Path r a) (q : Path s b) (hp : Function.Injective p)
    (hq : Function.Injective q) (hd : Disjoint (range p) (range q))
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (ha : a ∉ U) (hb : b ∉ U) :
    ∃ w : Path a b, Function.Injective w ∧ range w ∩ Uᶜ = {a, b} := by
  have hp' : Function.Injective p.symm := by
    intro x y h
    exact unitInterval.symm_involutive.injective (hp h)
  have hroot : r ∈ range p := p.source_mem_range
  have hrootU : r ∈ U := by
    simpa only [Path.source] using hpU 0 (by norm_num)
  have hinter : range p.symm ∩ ({r} : Set (ℝ × ℝ)) = {r} := by
    rw [Path.symm_range]
    exact inter_eq_right.mpr (singleton_subset_iff.mpr hroot)
  have htree : IsFiniteArcTree r (range p ∪ {r}) := by
    simpa only [Path.symm_range] using
      (IsFiniteArcTree.attach p.symm IsFiniteArcTree.singleton hp' hinter)
  have hrK : r ∈ range p ∪ {r} := Or.inl hroot
  have hrq : r ∉ range q := fun h => Set.disjoint_left.mp hd hroot h
  have hbK : b ∉ range p ∪ {r} := by
    rintro (hbp | hbr)
    · exact Set.disjoint_left.mp hd hbp q.target_mem_range
    · have : b = r := mem_singleton_iff.mp hbr
      exact hrq (this ▸ q.target_mem_range)
  let access : Unit → ℝ × ℝ := fun _ => s
  let boundary : Unit → ℝ × ℝ := fun _ => b
  let paths : ∀ i : Unit, Path (access i) (boundary i) := fun _ => q
  have hpaths : ∀ i ∈ ({()} : Finset Unit), Function.Injective (paths i) := by
    intro i _
    cases i
    exact hq
  have hdisjoint : ∀ i ∈ ({()} : Finset Unit), ∀ j ∈ ({()} : Finset Unit), i ≠ j →
      Disjoint (range (paths i) ∩ U) (range (paths j)) := by
    intro i _ j _ hne
    exact (hne (Subsingleton.elim i j)).elim
  have hinside : ∀ i ∈ ({()} : Finset Unit), ∀ t : unitInterval, t ≠ 1 → paths i t ∈ U := by
    intro i _ t ht
    cases i
    exact hqU t ht
  have hout : ∀ i ∈ ({()} : Finset Unit), boundary i ∉ U := by
    intro i _
    cases i
    exact hb
  have hr : r ∈ U \ (⋃ i ∈ ({()} : Finset Unit), range (paths i)) := by
    refine ⟨hrootU, ?_⟩
    intro h
    obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp h
    cases i
    exact hrq hi
  obtain ⟨z, hz, v, hv, hvK, htree', hvboundary, _⟩ :=
    exists_boundary_path_to_finiteArcTree hU hconn {()} paths hpaths hdisjoint hinside hout
      htree hrK hr (i := ()) (by simp) hbK
  have haK : a ∈ range v ∪ (range p ∪ {r}) := Or.inr (Or.inl p.target_mem_range)
  have hbK' : b ∈ range v ∪ (range p ∪ {r}) := Or.inl v.source_mem_range
  have hab : a ≠ b := fun h => Set.disjoint_left.mp hd p.target_mem_range
    (h.symm ▸ q.target_mem_range)
  obtain ⟨w, hw, hwsub⟩ := htree'.exists_injective_path haK hbK' hab
  have hboundary : (range v ∪ (range p ∪ {r})) ∩ Uᶜ ⊆ {a, b} := by
    intro x hx
    rcases hx.1 with hvx | hpx | hrx
    · have : x ∈ ({b} : Set (ℝ × ℝ)) := by rw [← hvboundary]; exact ⟨hvx, hx.2⟩
      simp only [mem_singleton_iff] at this
      simp [this]
    · have : x ∈ ({a} : Set (ℝ × ℝ)) := by
        rw [← range_inter_compl_eq_endpoint p hpU ha]
        exact ⟨hpx, hx.2⟩
      simp only [mem_singleton_iff] at this
      simp [this]
    · have : x = r := mem_singleton_iff.mp hrx
      exact (hx.2 (this.symm ▸ hrootU)).elim
  refine ⟨w, hw, ?_⟩
  apply subset_antisymm
  · exact (inter_subset_inter_left _ hwsub).trans hboundary
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨w.source_mem_range, ha⟩
    · exact ⟨w.target_mem_range, hb⟩

end FiniteAvalanches.Electrical.StatementGeometry
