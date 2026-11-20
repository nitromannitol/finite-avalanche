import FiniteAvalanches.Support.Plane.LocalArcEndpointAccess
import FiniteAvalanches.Support.Plane.BoundaryArcJoin

/-!
# Connecting endpoints through a common complement

If the complement of two arcs and a closed obstacle is connected, their
accessible endpoints can be joined without touching either arc elsewhere.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- Two arc endpoints can be joined through a common connected complement,
while avoiding a closed obstacle and both arcs away from the endpoints. -/
theorem exists_injective_path_between_arc_endpoints
    {U K : Set (ℝ × ℝ)} (hU : IsOpen U) (hK : IsClosed K)
    {x y z w : ℝ × ℝ} (p : Path x y) (q : Path z w)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hx : x ∈ U \ (K ∪ range q)) (hz : z ∈ U \ (K ∪ range p))
    (hconn : IsPreconnected (U \ (K ∪ range p ∪ range q))) :
    ∃ v : Path x z, Function.Injective v ∧ range v ⊆ U \ K ∧
      range v ∩ range p = {x} ∧ range v ∩ range q = {z} := by
  have hxq : x ∉ range q := fun h => hx.2 (Or.inr h)
  have hzp : z ∉ range p := fun h => hz.2 (Or.inr h)
  have hxz : x ≠ z := fun h => hzp (h ▸ p.source_mem_range)
  obtain ⟨A, B, hA, hB, hxA, hzB, hAB⟩ := t2_separation hxz
  let P := U \ (K ∪ range q)
  let Q := U \ (K ∪ range p)
  have hP : IsOpen P := hU.sdiff (hK.union (isCompact_range q.continuous).isClosed)
  have hQ : IsOpen Q := hU.sdiff (hK.union (isCompact_range p.continuous).isClosed)
  obtain ⟨a, _, a', ha', ha'sub, ha'out⟩ :=
    exists_injective_path_to_arc_endpoint_in_open p hp (hA.inter hP) ⟨hxA, hx⟩
  obtain ⟨b, _, b', hb', hb'sub, hb'out⟩ :=
    exists_injective_path_to_arc_endpoint_in_open q hq (hB.inter hQ) ⟨hzB, hz⟩
  let W := U \ (K ∪ range p ∪ range q)
  have hW : IsOpen W := hU.sdiff
    ((hK.union (isCompact_range p.continuous).isClosed).union
      (isCompact_range q.continuous).isClosed)
  have hdisj : Disjoint (range a') (range b') := by
    apply disjoint_left.mpr
    intro t ht1 ht2
    exact disjoint_left.mp hAB (ha'sub ht1).1 (hb'sub ht2).1
  have haW : ∀ t : unitInterval, t ≠ 1 → a' t ∈ W := by
    intro t ht
    have h := ha'sub ⟨t, rfl⟩
    exact ⟨h.2.1, fun hmem => by
      rcases hmem with hmem | hmem
      · rcases hmem with hK | hp
        · exact h.2.2 (Or.inl hK)
        · exact ha'out t ht hp
      · exact h.2.2 (Or.inr hmem)⟩
  have hbW : ∀ t : unitInterval, t ≠ 1 → b' t ∈ W := by
    intro t ht
    have h := hb'sub ⟨t, rfl⟩
    exact ⟨h.2.1, fun hmem => by
      rcases hmem with hmem | hmem
      · rcases hmem with hK | hp
        · exact h.2.2 (Or.inl hK)
        · exact h.2.2 (Or.inr hp)
      · exact hb'out t ht hmem⟩
  have hxW : x ∉ W := fun h => h.2 (Or.inl (Or.inr p.source_mem_range))
  have hzW : z ∉ W := fun h => h.2 (Or.inr q.source_mem_range)
  obtain ⟨v, hv, hboundary⟩ := exists_injective_path_between_boundary_accesses
    hW hconn a' b' ha' hb' hdisj haW hbW hxW hzW
  have hcases : ∀ t ∈ range v, t ∈ W ∨ t = x ∨ t = z := by
    intro t ht
    by_cases htW : t ∈ W
    · exact Or.inl htW
    · have h : t ∈ ({x, z} : Set (ℝ × ℝ)) := by
        rw [← hboundary]
        exact ⟨ht, htW⟩
      simpa only [mem_insert_iff, mem_singleton_iff] using Or.inr h
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · intro t ht
    rcases hcases t ht with ht | rfl | rfl
    · exact ⟨ht.1, fun h => ht.2 (Or.inl (Or.inl h))⟩
    · exact ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
    · exact ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  · apply subset_antisymm
    · rintro t ⟨ht, htp⟩
      rcases hcases t ht with ht | rfl | rfl
      · exact (ht.2 (Or.inl (Or.inr htp))).elim
      · exact mem_singleton _
      · exact (hzp htp).elim
    · exact singleton_subset_iff.mpr ⟨v.source_mem_range, p.source_mem_range⟩
  · apply subset_antisymm
    · rintro t ⟨ht, htq⟩
      rcases hcases t ht with ht | rfl | rfl
      · exact (ht.2 (Or.inr htq)).elim
      · exact (hxq htq).elim
      · exact mem_singleton _
    · exact singleton_subset_iff.mpr ⟨v.target_mem_range, q.source_mem_range⟩

end FiniteAvalanches.Electrical.StatementGeometry
