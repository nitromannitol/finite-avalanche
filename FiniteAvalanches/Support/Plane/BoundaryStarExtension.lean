import FiniteAvalanches.Support.Plane.StarSplicing

/-!
# Boundary access to a rooted arc tree

An accessible boundary point can be joined to the root of a finite arc tree
without meeting the tree elsewhere, provided a free root stub is available.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A boundary access avoiding a rooted tree and a free root stub extends to
an injective path meeting the tree only at its root. -/
theorem exists_boundary_path_to_root_of_stub
    {U K S : Set (ℝ × ℝ)} {r q x b : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hK : IsFiniteArcTree r K)
    (hKU : K ⊆ U) (hS : S.Finite) (p : Path q r) (hp : Function.Injective p)
    (hpU : range p ⊆ U \ S) (hpK : range p ∩ K = {r}) (hq : q ∉ K)
    (a : Path x b) (ha : Function.Injective a) (hx : x ∉ U)
    (haU : range a ⊆ U ∪ {x}) (haS : Disjoint (range a) S)
    (haK : Disjoint (range a) (K ∪ range p)) (hb : b ∈ U) :
    ∃ w : Path r x, Function.Injective w ∧ range w ⊆ (U ∪ {x}) \ S ∧
      range w ∩ K = {r} := by
  have hbK : b ∉ K := by
    intro h
    exact disjoint_left.mp haK a.target_mem_range (Or.inl h)
  have hbp : b ∉ range p := by
    intro h
    exact disjoint_left.mp haK a.target_mem_range (Or.inr h)
  have hbS : b ∉ S := fun h => disjoint_left.mp haS a.target_mem_range h
  obtain ⟨v, hv, hvU, hvK⟩ := exists_path_to_root_of_stub hU hconn hK hKU hS p hp hpU hpK
    ⟨⟨⟨hb, hbK⟩, hbS⟩, hbp⟩ hq
  have hxv : x ∉ range v := fun h => hx (hvU h).1
  obtain ⟨w, hw, hwsub⟩ := exists_injective_path_in_union v a hv ha hxv
  refine ⟨w, hw, ?_, ?_⟩
  · intro z hz
    rcases hwsub hz with hz | hz
    · exact ⟨Or.inl (hvU hz).1, (hvU hz).2⟩
    · exact ⟨haU hz, fun hs => disjoint_left.mp haS hz hs⟩
  · apply subset_antisymm
    · intro z hz
      rcases hwsub hz.1 with hvz | haz
      · rw [← hvK]
        exact ⟨hvz, hz.2⟩
      · exact (disjoint_left.mp haK haz (Or.inl hz.2)).elim
    · apply singleton_subset_iff.mpr
      have hrK : r ∈ K := by
        have h : r ∈ range p ∩ K := by rw [hpK]; exact mem_singleton r
        exact h.2
      exact ⟨w.source_mem_range, hrK⟩

end FiniteAvalanches.Electrical.StatementGeometry
