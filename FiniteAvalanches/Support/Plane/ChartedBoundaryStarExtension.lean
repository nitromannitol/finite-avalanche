import FiniteAvalanches.Support.Plane.BoundaryStarExtension
import FiniteAvalanches.Support.Plane.TransverseClosedAvoidance

/-!
# Rooted paths to charted boundary arcs

A charted point on one of finitely many disjoint boundary arcs can be joined
injectively to the root of a tree when a free root stub is available.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A charted point on a boundary arc can be joined to the root of an arc tree
while avoiding all the other boundary arcs and meeting the tree only at its root. -/
theorem exists_root_path_to_charted_boundary_arc
    {ι : Type*} [DecidableEq ι] {U S K : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (s : Finset ι)
    {x y : ι → ℝ × ℝ} (arc : ∀ i, Path (x i) (y i))
    (harc : ∀ i ∈ s, Function.Injective (arc i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (arc i) ∩ U) (range (arc j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → arc i t ∈ U)
    (hinter : ∀ i ∈ s, IsPreconnected (range (arc i) ∩ Uᶜ))
    (hS : S.Finite) (hobsS : ∀ i ∈ s, Disjoint (range (arc i)) S)
    (t : ι → unitInterval) (ht : ∀ i ∈ s, t i ≠ 1)
    (chart : ι → (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (c : ι → ℝ)
    (hvertical : ∀ i ∈ s, ∀ z ∈ range (arc i), (chart i z).1 = c i)
    {r q : ℝ × ℝ} (hK : IsFiniteArcTree r K)
    (hKU : K ⊆ U \ (⋃ i ∈ s, range (arc i)))
    (p : Path q r) (hp : Function.Injective p)
    (hpU : range p ⊆ (U \ (⋃ i ∈ s, range (arc i))) \ S)
    (hpK : range p ∩ K = {r}) (hq : q ∉ K)
    {i : ι} (hi : i ∈ s) :
    ∃ w : Path r (arc i (t i)), Function.Injective w ∧
      range w ⊆ ((U \ (⋃ j ∈ s, range (arc j))) ∪ {arc i (t i)}) \ S ∧
      range w ∩ K = {r} := by
  classical
  let W := U \ (⋃ j ∈ s, range (arc j))
  have hc : IsCompact (⋃ j ∈ s, range (arc j)) :=
    s.isCompact_biUnion (fun j _ => isCompact_range (arc j).continuous)
  have hW : IsOpen W := hU.sdiff hc.isClosed
  have hWconn : IsPreconnected W :=
    isPreconnected_sdiff_finset_paths_of_disjoint_inside hU hconn s arc harc hd hinter
  have hclosed : IsClosed (K ∪ range p) :=
    hK.isCompact.isClosed.union (isCompact_range p.continuous).isClosed
  have hmark : ∀ j ∈ s, arc j (t j) ∉ K ∪ range p := by
    intro j hj hz
    have hmem : arc j (t j) ∈ ⋃ k ∈ s, range (arc k) :=
      mem_iUnion₂.mpr ⟨j, hj, ⟨t j, rfl⟩⟩
    rcases hz with hz | hz
    · exact (hKU hz).2 hmem
    · exact (hpU hz).1.2 hmem
  obtain ⟨b, a, ha, _⟩ := exists_disjoint_transverse_paths_avoiding_closed
    hU s arc hd hinside hS hobsS t ht chart c hvertical hclosed hmark
  have hxi : arc i (t i) ∉ W := by
    intro hz
    exact hz.2 (mem_iUnion₂.mpr ⟨i, hi, ⟨t i, rfl⟩⟩)
  have haW : range (a i) ⊆ W ∪ {arc i (t i)} := by
    intro z hz
    by_cases hzi : z = arc i (t i)
    · exact Or.inr (mem_singleton_iff.mpr hzi)
    · apply Or.inl
      have hsub := (ha i hi).2.2.1 hz
      refine ⟨hsub.1.1, ?_⟩
      intro h
      obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp h
      by_cases hji : j = i
      · subst j
        have heq : z = arc i (t i) := by
          have hz' : z ∈ range (a i) ∩ range (arc i) := ⟨hz, hzj⟩
          rw [(ha i hi).2.2.2] at hz'
          exact mem_singleton_iff.mp hz'
        exact hzi heq
      · exact hsub.1.2 (Or.inr (mem_iUnion₂.mpr
          ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, hzj⟩))
  have haS : Disjoint (range (a i)) S := by
    apply disjoint_left.mpr
    intro z hz hzS
    exact ((ha i hi).2.2.1 hz).1.2 (Or.inl hzS)
  have haK : Disjoint (range (a i)) (K ∪ range p) := by
    apply disjoint_left.mpr
    intro z hz
    exact ((ha i hi).2.2.1 hz).2
  have hbW : b i ∈ W := by
    rcases haW (a i).target_mem_range with h | h
    · exact h
    · exact ((ha i hi).1 (mem_singleton_iff.mp h)).elim
  exact exists_boundary_path_to_root_of_stub hW hWconn hK hKU hS p hp hpU hpK hq
    (a i) (ha i hi).2.1 hxi haW haS haK hbW

end FiniteAvalanches.Electrical.StatementGeometry
