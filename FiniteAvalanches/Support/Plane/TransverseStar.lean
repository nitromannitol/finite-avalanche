import FiniteAvalanches.Support.Plane.CrossingAccess
import FiniteAvalanches.Support.Plane.PolygonalPathStar

/-!
# Stars and transverse boundary access

Disjoint transverse accesses to charted boundary arcs can be paired with a
star in the complement of those arcs.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Charted boundary arcs admit disjoint transverse accesses whose free endpoints
are joined to a root by a disjoint star avoiding the boundary arcs. -/
theorem exists_transverse_access_and_disjoint_star
    {ι : Type*} [DecidableEq ι] {U S : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hconn : IsPreconnected U) (s : Finset ι) {x y : ι → ℝ × ℝ}
    (p : ∀ i, Path (x i) (y i)) (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hinter : ∀ i ∈ s, IsPreconnected (range (p i) ∩ Uᶜ))
    (hS : S.Finite) (hobsS : ∀ i ∈ s, Disjoint (range (p i)) S)
    {r : ℝ × ℝ} (hr : r ∈ (U \ (⋃ i ∈ s, range (p i))) \ S)
    (t : ι → unitInterval) (ht : ∀ i ∈ s, t i ≠ 1)
    (chart : ι → (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (c : ι → ℝ)
    (hvertical : ∀ i ∈ s, ∀ z ∈ range (p i), (chart i z).1 = c i) :
    ∃ b : ι → ℝ × ℝ, ∃ w : ∀ i, Path (p i (t i)) (b i),
    ∃ (vs : ι → List (ℝ × ℝ)) (a : ∀ i, Path (b i) r),
      (∀ i ∈ s, b i ≠ p i (t i) ∧ Function.Injective (w i) ∧
        range (w i) ⊆ U \ ((S ∪ {r}) ∪ ⋃ j ∈ s.erase i, range (p j)) ∧
        range (w i) ∩ range (p i) = {p i (t i)}) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (w i)) (range (w j))) ∧
      (∀ i ∈ s, LatticeProb.Topology.IsSimplePolygonalChain (vs i)) ∧
      (∀ i ∈ s, Function.Injective (a i)) ∧
      (∀ i ∈ s, range (a i) = LatticeProb.Topology.polygonalChain (vs i)) ∧
      (∀ i ∈ s, range (a i) ⊆ (U \ (⋃ j ∈ s, range (p j))) \ S) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (a i) ∩ range (a j) = {r}) := by
  have hobs : ∀ i ∈ s, Disjoint (range (p i)) (S ∪ {r}) := by
    intro i hi
    refine disjoint_union_right.mpr ⟨hobsS i hi, ?_⟩
    rw [disjoint_singleton_right]
    intro h
    exact hr.1.2 (mem_iUnion₂.mpr ⟨i, hi, h⟩)
  obtain ⟨b, w, hw, hww⟩ := exists_disjoint_transverse_paths_to_boundary_arcs
    hU s p hd hinside (hS.union (finite_singleton r)) hobs t ht chart c hvertical
  have hb : ∀ i ∈ s, b i ∈ (U \ (⋃ j ∈ s, range (p j))) \ S := by
    intro i hi
    have hwbi := hw i hi
    have hbw : b i ∈ range (w i) := (w i).target_mem_range
    have hbsub := hwbi.2.2.1 hbw
    refine ⟨⟨hbsub.1, ?_⟩, fun hbS => hbsub.2 (Or.inl (Or.inl hbS))⟩
    intro h
    obtain ⟨j, hj, hbj⟩ := mem_iUnion₂.mp h
    by_cases hji : j = i
    · subst j
      have hbeq : b i = p i (t i) := by
        have h := hwbi.2.2.2.le ⟨hbw, hbj⟩
        simpa only [mem_singleton_iff] using h
      exact hwbi.1 hbeq
    · exact hbsub.2 (Or.inr (mem_iUnion₂.mpr
        ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, hbj⟩))
  have hbr : ∀ i ∈ s, b i ≠ r := by
    intro i hi heq
    have h := (hw i hi).2.2.1 (w i).target_mem_range
    exact h.2 (Or.inl (Or.inr (mem_singleton_iff.mpr heq)))
  have hbinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → b i ≠ b j := by
    intro i hi j hj hij heq
    apply disjoint_left.mp (hww i hi j hj hij) (w i).target_mem_range
    simpa only [heq] using (w j).target_mem_range
  have hc : IsCompact (⋃ i ∈ s, range (p i)) :=
    s.isCompact_biUnion (fun i _ => isCompact_range (p i).continuous)
  obtain ⟨vs, a, hvs, ha, hatrace, hasub, hasep⟩ :=
    exists_disjoint_polygonal_path_star (hU.sdiff hc.isClosed)
    (isPreconnected_sdiff_finset_paths_of_disjoint_inside hU hconn s p hp hd hinter)
    s hS hr hb hbr hbinj
  exact ⟨b, w, vs, a, hw, hww, hvs, ha, hatrace, hasub, hasep⟩

end FiniteAvalanches.Electrical.StatementGeometry
