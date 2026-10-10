import FiniteAvalanches.Trees.Lattice.RayCoalescence
import FiniteAvalanches.Wilson.Lattice.Paths

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb FiniteAvalanches.Wilson.Lattice
noncomputable section

theorem simpleRay_eq_of_vertex_eq (r q : SimpleRay) (h : r.vertex = q.vertex) : r = q := by
  rcases r with ⟨⟨v, hv⟩, hi⟩
  rcases q with ⟨⟨w, hw⟩, hj⟩
  change v = w at h
  cases h
  rfl

/-- The actual iterated ray, bundled as an infinite injective lattice path. -/
def bundledInfiniteRay (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : SimpleRay where
  vertex := infiniteRay ω hT hEnd x
  adjacent n := toGraph_le_lattice ω ((infiniteRay_isSimpleRay ω hT hEnd x).2.2 n)
  injective := infiniteRay_injective ω hT hEnd x

/-- Complete source characterization, for every literal SimpleRay. -/
theorem bundledInfiniteRay_characterization (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) (r : SimpleRay) :
    r = bundledInfiniteRay ω hT hEnd x ↔
      r.vertex 0 = x ∧ ∀ n, (toGraph ω).Adj (r.vertex n) (r.vertex (n + 1)) := by
  constructor
  · rintro rfl
    exact ⟨rfl, (infiniteRay_isSimpleRay ω hT hEnd x).2.2⟩
  · rintro ⟨h0, ha⟩
    apply simpleRay_eq_of_vertex_eq
    exact (infiniteRay_characterization ω hT hEnd x r.vertex).mpr ⟨h0, r.injective, ha⟩

theorem existsUnique_bundledSimpleRay (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) :
    ∃! r : SimpleRay, r.vertex 0 = x ∧
      ∀ n, (toGraph ω).Adj (r.vertex n) (r.vertex (n + 1)) := by
  refine ⟨bundledInfiniteRay ω hT hEnd x,
    (bundledInfiniteRay_characterization ω hT hEnd x _).mp rfl, ?_⟩
  intro r hr
  exact (bundledInfiniteRay_characterization ω hT hEnd x r).mpr hr

/-- No choice of the standing proof witnesses changes the oriented ray. -/
theorem bundledInfiniteRay_witness_independent (ω : EdgeField) (hT hT' : IsTree ω)
    (hEnd hEnd' : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : bundledInfiniteRay ω hT hEnd x = bundledInfiniteRay ω hT' hEnd' x := by
  apply (bundledInfiniteRay_characterization ω hT' hEnd' x _).mpr
  exact (bundledInfiniteRay_characterization ω hT hEnd x _).mp rfl

/-- Selected adjacency means the indicator of each actual unordered ray edge is true. -/
theorem bundledInfiniteRay_indicators (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) (n : ℕ) :
    ω ⟨s((bundledInfiniteRay ω hT hEnd x).vertex n,
      (bundledInfiniteRay ω hT hEnd x).vertex (n + 1)),
      (bundledInfiniteRay ω hT hEnd x).adjacent n⟩ = true :=
  (toGraph_adj_iff ω ((bundledInfiniteRay ω hT hEnd x).adjacent n)).mp
    ((infiniteRay_isSimpleRay ω hT hEnd x).2.2 n)

end
end FiniteAvalanches.Trees.Lattice
