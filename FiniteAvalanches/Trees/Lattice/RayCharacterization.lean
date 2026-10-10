import FiniteAvalanches.Trees.Lattice.BundledRays

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb FiniteAvalanches.Wilson.Lattice

/-- A one-ended lattice tree has exactly one infinite simple selected path from every
vertex, and any two such paths share a complete parametrized future tail.
Lyons–Peres Example7.1 p236; finite-complement criterion p242; ray definition p364.
Local finiteness is already proved for every literal selected lattice graph. -/
theorem oneEndedTree_unique_rays_common_tail (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite) :
    (∀ x : Site 2, ∃! r : SimpleRay, r.vertex 0 = x ∧
      ∀ n, (toGraph ω).Adj (r.vertex n) (r.vertex (n + 1))) ∧
    ∀ (x y : Site 2) (r q : SimpleRay),
      (r.vertex 0 = x ∧ ∀ n, (toGraph ω).Adj (r.vertex n) (r.vertex (n + 1))) →
      (q.vertex 0 = y ∧ ∀ n, (toGraph ω).Adj (q.vertex n) (q.vertex (n + 1))) →
      ∃ m n : ℕ, ∀ k : ℕ, r.vertex (m + k) = q.vertex (n + k) := by
  refine ⟨existsUnique_bundledSimpleRay ω hT hEnd, ?_⟩
  intro x y r q hr hq
  have er := (bundledInfiniteRay_characterization ω hT hEnd x r).mpr hr
  have eq := (bundledInfiniteRay_characterization ω hT hEnd y q).mpr hq
  subst r
  subst q
  exact infiniteRay_common_tail ω hT hEnd x y

end FiniteAvalanches.Trees.Lattice
