import FiniteAvalanches.Wilson.Lattice.RootObservation

/-! Finite edge exhaustions and query lists beginning at a given site. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- An enumeration of all finite sets of lattice edges. -/
def finiteEdgeEnumeration : ℕ → Finset LatticeEdge :=
  Classical.choose (exists_surjective_nat (Finset LatticeEdge))

/-- The finite edge sets encountered through the first `n` enumeration steps. -/
def finiteEdgeExhaustion (n : ℕ) : Finset LatticeEdge :=
  (Finset.range n).biUnion finiteEdgeEnumeration

/-- Every finite edge set is contained in all sufficiently late exhaustion sets. -/
theorem eventually_subset_finiteEdgeExhaustion (E : Finset LatticeEdge) :
    ∀ᶠ n : ℕ in atTop, E ⊆ finiteEdgeExhaustion n := by
  obtain ⟨i, hi⟩ := (Classical.choose_spec (exists_surjective_nat (Finset LatticeEdge))) E
  filter_upwards [eventually_ge_atTop (i + 1)] with n hn
  intro e he
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
  change e ∈ finiteEdgeEnumeration i
  change finiteEdgeEnumeration i = E at hi
  rw [hi]
  exact he

/-- A finite query sequence covers every endpoint of the observed edges and
starts at the specified site. -/
theorem exists_rootEdgeQueries (x : Site 2) (E : Finset LatticeEdge) :
    ∃ (q : ℕ → Site 2) (n : ℕ), q 0 = x ∧ 0 < n ∧
      ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, q i = z := by
  obtain ⟨q, n, hE, _⟩ := exists_finite_queries E ∅
  let q' : ℕ → Site 2
    | 0 => x
    | i + 1 => q i
  refine ⟨q', n + 1, rfl, Nat.zero_lt_succ n, ?_⟩
  intro e he z hz
  obtain ⟨i, hi, hq⟩ := hE e he z hz
  exact ⟨i + 1, by omega, hq⟩

/-- A chosen query sequence for a finite edge set. -/
def rootEdgeQueries (x : Site 2) (E : Finset LatticeEdge) : ℕ → Site 2 :=
  (exists_rootEdgeQueries x E).choose

/-- The length of a chosen finite query sequence for an edge set. -/
def rootEdgeQueryLength (x : Site 2) (E : Finset LatticeEdge) : ℕ :=
  (exists_rootEdgeQueries x E).choose_spec.choose

/-- The chosen query starts at the designated site and covers its edge endpoints. -/
theorem rootEdgeQueries_spec (x : Site 2) (E : Finset LatticeEdge) :
    rootEdgeQueries x E 0 = x ∧ 0 < rootEdgeQueryLength x E ∧
      ∀ e ∈ E, ∀ z ∈ e.val,
        ∃ i < rootEdgeQueryLength x E, rootEdgeQueries x E i = z :=
  (exists_rootEdgeQueries x E).choose_spec.choose_spec

end
end FiniteAvalanches.Wilson.Lattice
