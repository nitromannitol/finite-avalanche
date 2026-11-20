import FiniteAvalanches.Support.Plane.TreePaths

/-!
# Polygonal path stars

Disjoint path stars in open plane regions can be chosen with polygonal images.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- Distinct points in an open connected plane region admit a disjoint star of
injective paths with polygonal images, avoiding a prescribed finite set. -/
theorem exists_disjoint_polygonal_path_star {ι : Type*} {U S : Set (ℝ × ℝ)}
    {r : ℝ × ℝ} {x : ι → ℝ × ℝ} (hU : IsOpen U)
    (hconn : IsPreconnected U) (s : Finset ι) (hS : S.Finite)
    (hr : r ∈ U \ S) (hx : ∀ i ∈ s, x i ∈ U \ S)
    (hxr : ∀ i ∈ s, x i ≠ r)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → x i ≠ x j) :
    ∃ (vs : ι → List (ℝ × ℝ)) (p : ∀ i, Path (x i) r),
      (∀ i ∈ s, LatticeProb.Topology.IsSimplePolygonalChain (vs i)) ∧
      (∀ i ∈ s, Function.Injective (p i)) ∧
      (∀ i ∈ s, range (p i) = LatticeProb.Topology.polygonalChain (vs i)) ∧
      (∀ i ∈ s, range (p i) ⊆ U \ S) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (p i) ∩ range (p j) = {r}) := by
  classical
  obtain ⟨vs, hs, hh, hl, hsub, hd⟩ :=
    exists_disjoint_polygonal_star hU hconn s hS hr hx hxr hinj
  let p : ∀ i, Path (x i) r := fun i =>
    if hi : i ∈ s then
      (LatticeProb.Topology.polygonalChainPath (vs i) (hs i hi).ne_nil).cast
        (hh i hi).symm (hl i hi).symm
    else Path.segment (x i) r
  have hp : ∀ i ∈ s, Function.Injective (p i) := by
    intro i hi
    dsimp only [p]
    rw [dif_pos hi]
    apply (hs i hi).path_injective
    rw [hh i hi, hl i hi]
    exact hxr i hi
  have htrace : ∀ i ∈ s, range (p i) = LatticeProb.Topology.polygonalChain (vs i) := by
    intro i hi
    dsimp only [p]
    rw [dif_pos hi]
    exact LatticeProb.Topology.range_polygonal_chain_path _ _
  refine ⟨vs, p, hs, hp, htrace, ?_, ?_⟩
  · intro i hi
    rw [htrace i hi]
    exact hsub i hi
  · intro i hi j hj hij
    rw [htrace i hi, htrace j hj]
    exact hd i hi j hj hij

end FiniteAvalanches.Electrical.StatementGeometry
