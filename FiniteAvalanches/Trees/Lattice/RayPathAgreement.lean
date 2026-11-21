import FiniteAvalanches.Trees.Lattice.RayPast
import FiniteAvalanches.Trees.Lattice.RayCoalescence
import FiniteAvalanches.Trees.Lattice.EuclideanPaths

/-! Tree paths toward distant sites follow the ray.

In a tree with one end, deleting the edge from a vertex `x` toward the end leaves the
past of `x` as the component of `x`. A path whose two endpoints lie outside the past of
`x` does not visit `x`: both halves of the path at `x` would cross the deleted edge. Hence
the tree path from `x` to `z` starts with the first `K` steps of the ray from `x` unless
`z` lies in the past of the `K`-th ray vertex, and every vertex of this path off the ray
has `z` in its past. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice

open LatticeProb SimpleGraph
open FiniteAvalanches.Trees.Lattice.BarlowMasson
open scoped Classical

noncomputable section

variable (ω : EdgeField) (hT : IsTree ω)
  (hEnd : ∀ K : Finset (Site 2), ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)

/-- A path with both endpoints outside the past of `x` does not visit `x`. -/
theorem not_mem_support_of_not_mem_rayPast (x : Site 2) {a b : Site 2}
    (q : (toGraph ω).Walk a b) (hq : q.IsPath) (ha : a ∉ rayPast ω hT hEnd x)
    (hb : b ∉ rayPast ω hT hEnd x) : x ∉ q.support := by
  intro hx
  let e := outgoingLatticeEdge ω hT hEnd x
  have hreach (y : Site 2) (p : (toGraph ω).Walk x y) (hp : e.val ∉ p.edges) :
      y ∈ rayPast ω hT hEnd x := by
    rw [mem_rayPast_iff]
    exact (p.toDeleteEdge e.val hp).reachable.symm
  have h2 : e.val ∈ (q.dropUntil x hx).edges := by
    by_contra h
    exact hb (hreach b _ h)
  have h1 : e.val ∈ (q.takeUntil x hx).edges := by
    by_contra h
    apply ha
    apply hreach a (q.takeUntil x hx).reverse
    rwa [Walk.edges_reverse, List.mem_reverse]
  have hnd := hq.isTrail.edges_nodup
  rw [← q.take_spec hx, Walk.edges_append] at hnd
  exact List.disjoint_of_nodup_append hnd h1 h2

theorem rayPast_mono_ray (x : Site 2) {j K : ℕ} (hjK : j ≤ K) :
    rayPast ω hT hEnd (infiniteRay ω hT hEnd x j) ⊆ rayPast ω hT hEnd (infiniteRay ω hT hEnd x K) := by
  intro z hz
  rw [mem_rayPast_iff_ray_passes] at hz ⊢
  obtain ⟨i, hi⟩ := hz
  refine ⟨i + (K - j), ?_⟩
  rw [infiniteRay_add, hi, ← infiniteRay_add, Nat.add_sub_cancel' hjK]

theorem ray_not_mem_rayPast_earlier (x : Site 2) {j K : ℕ} (hjK : j < K) :
    infiniteRay ω hT hEnd x K ∉ rayPast ω hT hEnd (infiniteRay ω hT hEnd x j) := by
  rw [mem_rayPast_iff_ray_passes]
  rintro ⟨i, hi⟩
  rw [← infiniteRay_add] at hi
  have := infiniteRay_injective ω hT hEnd x hi
  omega

/-- The first `K` steps of the ray. -/
def rayWalk (x : Site 2) : (K : ℕ) → (toGraph ω).Walk x (infiniteRay ω hT hEnd x K)
  | 0 => Walk.nil
  | K + 1 => (rayWalk x K).concat ((infiniteRay_isSimpleRay ω hT hEnd x).2.2 K)

theorem rayWalk_support (x : Site 2) (K : ℕ) :
    (rayWalk ω hT hEnd x K).support = (List.range (K + 1)).map (infiniteRay ω hT hEnd x) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [rayWalk, Walk.support_concat, ih]
    simp [List.range_succ]

/-- Unless `z` lies in the past of the `K`-th ray vertex, the tree path from `x` to `z`
starts with the first `K` steps of the ray. -/
theorem treePath_support_eq_of_not_mem_rayPast (x z : Site 2) (K : ℕ)
    (hz : z ∉ rayPast ω hT hEnd (infiniteRay ω hT hEnd x K)) :
    (treePath ω hT x z).support = (List.range (K + 1)).map (infiniteRay ω hT hEnd x) ++
      (treePath ω hT (infiniteRay ω hT hEnd x K) z).support.tail := by
  let q := treePath ω hT (infiniteRay ω hT hEnd x K) z
  have hq : q.IsPath := FiniteAvalanches.Trees.RootedPaths.path_isPath hT _ _
  have hqs := hq.support_nodup
  rw [← q.cons_tail_support] at hqs
  have hc : ((rayWalk ω hT hEnd x K).append q).IsPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_append, rayWalk_support]
    apply List.Nodup.append
    · exact (List.nodup_range).map (infiniteRay_injective ω hT hEnd x)
    · exact (List.nodup_cons.mp hqs).2
    · intro v hv hvq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      have hjK := Nat.lt_succ_iff.mp (List.mem_range.mp hj)
      rcases lt_or_eq_of_le hjK with hlt | rfl
      · apply not_mem_support_of_not_mem_rayPast ω hT hEnd (infiniteRay ω hT hEnd x j) q hq
          (ray_not_mem_rayPast_earlier ω hT hEnd x hlt)
          (fun h => hz (rayPast_mono_ray ω hT hEnd x hjK h))
        exact List.mem_of_mem_tail hvq
      · exact (List.nodup_cons.mp hqs).1 hvq
  have he := (treePath_full_characterization ω hT x z _).mpr hc
  rw [he, Walk.support_append, rayWalk_support]

/-- A vertex of the tree path from `x` to `z` off the ray from `x` has `z` in its past. -/
theorem mem_rayPast_of_mem_treePath (x z v : Site 2) (hv : v ∈ (treePath ω hT x z).support)
    (hvr : v ∉ Set.range (infiniteRay ω hT hEnd x)) : z ∈ rayPast ω hT hEnd v := by
  by_contra hz
  exact not_mem_support_of_not_mem_rayPast ω hT hEnd v (treePath ω hT x z)
    (FiniteAvalanches.Trees.RootedPaths.path_isPath hT _ _)
    (by rw [mem_rayPast_iff_ray_passes]; exact hvr) hz hv

end

end FiniteAvalanches.Trees.Lattice
