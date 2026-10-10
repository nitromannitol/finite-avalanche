import FiniteAvalanches.Trees.Lattice.SimpleRays

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb SimpleGraph
open scoped Classical
noncomputable section

/-- An original selected edge is oriented in exactly one direction toward infinity. -/
theorem adjacent_direction_dichotomy (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x y : Site 2) (hxy : (toGraph ω).Adj x y) :
    infiniteDirection ω hT hEnd x = y ∨ infiniteDirection ω hT hEnd y = x := by
  let e : LatticeEdge := ⟨s(x, y), toGraph_le_lattice ω hxy⟩
  have he : ω e = true := (edge_mem_toGraph_iff ω e).mp hxy
  obtain ⟨⟨_, _, hFinUnique⟩, _⟩ := cutGraph_existsUnique_finite_and_infinite ω hT hEnd e he
  by_cases hyinf : (((toGraph ω).deleteEdges {s(x, y)}).connectedComponentMk y).supp.Infinite
  · exact Or.inl ((infiniteDirection_characterization ω hT hEnd x y).mpr ⟨hxy, hyinf⟩).symm
  · have hxinf : (((toGraph ω).deleteEdges {s(x, y)}).connectedComponentMk x).supp.Infinite := by
      intro hxfin
      have heq := (hFinUnique _ hxfin).trans (hFinUnique _ (not_not.mp hyinf)).symm
      exact ((SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hxy)
        (SimpleGraph.ConnectedComponent.exact heq)
    apply Or.inr
    apply Eq.symm
    apply (infiniteDirection_characterization ω hT hEnd y x).mpr
    refine ⟨hxy.symm, ?_⟩
    rw [Sym2.eq_swap]
    exact hxinf

/-- Starting at a vertex on a ray gives precisely its remaining tail. -/
theorem infiniteRay_add (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) (m n : ℕ) :
    infiniteRay ω hT hEnd x (m + n) =
      infiniteRay ω hT hEnd (infiniteRay ω hT hEnd x m) n := by
  unfold infiniteRay
  rw [Nat.add_comm m n, Function.iterate_add_apply]

/-- At any shared vertex the entire future tail, including its parametrization, is unique. -/
theorem infiniteRay_tail_of_eq (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x y : Site 2) (m n : ℕ)
    (h : infiniteRay ω hT hEnd x m = infiniteRay ω hT hEnd y n) (k : ℕ) :
    infiniteRay ω hT hEnd x (m + k) = infiniteRay ω hT hEnd y (n + k) := by
  rw [infiniteRay_add, infiniteRay_add, h]

private theorem adjacent_rays_meet (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x y : Site 2) (hxy : (toGraph ω).Adj x y) :
    ∃ m n : ℕ, infiniteRay ω hT hEnd x m = infiniteRay ω hT hEnd y n := by
  rcases adjacent_direction_dichotomy ω hT hEnd x y hxy with h | h
  · exact ⟨1, 0, by simpa only [infiniteRay_succ, infiniteRay_zero] using h⟩
  · exact ⟨0, 1, by simpa only [infiniteRay_succ, infiniteRay_zero] using h.symm⟩

private theorem rays_meet_trans (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x y z : Site 2)
    (hxy : ∃ m n : ℕ, infiniteRay ω hT hEnd x m = infiniteRay ω hT hEnd y n)
    (hyz : ∃ p q : ℕ, infiniteRay ω hT hEnd y p = infiniteRay ω hT hEnd z q) :
    ∃ m n : ℕ, infiniteRay ω hT hEnd x m = infiniteRay ω hT hEnd z n := by
  obtain ⟨m, n, hxy⟩ := hxy
  obtain ⟨p, q, hyz⟩ := hyz
  have h1 := infiniteRay_tail_of_eq ω hT hEnd x y m n hxy (max n p - n)
  have h2 := infiniteRay_tail_of_eq ω hT hEnd y z p q hyz (max n p - p)
  have hn : n + (max n p - n) = max n p := by omega
  have hp : p + (max n p - p) = max n p := by omega
  rw [hn] at h1
  rw [hp] at h2
  exact ⟨m + (max n p - n), q + (max n p - p), h1.trans h2⟩

/-- Rays from any two actual lattice vertices eventually have the same infinite tail. -/
theorem infiniteRay_common_tail (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x y : Site 2) :
    ∃ m n : ℕ, ∀ k : ℕ,
      infiniteRay ω hT hEnd x (m + k) = infiniteRay ω hT hEnd y (n + k) := by
  have hmeet : ∃ m n : ℕ, infiniteRay ω hT hEnd x m = infiniteRay ω hT hEnd y n := by
    obtain ⟨p⟩ := hT.connected.preconnected x y
    induction p with
    | nil => exact ⟨0, 0, rfl⟩
    | @cons a b c hab p ih =>
      exact rays_meet_trans ω hT hEnd a b c (adjacent_rays_meet ω hT hEnd a b hab) ih
  obtain ⟨m, n, hmn⟩ := hmeet
  exact ⟨m, n, infiniteRay_tail_of_eq ω hT hEnd x y m n hmn⟩

/-- The first shared vertex has uniquely determined indices on both simple rays. -/
theorem existsUnique_first_ray_meeting (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x y : Site 2) :
    ∃! p : ℕ × ℕ,
      infiniteRay ω hT hEnd x p.1 = infiniteRay ω hT hEnd y p.2 ∧
      (∀ i < p.1, ∀ j, infiniteRay ω hT hEnd x i ≠ infiniteRay ω hT hEnd y j) ∧
      (∀ j < p.2, ∀ i, infiniteRay ω hT hEnd x i ≠ infiniteRay ω hT hEnd y j) := by
  obtain ⟨m, n, hmn⟩ := infiniteRay_common_tail ω hT hEnd x y
  have hmeet : ∃ i, ∃ j, infiniteRay ω hT hEnd x i = infiniteRay ω hT hEnd y j :=
    ⟨m, n, by simpa only [Nat.add_zero] using hmn 0⟩
  let m := Nat.find hmeet
  obtain ⟨n, hmn⟩ := Nat.find_spec hmeet
  have hmin : ∀ i < m, ∀ j, infiniteRay ω hT hEnd x i ≠ infiniteRay ω hT hEnd y j := by
    intro i hi j hij
    exact Nat.find_min hmeet hi ⟨j, hij⟩
  have hmin' : ∀ j < n, ∀ i, infiniteRay ω hT hEnd x i ≠ infiniteRay ω hT hEnd y j := by
    intro j hj i hij
    have hmi : m ≤ i := by
      by_contra hlt
      exact hmin i (by omega) j hij
    have ht := infiniteRay_tail_of_eq ω hT hEnd x y m n hmn (i - m)
    have hm : m + (i - m) = i := by omega
    rw [hm] at ht
    have he := infiniteRay_injective ω hT hEnd y (ht.symm.trans hij)
    omega
  refine ⟨(m, n), ⟨hmn, hmin, hmin'⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨hab, hamin, _⟩
  have ham : a = m := by
    apply Nat.le_antisymm
    · by_contra hgt
      exact hamin m (by omega) n hmn
    · by_contra hgt
      exact hmin a (by omega) b hab
  apply Prod.ext ham
  have hmn' : infiniteRay ω hT hEnd x a = infiniteRay ω hT hEnd y n := by
    rw [ham]
    exact hmn
  exact infiniteRay_injective ω hT hEnd y (hab.symm.trans hmn')

end
end FiniteAvalanches.Trees.Lattice
