import FiniteAvalanches.Trees.Lattice.RayCoalescence

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb SimpleGraph
open scoped Classical
noncomputable section

/-- Every finite nonempty collection of actual rays has a common vertex. -/
theorem finite_rays_common_vertex (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (S : Finset (Site 2)) (hS : S.Nonempty) :
    ∃ c : Site 2, ∀ x ∈ S, c ∈ Set.range (infiniteRay ω hT hEnd x) := by
  induction S using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hS)
  | @insert x S hx ih =>
    by_cases hne : S.Nonempty
    · obtain ⟨c, hc⟩ := ih hne
      obtain ⟨m, n, hmn⟩ := infiniteRay_common_tail ω hT hEnd x c
      refine ⟨infiniteRay ω hT hEnd c n, ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with h | h
      · subst v
        exact ⟨m, by simpa only [Nat.add_zero] using hmn 0⟩
      · obtain ⟨k, hk⟩ := hc v h
        exact ⟨k + n, by rw [infiniteRay_add, hk]⟩
    · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      refine ⟨x, ?_⟩
      intro v hv
      have hvx : v = x := by simpa only [Finset.mem_insert, Finset.notMem_empty, or_false] using hv
      subst v
      exact ⟨0, rfl⟩

/-- The first vertex common to all rays is the unique common vertex preceding every other one. -/
theorem existsUnique_common_ray_ancestor (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (S : Finset (Site 2)) (hS : S.Nonempty) :
    ∃! c : Site 2,
      (∀ x ∈ S, c ∈ Set.range (infiniteRay ω hT hEnd x)) ∧
      ∀ d : Site 2, (∀ x ∈ S, d ∈ Set.range (infiniteRay ω hT hEnd x)) →
        d ∈ Set.range (infiniteRay ω hT hEnd c) := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨d, hd⟩ := finite_rays_common_vertex ω hT hEnd S ⟨x, hx⟩
  obtain ⟨n, hn⟩ := hd x hx
  have hex : ∃ n, ∀ v ∈ S,
      infiniteRay ω hT hEnd x n ∈ Set.range (infiniteRay ω hT hEnd v) :=
    ⟨n, hn.symm ▸ hd⟩
  let N := Nat.find hex
  let c := infiniteRay ω hT hEnd x N
  have hc : ∀ v ∈ S, c ∈ Set.range (infiniteRay ω hT hEnd v) := Nat.find_spec hex
  have hfirst : ∀ d : Site 2,
      (∀ v ∈ S, d ∈ Set.range (infiniteRay ω hT hEnd v)) →
      d ∈ Set.range (infiniteRay ω hT hEnd c) := by
    intro d hd
    obtain ⟨m, hm⟩ := hd x hx
    have hNm : N ≤ m := by
      by_contra hlt
      exact Nat.find_min hex (by omega) (hm.symm ▸ hd)
    refine ⟨m - N, ?_⟩
    change infiniteRay ω hT hEnd (infiniteRay ω hT hEnd x N) (m - N) = d
    rw [← infiniteRay_add, Nat.add_sub_of_le hNm]
    exact hm
  refine ⟨c, ⟨hc, hfirst⟩, ?_⟩
  rintro c' ⟨hc', hfirst'⟩
  obtain ⟨i, hi⟩ := hfirst c' hc'
  obtain ⟨j, hj⟩ := hfirst' c hc
  have hcycle : infiniteRay ω hT hEnd c (i + j) = infiniteRay ω hT hEnd c 0 := by
    rw [infiniteRay_add, hi, hj, infiniteRay_zero]
  have hij := infiniteRay_injective ω hT hEnd c hcycle
  have hi0 : i = 0 := by omega
  rw [hi0, infiniteRay_zero] at hi
  exact hi.symm

/-- The first vertex common to all rays from the specified nonempty finite set. -/
def commonRayAncestor (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (S : Finset (Site 2)) (hS : S.Nonempty) : Site 2 :=
  Classical.choose (existsUnique_common_ray_ancestor ω hT hEnd S hS).exists

theorem commonRayAncestor_characterization (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (S : Finset (Site 2)) (hS : S.Nonempty) (c : Site 2) :
    c = commonRayAncestor ω hT hEnd S hS ↔
      (∀ x ∈ S, c ∈ Set.range (infiniteRay ω hT hEnd x)) ∧
      ∀ d : Site 2, (∀ x ∈ S, d ∈ Set.range (infiniteRay ω hT hEnd x)) →
        d ∈ Set.range (infiniteRay ω hT hEnd c) := by
  have hc := Classical.choose_spec (existsUnique_common_ray_ancestor ω hT hEnd S hS).exists
  constructor
  · rintro rfl; exact hc
  · intro h
    exact (existsUnique_common_ray_ancestor ω hT hEnd S hS).unique h hc

/-- All rays from the finite set have the unique ray from their first common vertex as a tail. -/
theorem commonRayAncestor_tails (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (S : Finset (Site 2)) (hS : S.Nonempty) :
    ∀ x ∈ S, ∃ n : ℕ, ∀ k : ℕ,
      infiniteRay ω hT hEnd x (n + k) =
        infiniteRay ω hT hEnd (commonRayAncestor ω hT hEnd S hS) k := by
  have hc := ((commonRayAncestor_characterization ω hT hEnd S hS _).mp rfl).1
  intro x hx
  obtain ⟨n, hn⟩ := hc x hx
  exact ⟨n, fun k => by rw [infiniteRay_add, hn]⟩

/-- The outgoing edge is an original lattice edge, with its selected indicator retained. -/
def outgoingLatticeEdge (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : LatticeEdge :=
  ⟨s(x, infiniteDirection ω hT hEnd x),
    toGraph_le_lattice ω (infiniteDirection_spec ω hT hEnd x).1⟩

theorem outgoingLatticeEdge_selected (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : ω (outgoingLatticeEdge ω hT hEnd x) = true :=
  (edge_mem_toGraph_iff ω _).mp (infiniteDirection_spec ω hT hEnd x).1

/-- The past is the starting vertex's actual component after its outgoing edge is deleted. -/
def rayPast (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : Set (Site 2) :=
  cutComponent ω (outgoingLatticeEdge ω hT hEnd x) x

theorem mem_rayPast_iff (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x z : Site 2) :
    z ∈ rayPast ω hT hEnd x ↔
      (cutGraph ω (outgoingLatticeEdge ω hT hEnd x)).Reachable z x :=
  mem_cutComponent_iff ω _ x z

theorem rayPast_finite (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : (rayPast ω hT hEnd x).Finite :=
  infiniteDirection_start_finite ω hT hEnd x

end
end FiniteAvalanches.Trees.Lattice
