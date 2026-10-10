import FiniteAvalanches.Trees.Lattice.RayDirection

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb SimpleGraph
open scoped Classical
noncomputable section

/-- An infinite simple path in the actual selected lattice graph, with prescribed start. -/
def IsSimpleRay (ω : EdgeField) (x : Site 2) (r : ℕ → Site 2) : Prop :=
  r 0 = x ∧ Function.Injective r ∧ ∀ n, (toGraph ω).Adj (r n) (r (n + 1))

/-- Iterate the uniquely characterized neighbor toward the infinite side. -/
def infiniteRay (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) (n : ℕ) : Site 2 := (infiniteDirection ω hT hEnd)^[n] x

theorem infiniteRay_zero (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : infiniteRay ω hT hEnd x 0 = x := rfl

theorem infiniteRay_succ (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) (n : ℕ) :
    infiniteRay ω hT hEnd x (n + 1) =
      infiniteDirection ω hT hEnd (infiniteRay ω hT hEnd x n) :=
  Function.iterate_succ_apply' _ _ _

private def rayPrefix (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : ∀ n : ℕ, (toGraph ω).Walk x (infiniteRay ω hT hEnd x n)
  | 0 => .nil
  | n + 1 => ((rayPrefix ω hT hEnd x n).concat
      (infiniteDirection_spec ω hT hEnd (infiniteRay ω hT hEnd x n)).1).copy
        rfl (infiniteRay_succ ω hT hEnd x n).symm

private theorem rayPrefix_support (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) (n : ℕ) :
    (rayPrefix ω hT hEnd x n).support = (List.range (n + 1)).map (infiniteRay ω hT hEnd x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rayPrefix, Walk.support_copy, Walk.support_concat, ih,
      List.range_succ, List.map_append, List.map_cons, List.map_nil, infiniteRay_succ]

private theorem rayPrefix_isPath (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) (n : ℕ) : (rayPrefix ω hT hEnd x n).IsPath := by
  induction n with
  | zero => exact Walk.IsPath.nil
  | succ n ih =>
    simp only [rayPrefix, Walk.isPath_copy]
    apply ih.concat _ (infiniteDirection_spec ω hT hEnd (infiniteRay ω hT hEnd x n)).1
    intro hmem
    cases n with
    | zero =>
      change infiniteDirection ω hT hEnd x ∈ [x] at hmem
      exact (infiniteDirection_spec ω hT hEnd x).1.ne (List.mem_singleton.mp hmem).symm
    | succ k =>
      have heq := hT.isAcyclic.eq_penultimate_of_adj_end ih
        (infiniteDirection_spec ω hT hEnd (infiniteRay ω hT hEnd x (k + 1))).1 hmem
      have hp : (rayPrefix ω hT hEnd x (k + 1)).penultimate = infiniteRay ω hT hEnd x k := by
        simp only [rayPrefix, Walk.penultimate, Walk.length_copy, Walk.getVert_copy]
        exact Walk.penultimate_concat _ _
      rw [hp, infiniteRay_succ] at heq
      exact infiniteDirection_no_backtrack ω hT hEnd (infiniteRay ω hT hEnd x k) heq

theorem infiniteRay_injective (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : Function.Injective (infiniteRay ω hT hEnd x) := by
  intro m n heq
  have hnd := (rayPrefix_isPath ω hT hEnd x (max m n)).support_nodup
  rw [rayPrefix_support] at hnd
  exact (List.nodup_map_iff_inj_on List.nodup_range).mp hnd m
    (List.mem_range.mpr (Nat.lt_succ_of_le (le_max_left _ _))) n
    (List.mem_range.mpr (Nat.lt_succ_of_le (le_max_right _ _))) heq

theorem infiniteRay_isSimpleRay (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : IsSimpleRay ω x (infiniteRay ω hT hEnd x) := by
  refine ⟨rfl, infiniteRay_injective ω hT hEnd x, ?_⟩
  intro n
  rw [infiniteRay_succ]
  exact (infiniteDirection_spec ω hT hEnd (infiniteRay ω hT hEnd x n)).1

private theorem simpleRay_first_side_infinite (ω : EdgeField) (r : ℕ → Site 2)
    (hinj : Function.Injective r) (hadj : ∀ n, (toGraph ω).Adj (r n) (r (n + 1))) :
    (((toGraph ω).deleteEdges {s(r 0, r 1)}).connectedComponentMk (r 1)).supp.Infinite := by
  have hreach : ∀ n, ((toGraph ω).deleteEdges {s(r 0, r 1)}).Reachable (r 1) (r (n + 1)) := by
    intro n
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      apply ih.trans
      apply SimpleGraph.Adj.reachable
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hadj (n + 1), ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      rcases Sym2.eq_iff.mp heq with h | h
      · have he := hinj h.1; omega
      · have he := hinj h.2; omega
  have hi : Function.Injective (fun n : ℕ => r (n + 1)) := by
    intro m n he
    exact Nat.add_right_cancel (hinj he)
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n, rfl⟩
  exact SimpleGraph.ConnectedComponent.sound (hreach n).symm

theorem simpleRay_step_direction (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) (r : ℕ → Site 2) (hr : IsSimpleRay ω x r) (n : ℕ) :
    r (n + 1) = infiniteDirection ω hT hEnd (r n) := by
  apply (infiniteDirection_characterization ω hT hEnd (r n) (r (n + 1))).mpr
  refine ⟨hr.2.2 n, ?_⟩
  exact simpleRay_first_side_infinite ω (fun k => r (n + k))
    (fun a b h => Nat.add_left_cancel (hr.2.1 h))
    (fun k => by simpa only [Nat.add_assoc] using hr.2.2 (n + k))

/-- Every infinite simple path from a vertex is the actual iterated outgoing ray. -/
theorem infiniteRay_characterization (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) (r : ℕ → Site 2) : r = infiniteRay ω hT hEnd x ↔ IsSimpleRay ω x r := by
  constructor
  · rintro rfl; exact infiniteRay_isSimpleRay ω hT hEnd x
  · intro hr
    funext n
    induction n with
    | zero => exact hr.1
    | succ n ih =>
      rw [simpleRay_step_direction ω hT hEnd x r hr n, ih, infiniteRay_succ]

theorem existsUnique_simpleRay (ω : EdgeField) (hT : IsTree ω)
    (hEnd : ∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite)
    (x : Site 2) : ∃! r : ℕ → Site 2, IsSimpleRay ω x r :=
  ⟨infiniteRay ω hT hEnd x, infiniteRay_isSimpleRay ω hT hEnd x,
    fun r hr => (infiniteRay_characterization ω hT hEnd x r).mpr hr⟩

end
end FiniteAvalanches.Trees.Lattice
