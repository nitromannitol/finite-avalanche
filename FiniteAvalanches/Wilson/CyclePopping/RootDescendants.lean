import FiniteAvalanches.Wilson.CyclePopping.RootOrbits

/-! Descendant cuts of a rootward arrow configuration. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Function
open scoped Classical

noncomputable section

variable {V : Type*}

/-- Vertices whose arrow orbit reaches `u` before the first root. -/
def rootDescendants (R : Set V) (f : V → V) (h : ∀ v, ∃ n, f^[n] v ∈ R)
    (u : V) : Set V :=
  {v | ∃ n, f^[n] v = u ∧ Nat.find (h u) + n = Nat.find (h v)}

/-- Every vertex is its own rootward descendant. -/
theorem mem_rootDescendants_self (R : Set V) (f : V → V)
    (h : ∀ v, ∃ n, f^[n] v ∈ R) (u : V) : u ∈ rootDescendants R f h u := by
  exact ⟨0, rfl, Nat.add_zero _⟩

/-- A nonroot's successor lies outside its descendant set. -/
theorem successor_not_mem_rootDescendants (R : Set V) (f : V → V)
    (h : ∀ v, ∃ n, f^[n] v ∈ R) {u : V} (hu : u ∉ R) :
    f u ∉ rootDescendants R f h u := by
  rintro ⟨n, _, hn⟩
  have ht := firstRootTime_succ R f h hu
  omega

/-- At any other nonroot, a vertex and its successor lie on the same side
of the descendant cut. -/
theorem mem_rootDescendants_iff_successor (R : Set V) (f : V → V)
    (h : ∀ v, ∃ n, f^[n] v ∈ R) {u v : V} (hv : v ∉ R) (hvu : v ≠ u) :
    v ∈ rootDescendants R f h u ↔ f v ∈ rootDescendants R f h u := by
  have ht := firstRootTime_succ R f h hv
  constructor
  · rintro ⟨n, hn, htime⟩
    cases n with
    | zero => exact (hvu hn).elim
    | succ n =>
      refine ⟨n, ?_, ?_⟩
      · rw [Function.iterate_succ_apply] at hn
        exact hn
      · omega
  · rintro ⟨n, hn, htime⟩
    refine ⟨n + 1, ?_, ?_⟩
    · rw [Function.iterate_succ_apply]
      exact hn
    · omega

end
end FiniteAvalanches.Wilson.CyclePopping
