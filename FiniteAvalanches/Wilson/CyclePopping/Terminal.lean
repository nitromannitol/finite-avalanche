import FiniteAvalanches.Wilson.CyclePopping.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! On a finite graph, a terminal arrow configuration sends every vertex to a root. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Function
open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

/-- An orbit which avoids the roots in a finite graph contains a legal cycle. -/
theorem exists_cycle_of_orbit_avoids (R : Set V) (f : V → V) (x : V)
    (havoid : ∀ n, f^[n] x ∉ R) : ∃ c : Finset V, IsCycle R f c := by
  have hrepeat : ∃ m n : ℕ, m < n ∧ f^[m] x = f^[n] x := by
    obtain ⟨m, n, heq, hne⟩ : ∃ m n : ℕ, f^[m] x = f^[n] x ∧ m ≠ n := by
      simpa [Function.Injective] using not_injective_infinite_finite (fun n : ℕ => f^[n] x)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨m, n, h, heq⟩
    · exact ⟨n, m, h, heq.symm⟩
  obtain ⟨m, n, hmn, heq⟩ := hrepeat
  let a := f^[m] x
  have hp : IsPeriodicPt f (n - m) a := by
    change f^[n - m] (f^[m] x) = f^[m] x
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hmn)]
    exact heq.symm
  have ha : a ∈ periodicPts f := mk_mem_periodicPts (Nat.sub_pos_of_lt hmn) hp
  let c : Finset V := Finset.univ.filter (fun y => ∃ t, f^[t] a = y)
  have hc (y : V) : y ∈ c ↔ ∃ t, f^[t] a = y := by simp [c]
  refine ⟨c, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact ⟨a, (hc a).mpr ⟨0, rfl⟩⟩
  · intro y hy
    obtain ⟨t, rfl⟩ := (hc y).mp hy
    simpa only [a, ← Function.iterate_add_apply] using havoid (t + m)
  · intro y hy
    obtain ⟨t, rfl⟩ := (hc y).mp hy
    exact (hc _).mpr ⟨t + 1, by rw [Function.iterate_succ_apply']⟩
  · intro y hy z hz
    obtain ⟨s, rfl⟩ := (hc y).mp hy
    obtain ⟨t, rfl⟩ := (hc z).mp hz
    have hy : f^[s] a ∈ periodicPts f :=
      mk_mem_periodicPts (Nat.sub_pos_of_lt hmn) (hp.apply_iterate s)
    apply (mem_periodicOrbit_iff hy).mp
    rw [periodicOrbit_apply_iterate_eq ha s]
    exact iterate_mem_periodicOrbit ha t

/-- Terminal configurations are exactly those whose arrows lead every vertex to a root. -/
theorem terminal_iff_reaches_root {A : V → Type*} (R : Set V)
    (head : (v : V) → A v → V) (σ : Stacks A) (k : Cursor V) :
    terminal R head σ k ↔ ∀ x, ∃ n, (next head σ k)^[n] x ∈ R := by
  constructor
  · intro ht x
    by_contra h
    push Not at h
    obtain ⟨c, hc⟩ := exists_cycle_of_orbit_avoids R (next head σ k) x h
    exact ht c hc
  · intro h c hc
    obtain ⟨x, hx⟩ := hc.nonempty
    obtain ⟨n, hn⟩ := h x
    exact hc.avoids_roots _ (hc.iterate_mem hx n) hn

end
end FiniteAvalanches.Wilson.CyclePopping
