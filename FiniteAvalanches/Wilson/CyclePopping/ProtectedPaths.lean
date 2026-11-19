import FiniteAvalanches.Wilson.CyclePopping.Basic

/-! Cycle pops preserve arrows already leading through a protected set to roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open scoped Classical

noncomputable section

variable {V : Type*} {A : V → Type*}

private theorem reaches_of_eq_before_root {R B : Set V} {f g : V → V}
    (hclosed : ∀ v ∈ B, v ∉ R → f v ∈ B)
    (heq : ∀ v ∈ B, v ∉ R → f v = g v) :
    ∀ n v, v ∈ B → f^[n] v ∈ R → ∃ m, g^[m] v ∈ R := by
  intro n
  induction n with
  | zero =>
    intro v _ hv
    exact ⟨0, hv⟩
  | succ n ih =>
    intro v hv hn
    by_cases hr : v ∈ R
    · exact ⟨0, hr⟩
    · rw [Function.iterate_succ_apply] at hn
      obtain ⟨m, hm⟩ := ih (f v) (hclosed v hv hr) hn
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply, ← heq v hv hr]
      exact hm

/-- A legal directed cycle cannot meet a vertex whose orbit reaches a root. -/
theorem IsCycle.disjoint_of_reaches_root {R B : Set V} {f : V → V} {c : Finset V}
    (hc : IsCycle R f c) (hreaches : ∀ v ∈ B, ∃ n, f^[n] v ∈ R) :
    Disjoint (c : Set V) B := by
  apply Set.disjoint_left.mpr
  intro v hv hB
  obtain ⟨n, hn⟩ := hreaches v hB
  exact hc.avoids_roots _ (hc.iterate_mem hv n) hn

variable [DecidableEq V]

/-- If selected arrows stay within a set until reaching the roots, any later legal
cycle-pop run leaves every cursor on that set unchanged. -/
theorem pop_run_preserves_rootward_set (R B : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) {k l : Cursor V}
    (hclosed : ∀ v ∈ B, v ∉ R → next head σ k v ∈ B)
    (hreaches : ∀ v ∈ B, ∃ n, (next head σ k)^[n] v ∈ R)
    (hrun : Relation.ReflTransGen (pop_step R head σ) k l) :
    ∀ v ∈ B, l v = k v := by
  induction hrun with
  | refl => intro _ _; rfl
  | @tail m l hkm hml ih =>
    have heq : ∀ v ∈ B, v ∉ R → next head σ k v = next head σ m v := by
      intro v hv _
      simp only [next, top, ih v hv]
    have hreachm : ∀ v ∈ B, ∃ n, (next head σ m)^[n] v ∈ R := by
      intro v hv
      obtain ⟨n, hn⟩ := hreaches v hv
      exact reaches_of_eq_before_root hclosed heq n v hv hn
    obtain ⟨c, hc, rfl⟩ := hml
    have hdis := hc.disjoint_of_reaches_root hreachm
    intro v hv
    have hnot : v ∉ c := fun hvc => Set.disjoint_left.mp hdis hvc hv
    rw [pop_apply_of_not_mem m c hnot]
    exact ih v hv

/-- The selected instructions on a protected rootward set persist throughout
every finite legal cycle-pop run. -/
theorem top_eq_of_pop_run_on_rootward_set (R B : Set V)
    (head : (v : V) → A v → V) (σ : Stacks A) {k l : Cursor V}
    (hclosed : ∀ v ∈ B, v ∉ R → next head σ k v ∈ B)
    (hreaches : ∀ v ∈ B, ∃ n, (next head σ k)^[n] v ∈ R)
    (hrun : Relation.ReflTransGen (pop_step R head σ) k l) {v : V} (hv : v ∈ B) :
    top σ l v = top σ k v := by
  simp only [top, pop_run_preserves_rootward_set R B head σ hclosed hreaches hrun v hv]

end
end FiniteAvalanches.Wilson.CyclePopping
