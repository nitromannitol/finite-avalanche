import FiniteAvalanches.Wilson.CyclePopping.StackSplice
import Mathlib.Topology.Constructions

/-! Fixed-cursor cycle-popping events depend on finitely many stack instructions. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Filter
open scoped Classical Topology

noncomputable section

variable {V : Type*} {A : V → Type*} [Fintype V]
variable [∀ v, TopologicalSpace (A v)] [∀ v, DiscreteTopology (A v)]

/-- A finite stack prefix agrees with the original stack in a neighborhood. -/
theorem eventually_stack_agrees_below (σ : Stacks A) (l : Cursor V) :
    ∀ᶠ τ : Stacks A in 𝓝 σ, ∀ v i, i < l v → τ v i = σ v i := by
  have h : ∀ᶠ τ : Stacks A in 𝓝 σ, ∀ v (i : Fin (l v)), τ v i.val = σ v i.val := by
    apply eventually_all.mpr
    intro v
    apply eventually_all.mpr
    intro i
    have hc : Continuous (fun τ : Stacks A => τ v i.val) :=
      (continuous_apply i.val).comp (continuous_apply v)
    exact hc.continuousAt.eventually_mem
      ((isOpen_discrete ({σ v i.val} : Set (A v))).mem_nhds (Set.mem_singleton _))
  filter_upwards [h] with τ hτ v i hi
  exact hτ v ⟨i, hi⟩

/-- Reachability of a fixed cursor by legal cycle popping is an open stack event. -/
theorem isOpen_pop_run [DecidableEq V] (R : Set V) (head : (v : V) → A v → V)
    (k l : Cursor V) :
    IsOpen {σ : Stacks A | Relation.ReflTransGen (pop_step R head σ) k l} := by
  apply isOpen_iff_mem_nhds.mpr
  intro σ hσ
  filter_upwards [eventually_stack_agrees_below σ l] with τ hτ
  exact pop_run_congr_below R head hσ (fun v i hi => (hτ v i hi).symm)

/-- At a fixed cursor, terminality depends only on the finitely many top instructions. -/
theorem isOpen_terminal (R : Set V) (head : (v : V) → A v → V) (l : Cursor V) :
    IsOpen {σ : Stacks A | terminal R head σ l} := by
  apply isOpen_iff_mem_nhds.mpr
  intro σ hσ
  have h : ∀ᶠ τ : Stacks A in 𝓝 σ, ∀ v, τ v (l v) = σ v (l v) := by
    apply eventually_all.mpr
    intro v
    have hc : Continuous (fun τ : Stacks A => τ v (l v)) :=
      (continuous_apply (l v)).comp (continuous_apply v)
    exact hc.continuousAt.eventually_mem
      ((isOpen_discrete ({σ v (l v)} : Set (A v))).mem_nhds (Set.mem_singleton _))
  filter_upwards [h] with τ hτ
  change terminal R head σ l at hσ
  have hn : next head τ l = next head σ l := by
    funext v
    simp only [next, top, hτ v]
  simpa only [terminal, hn] using hσ

end
end FiniteAvalanches.Wilson.CyclePopping
