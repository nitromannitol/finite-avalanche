import FiniteAvalanches.Wilson.CyclePopping.RootOrbits
import FiniteAvalanches.Trees.Joining

/-! Root components of the copied edges selected by rootward arrows. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- A finite initial orbit segment avoiding the roots is a copied-edge walk. -/
theorem reaches_iterate_before_root (G : Multigraph V E) (F : Finset E)
    (R : Set V) (f : V → V) (hstep : ∀ v ∉ R, G.adjacent F v (f v))
    (x : V) (n : ℕ) (havoid : ∀ i < n, f^[i] x ∉ R) :
    G.reaches F x (f^[n] x) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (ih (fun i hi => havoid i (Nat.lt_succ_of_lt hi))).tail
      (hstep _ (havoid n (Nat.lt_succ_self n)))

/-- If the copied edges are exactly nonroot arrows and every orbit hits a root,
each graph component contains exactly one original root. -/
theorem rootward_components (G : Multigraph V E) (F : Finset E)
    (R : Set V) (f : V → V) (hhit : ∀ v, ∃ n, f^[n] v ∈ R)
    (hstep : ∀ v ∉ R, G.adjacent F v (f v))
    (hedge : ∀ x y, G.adjacent F x y → rootwardAdj R f x y) :
    ∀ x, ∃ r ∈ R, G.reaches F x r ∧
      ∀ r' ∈ R, G.reaches F x r' → r' = r := by
  intro x
  refine ⟨firstRoot R f hhit x, firstRoot_mem R f hhit x, ?_, ?_⟩
  · apply reaches_iterate_before_root G F R f hstep x (Nat.find (hhit x))
    intro i hi
    exact Nat.find_min (hhit x) hi
  · intro r hr hxr
    have hp : Relation.ReflTransGen (rootwardAdj R f) x r := by
      exact Relation.ReflTransGen.mono (fun u v hxy => hedge u v hxy) x r hxr
    have he := firstRoot_eq_of_rootwardReach R f hhit hp
    rw [firstRoot_of_mem R f hhit hr] at he
    exact he.symm

end
end FiniteAvalanches.Wilson.CyclePopping
