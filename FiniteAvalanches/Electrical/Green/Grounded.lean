import FiniteAvalanches.Electrical.Dirichlet
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The grounded Green kernel of the actual positive copied Laplacian. -/
namespace FiniteAvalanches.Electrical
open scoped BigOperators Classical
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Arbitrary Poisson data have a unique zero-ground solution on a connected copied network. -/
theorem existsUnique_grounded_poisson (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (r : V → ℝ) :
    ∃! f : V → ℝ, f v = 0 ∧ ∀ x, x ≠ v → laplacian a b f x = r x := by
  let B : Finset V := {v}
  have hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y := fun x => ⟨v,by simp [B],hc x v⟩
  obtain ⟨u,hu⟩ := LinearMap.surjective_of_injective (dirichletMap_injective a b B hB)
    (fun x => r x.val)
  have hspec : zeroExtend B u v = 0 ∧ ∀ x, x ≠ v → laplacian a b (zeroExtend B u) x = r x := by
    constructor
    · simp [zeroExtend,B]
    · intro x hx
      exact congrFun hu ⟨x,by simpa [B] using hx⟩
  refine ⟨zeroExtend B u,hspec,?_⟩
  intro f hf
  have hz : f-zeroExtend B u = 0 := by
    apply eq_zero_of_harmonic a b B hB
    · intro x hx
      have h : x = v := by simpa [B] using hx
      subst x
      simp only [Pi.sub_apply,hf.1,hspec.1,sub_self]
    · intro x hx
      have h : x ≠ v := by simpa [B] using hx
      rw [laplacian_sub,hf.2 x h,hspec.2 x h,sub_self]
  exact sub_eq_zero.mp hz

/-- Selected only after the Poisson existence and uniqueness theorem. -/
noncomputable def groundedPoisson (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (r : V → ℝ) : V → ℝ :=
  (existsUnique_grounded_poisson a b v hc r).choose

theorem groundedPoisson_spec (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (r : V → ℝ) :
    groundedPoisson a b v hc r v = 0 ∧ ∀ x, x ≠ v → laplacian a b (groundedPoisson a b v hc r) x = r x :=
  (existsUnique_grounded_poisson a b v hc r).choose_spec.1

theorem groundedPoisson_eq (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (r f : V → ℝ)
    (hf : f v = 0 ∧ ∀ x, x ≠ v → laplacian a b f x = r x) : f = groundedPoisson a b v hc r :=
  (existsUnique_grounded_poisson a b v hc r).choose_spec.2 f hf

/-- Unit injection at x and grounding at v; injection at v gives the identically zero row. -/
noncomputable def groundedGreen (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (x y : V) : ℝ :=
  groundedPoisson a b v hc (fun z => if z = x then 1 else 0) y

theorem groundedGreen_ground (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (x : V) : groundedGreen a b v hc x v = 0 :=
  (groundedPoisson_spec a b v hc _).1

theorem groundedGreen_laplacian (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (x y : V) (hy : y ≠ v) :
    laplacian a b (groundedGreen a b v hc x) y = if y = x then 1 else 0 :=
  (groundedPoisson_spec a b v hc _).2 y hy

theorem groundedGreen_ground_source (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) : groundedGreen a b v hc v = 0 := by
  apply (groundedPoisson_eq a b v hc _ 0 ?_).symm
  refine ⟨rfl,?_⟩
  intro x hx
  rw [if_neg hx]
  change laplacian a b (fun _ => 0) x = 0
  exact laplacian_const a b 0 x

/-- Pairing with a zero-ground function removes only the actual ground term. -/
theorem groundedGreen_pairing (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (x : V) (f : V → ℝ) (hf : f v = 0) :
    (∑ y, f y*laplacian a b (groundedGreen a b v hc x) y) = f x := by
  calc
    _ = ∑ y, f y*(if y = x then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y = v
      · subst y; rw [hf,zero_mul,zero_mul]
      · rw [groundedGreen_laplacian a b v hc x y hy]
    _ = f x := by simp

/-- Reciprocity follows from the literal copied-edge incidence pairing. -/
theorem groundedGreen_symm (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (x y : V) :
    groundedGreen a b v hc x y = groundedGreen a b v hc y x := by
  have hxy := groundedGreen_pairing a b v hc x (groundedGreen a b v hc y) (groundedGreen_ground a b v hc y)
  have hyx := groundedGreen_pairing a b v hc y (groundedGreen a b v hc x) (groundedGreen_ground a b v hc x)
  rw [incidence_sum] at hxy hyx
  have hs : (∑ e, (groundedGreen a b v hc x (a e)-groundedGreen a b v hc x (b e))*
      (groundedGreen a b v hc y (a e)-groundedGreen a b v hc y (b e))) =
      ∑ e, (groundedGreen a b v hc y (a e)-groundedGreen a b v hc y (b e))*
        (groundedGreen a b v hc x (a e)-groundedGreen a b v hc x (b e)) := by
    apply Finset.sum_congr rfl
    intro e _
    ring
  exact hyx.symm.trans (hs.symm.trans hxy)

/-- Unit-current energy equals the actual Green diagonal, with E counted once. -/
theorem energy_groundedGreen_eq (a b : E → V) (v : V)
    (hc : (supportGraph a b).Preconnected) (x : V) :
    energy a b (groundedGreen a b v hc x) = groundedGreen a b v hc x x := by
  rw [energy_eq_incidence_sum]
  exact groundedGreen_pairing a b v hc x _ (groundedGreen_ground a b v hc x)

end FiniteAvalanches.Electrical
