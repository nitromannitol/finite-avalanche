import FiniteAvalanches.Electrical.Network
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Linarith

/-! Finite Dirichlet problems with individually indexed unit-conductance edges. -/

namespace FiniteAvalanches.Electrical

open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem energy_nonneg (a b : E → V) (f : V → ℝ) : 0 ≤ energy a b f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Fintype V] in
theorem energy_eq_zero_iff (a b : E → V) (f : V → ℝ) :
    energy a b f = 0 ↔ ∀ e, f (a e) = f (b e) := by
  rw [energy, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, sub_eq_zero]

omit [Fintype V] in
theorem laplacian_add (a b : E → V) (f g : V → ℝ) (x : V) :
    laplacian a b (f + g) x = laplacian a b f x + laplacian a b g x := by
  simp only [laplacian, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by split_ifs <;> ring

omit [Fintype V] in
theorem laplacian_smul (a b : E → V) (r : ℝ) (f : V → ℝ) (x : V) :
    laplacian a b (r • f) x = r * laplacian a b f x := by
  simp only [laplacian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by split_ifs <;> ring

omit [Fintype V] in
theorem laplacian_sub (a b : E → V) (f g : V → ℝ) (x : V) :
    laplacian a b (f - g) x = laplacian a b f x - laplacian a b g x := by
  simp only [laplacian, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e _ => by split_ifs <;> ring

omit [Fintype V] [Fintype E] in
theorem eq_of_reachable (a b : E → V) (f : V → ℝ)
    (hf : ∀ e, f (a e) = f (b e)) {x y : V}
    (hxy : (supportGraph a b).Reachable x y) : f x = f y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => rfl
  | cons h p ih =>
    obtain ⟨_, e, he⟩ := h
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hf e).trans ih
    · exact (hf e).symm.trans ih

/-- A zero-boundary harmonic function vanishes when each component meets the boundary. -/
theorem eq_zero_of_harmonic (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y)
    (f : V → ℝ) (hfB : ∀ x ∈ B, f x = 0)
    (hf : ∀ x, x ∉ B → laplacian a b f x = 0) : f = 0 := by
  have he : energy a b f = 0 := by
    rw [energy_eq_incidence_sum]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x ∈ B
    · rw [hfB x hx, zero_mul]
    · rw [hf x hx, mul_zero]
  have hedge := (energy_eq_zero_iff a b f).mp he
  funext x
  obtain ⟨y, hy, hxy⟩ := hB x
  exact (eq_of_reachable a b f hedge hxy).trans (hfB y hy)

/-- Extend free-vertex data by zero at boundary vertices. -/
noncomputable def zeroExtend (B : Finset V) (u : {x // x ∉ B} → ℝ) (x : V) : ℝ :=
  if hx : x ∈ B then 0 else u ⟨x, hx⟩

/-- The positive Dirichlet Laplacian on free vertices. -/
noncomputable def dirichletMap (a b : E → V) (B : Finset V) :
    ({x // x ∉ B} → ℝ) →ₗ[ℝ] ({x // x ∉ B} → ℝ) where
  toFun u x := laplacian a b (zeroExtend B u) x
  map_add' u w := by
    have h : zeroExtend B (u + w) = zeroExtend B u + zeroExtend B w := by
      funext x; simp only [zeroExtend, Pi.add_apply]; split_ifs <;> simp
    funext x; rw [h, laplacian_add]; rfl
  map_smul' r u := by
    have h : zeroExtend B (r • u) = r • zeroExtend B u := by
      funext x; simp only [zeroExtend, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    funext x; rw [h, laplacian_smul]; rfl

theorem dirichletMap_injective (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y) :
    Function.Injective (dirichletMap a b B) := by
  intro u w huw
  have hf : zeroExtend B u - zeroExtend B w = 0 := by
    apply eq_zero_of_harmonic a b B hB
    · intro x hx
      simp only [Pi.sub_apply, zeroExtend, dif_pos hx, sub_self]
    · intro x hx
      rw [laplacian_sub]
      exact sub_eq_zero.mpr (congrFun huw ⟨x, hx⟩)
  funext x
  have hx := congrFun hf x.val
  simpa only [Pi.sub_apply, zeroExtend, dif_neg x.property, Pi.zero_apply,
    sub_eq_zero] using hx

/-- Existence and uniqueness are proved before any harmonic extension is selected. -/
theorem existsUnique_harmonic_extension (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y) (t : V → ℝ) :
    ∃! f : V → ℝ, (∀ x ∈ B, f x = t x) ∧
      (∀ x, x ∉ B → laplacian a b f x = 0) := by
  let v : V → ℝ := fun x => if x ∈ B then t x else 0
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective
    (dirichletMap_injective a b B hB) (fun x => -laplacian a b v x)
  refine ⟨v + zeroExtend B u, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [Pi.add_apply, v, if_pos hx, zeroExtend, dif_pos hx, add_zero]
  · intro x hx
    rw [laplacian_add]
    have hux := congrFun hu ⟨x, hx⟩
    change laplacian a b (zeroExtend B u) x = -laplacian a b v x at hux
    rw [hux, add_neg_cancel]
  · intro f hf
    have hz : f - (v + zeroExtend B u) = 0 := by
      apply eq_zero_of_harmonic a b B hB
      · intro x hx
        simp only [Pi.sub_apply, hf.1 x hx, Pi.add_apply, v, if_pos hx,
          zeroExtend, dif_pos hx, add_zero, sub_self]
      · intro x hx
        rw [laplacian_sub, hf.2 x hx, laplacian_add]
        have hux := congrFun hu ⟨x, hx⟩
        change laplacian a b (zeroExtend B u) x = -laplacian a b v x at hux
        rw [hux, add_neg_cancel, sub_self]
    exact sub_eq_zero.mp hz

/-- The harmonic extension of specified boundary values. -/
noncomputable def harmonicExtension (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y) (t : V → ℝ) : V → ℝ :=
  (existsUnique_harmonic_extension a b B hB t).choose

theorem harmonicExtension_spec (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y) (t : V → ℝ) :
    (∀ x ∈ B, harmonicExtension a b B hB t x = t x) ∧
      (∀ x, x ∉ B → laplacian a b (harmonicExtension a b B hB t) x = 0) :=
  (existsUnique_harmonic_extension a b B hB t).choose_spec.1

theorem harmonicExtension_eq (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y) (t f : V → ℝ)
    (hf : (∀ x ∈ B, f x = t x) ∧
      (∀ x, x ∉ B → laplacian a b f x = 0)) :
    f = harmonicExtension a b B hB t :=
  (existsUnique_harmonic_extension a b B hB t).choose_spec.2 f hf

omit [Fintype V] in
theorem laplacian_const (a b : E → V) (r : ℝ) (x : V) :
    laplacian a b (fun _ => r) x = 0 := by
  simp only [laplacian, sub_self, ite_self, add_zero, Finset.sum_const_zero]

/-- Exact quadratic expansion; its cross term is a finite incidence sum. -/
theorem energy_sub_expansion (a b : E → V) (f h : V → ℝ) :
    energy a b f = energy a b h + energy a b (f - h) +
      2 * ∑ x, (f x - h x) * laplacian a b h x := by
  rw [incidence_sum a b h (fun x => f x - h x)]
  unfold energy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by simp only [Pi.sub_apply]; ring

/-- Dirichlet minimization with the complete nonnegative error retained. -/
theorem energy_eq_add_energy_sub_of_harmonic (a b : E → V) (B : Finset V)
    (f h : V → ℝ) (hf : ∀ x ∈ B, f x = h x)
    (hh : ∀ x, x ∉ B → laplacian a b h x = 0) :
    energy a b f = energy a b h + energy a b (f - h) := by
  rw [energy_sub_expansion]
  have hz : (∑ x, (f x - h x) * laplacian a b h x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x ∈ B
    · rw [hf x hx, sub_self, zero_mul]
    · rw [hh x hx, mul_zero]
  rw [hz, mul_zero, add_zero]

theorem energy_harmonicExtension_le (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y)
    (t f : V → ℝ) (hf : ∀ x ∈ B, f x = t x) :
    energy a b (harmonicExtension a b B hB t) ≤ energy a b f := by
  have hs := harmonicExtension_spec a b B hB t
  rw [energy_eq_add_energy_sub_of_harmonic a b B f _
    (fun x hx => (hf x hx).trans (hs.1 x hx).symm) hs.2]
  exact le_add_of_nonneg_right (energy_nonneg a b _)

end FiniteAvalanches.Electrical
