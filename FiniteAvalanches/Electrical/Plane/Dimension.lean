import FiniteAvalanches.Electrical.Plane.Incidence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Finite-dimensional incidence facts used to prove, rather than assume, integrability. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- One fixed root removes exactly one coordinate, even on a singleton carrier. -/
theorem card_nonroot {X : Type*} [Fintype X] (root : X) :
    Fintype.card {x : X // x ≠ root} = Fintype.card X-1 := by
  simpa only [Fintype.card_subtype_eq] using Fintype.card_subtype_compl (fun x : X => x = root)

/-- Coordinates on all nonroot vertices, extended by the prescribed zero gauge. -/
noncomputable def rootExtend {X : Type*} (root : X) :
    ({x : X // x ≠ root} → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun q x := if h : x = root then 0 else q ⟨x,h⟩
  map_add' q r := by
    funext x
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' r q := by
    funext x
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    split_ifs <;> simp

@[simp] theorem rootExtend_root {X : Type*} (root : X) (q : {x : X // x ≠ root} → ℝ) :
    rootExtend root q root = 0 := by simp [rootExtend]

@[simp] theorem rootExtend_nonroot {X : Type*} (root : X) (q : {x : X // x ≠ root} → ℝ)
    (x : {x : X // x ≠ root}) : rootExtend root q x.val = q x := by
  simp only [rootExtend,LinearMap.coe_mk,AddHom.coe_mk,dif_neg x.property]

/-- The gauge-coordinate extension is injective before it is composed with any gradient. -/
theorem rootExtend_injective {X : Type*} (root : X) : Function.Injective (rootExtend root) := by
  intro q r h
  funext x
  have hx := congrFun h x.val
  simpa only [rootExtend_nonroot] using hx

/-- Rank-nullity with a proved surjective anchored incidence map. -/
theorem finrank_ker_anchoredBoundary {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (root : V) (hc : (supportGraph a b).Preconnected) :
    Module.finrank ℝ (LinearMap.ker (anchoredBoundary a b root))+
      (Fintype.card V-1) = Fintype.card E := by
  have hr : LinearMap.range (anchoredBoundary a b root) = ⊤ :=
    LinearMap.range_eq_top.mpr (anchoredBoundary_surjective a b root hc)
  have hd := (anchoredBoundary a b root).finrank_range_add_finrank_ker
  rw [hr,finrank_top,Module.finrank_pi,card_nonroot,Module.finrank_pi] at hd
  omega

/-- An injective linear map into a finite-dimensional space of equal dimension is onto. -/
theorem surjective_of_injective_of_finrank_eq {X Y : Type*}
    [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
    (f : X →ₗ[ℝ] Y) (hi : Function.Injective f)
    (hd : Module.finrank ℝ X = Module.finrank ℝ Y) : Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact (LinearMap.finrank_range_of_inj hi).trans hd

end FiniteAvalanches.Electrical.Plane
