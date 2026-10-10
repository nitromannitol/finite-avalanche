import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace FiniteAvalanches.External
open scoped BigOperators

/-- Finite nested projection DPP domination and its equivalent monotone coupling.
Event domination: Lyons (2003), Theorem 6.2, p.183.
Coupling: derived finite corollary of Edwards (1978), Theorem 7.3, pp.76–77
(equivalently Theorem 4.1, p.59, plus finite layer-cake). -/
axiom lyons_nestedProjectionDomination
    {E : Type*} [Fintype E] [DecidableEq E]
    (Q₁ Q₂ : Matrix E E ℝ)
    (hQ₁s : Q₁.IsSymm) (hQ₁i : Q₁ * Q₁ = Q₁)
    (hQ₂s : Q₂.IsSymm) (hQ₂i : Q₂ * Q₂ = Q₂)
    (hle : LinearMap.range Q₁.mulVecLin ≤ LinearMap.range Q₂.mulVecLin)
    (p₁ p₂ : Finset E → ℝ) (hp₁ : ∀ S, 0 ≤ p₁ S) (hp₂ : ∀ S, 0 ≤ p₂ S)
    (hdet₁ : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₁ S =
      (Q₁.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det)
    (hdet₂ : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₂ S =
      (Q₂.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det) :
    (∀ ev : Set (Finset E), (∀ S ∈ ev, ∀ e : E, insert e S ∈ ev) →
      ∑ S, Set.indicator ev p₁ S ≤ ∑ S, Set.indicator ev p₂ S) ∧
    (∃ q : Finset E → Finset E → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = p₁ S) ∧
      (∀ T, ∑ S, q S T = p₂ T) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, ¬ S ⊆ T → q S T = 0))

end FiniteAvalanches.External
