import FiniteAvalanches.Electrical.Geometry.DiskDrawing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Audited classical disk-alternation input.
This derived standard result is registered against Thomassen1992 Lemma2.1 and Lemma2.13,
with an independent derivation covering arbitrary compact connected continua.
The registered input is pure topology. It supplies no graph-to-disk construction,
boundary-angle extraction, or manuscript electrical estimate. -/
namespace FiniteAvalanches.External
open FiniteAvalanches.Electrical.StatementGeometry

/-- Classical crosscut corollary of Thomassen1992 Lemma2.1(p118) and Lemma2.13(pp122–123).
Compact connected sets, without a path-connected assumption, are reduced to disjoint
polygonal crosscuts by inward scaling, connected open neighborhoods, radial extension
and finite polygonal loop pruning. Lemma2.13 excludes alternating crosscut endpoints.
No graph, path law, rotation, Euler, response or paper estimate occurs in this input. -/
axiom disk_alternation_impossible (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (K L : Set (ℝ × ℝ)) (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKd : K ⊆ disk) (hLd : L ⊆ disk)
    (hKL : Disjoint K L)
    (h₁ : (Real.cos θ₁, Real.sin θ₁) ∈ K) (h₃ : (Real.cos θ₃, Real.sin θ₃) ∈ K)
    (h₂ : (Real.cos θ₂, Real.sin θ₂) ∈ L) (h₄ : (Real.cos θ₄, Real.sin θ₄) ∈ L) : False

end FiniteAvalanches.External
