import FiniteAvalanches.External.DiskAlternation
import Mathlib.Data.Set.Disjoint
import Mathlib.Tactic.Linarith

/-! Consequences of the disclosed pure disk-alternation input.
The geometric angle data in the drawing application are explicit inputs.
This module proves no graph-to-disk construction or extraction of boundary angles. -/
namespace FiniteAvalanches.Electrical.StatementGeometry

/-- Two continua containing alternating circle points have a common point. -/
theorem alternating_continua_intersect (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (K L : Set (ℝ × ℝ)) (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKd : K ⊆ disk) (hLd : L ⊆ disk)
    (h₁ : (Real.cos θ₁, Real.sin θ₁) ∈ K) (h₃ : (Real.cos θ₃, Real.sin θ₃) ∈ K)
    (h₂ : (Real.cos θ₂, Real.sin θ₂) ∈ L) (h₄ : (Real.cos θ₄, Real.sin θ₄) ∈ L) :
    (K ∩ L).Nonempty := by
  apply Set.not_disjoint_iff_nonempty_inter.mp
  intro hKL
  exact FiniteAvalanches.External.disk_alternation_impossible
    θ₁ θ₂ θ₃ θ₄ h₁₂ h₂₃ h₃₄ h₄₁ K L hK hKc hL hLc hKd hLd hKL h₁ h₃ h₂ h₄

/-- Horizontal and vertical terminal continua meet, even if the continua have no paths. -/
theorem quarter_circle_continua_intersect
    (K L : Set (ℝ × ℝ)) (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKd : K ⊆ disk) (hLd : L ⊆ disk)
    (h₁ : (Real.cos 0, Real.sin 0) ∈ K)
    (h₃ : (Real.cos Real.pi, Real.sin Real.pi) ∈ K)
    (h₂ : (Real.cos (Real.pi / 2), Real.sin (Real.pi / 2)) ∈ L)
    (h₄ : (Real.cos (3 * Real.pi / 2), Real.sin (3 * Real.pi / 2)) ∈ L) :
    (K ∩ L).Nonempty := by
  exact alternating_continua_intersect 0 (Real.pi / 2) Real.pi (3 * Real.pi / 2)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    K L hK hKc hL hLc hKd hLd h₁ h₃ h₂ h₄

namespace Drawing
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E} (drawing : Drawing J)

/-- Literal copied walks construct the continua consumed by the registered pure input.
The whole-disk drawing and ordered angle equalities are supplied geometric data. -/
theorem alternating_walks_impossible {C D : Set V} {s t : Finset E}
    (hCD : Disjoint C D)
    (hs : ∀ e ∈ s, J.left e ∈ C ∧ J.right e ∈ C)
    (ht : ∀ e ∈ t, J.left e ∈ D ∧ J.right e ∈ D)
    (x₀ x₁ y₀ y₁ : V) (hx : x₀ ∈ C) (hy : y₀ ∈ D)
    (hxx : J.reaches s x₀ x₁) (hyy : J.reaches t y₀ y₁)
    (hvertices : ∀ x, drawing.point x ∈ disk)
    (hedges : ∀ e q, drawing.curve e q ∈ disk)
    (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (p₁ : drawing.point x₀ = (Real.cos θ₁, Real.sin θ₁))
    (p₃ : drawing.point x₁ = (Real.cos θ₃, Real.sin θ₃))
    (p₂ : drawing.point y₀ = (Real.cos θ₂, Real.sin θ₂))
    (p₄ : drawing.point y₁ = (Real.cos θ₄, Real.sin θ₄)) : False := by
  obtain ⟨K, L, hK, hKc, hL, hLc, hKd, hLd, hKL, hx₀, hx₁, hy₀, hy₁⟩ :=
    drawing.disjoint_connecting_continua hCD hs ht x₀ x₁ y₀ y₁ hx hy hxx hyy hvertices hedges
  exact FiniteAvalanches.External.disk_alternation_impossible
    θ₁ θ₂ θ₃ θ₄ h₁₂ h₂₃ h₃₄ h₄₁ K L hK hKc hL hLc hKd hLd hKL
    (p₁ ▸ hx₀) (p₃ ▸ hx₁) (p₂ ▸ hy₀) (p₄ ▸ hy₁)

end Drawing
end FiniteAvalanches.Electrical.StatementGeometry
