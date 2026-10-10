import FiniteAvalanches.Electrical.Geometry.DiskDrawing

namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- Spanning forest with the prescribed paired terminal components; every component
contains a terminal, and distinct `a` terminals lie in distinct components. -/
abbrev PairingGrove {k : ℕ} (a b : Fin k → V) (π : Equiv.Perm (Fin k)) :=
  {F : Finset E //
    (∀ e ∈ F, ¬J.reaches (F.erase e) (J.left e) (J.right e)) ∧
    (∀ y, ∃ r, J.reaches F y (a r) ∨ J.reaches F y (b r)) ∧
    (∀ r s, J.reaches F (a r) (b s) ↔ s = π r) ∧
    (∀ r s, r ≠ s → ¬J.reaches F (a r) (a s))}

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph

