import FiniteAvalanches.Wilson.Lattice.ColoredForests
import Mathlib.Order.Filter.Basic

/-! Exact source ct:continuity root formation. Nonempty limiting roots are
derived from the fixed source witnesses, never added as extra hypotheses. -/
namespace FiniteAvalanches.Wilson.Lattice.ContinuityAudit
open LatticeProb Filter

theorem fixed_member_in_local_limit {Sj : ℕ → Set (Site 2)} {S : Set (Site 2)}
    (a : Site 2) (ha : ∀ j, a ∈ Sj j)
    (hlocal : ∀ x, ∀ᶠ j in atTop, x ∈ Sj j ↔ x ∈ S) : a ∈ S := by
  obtain ⟨j, hj⟩ := (hlocal a).exists
  exact hj.mp (ha j)

/-- The limiting pair has precisely the source sets, with nonemptiness proved
from the common vertices and local membership convergence. -/
def limitRoots (Rj : ℕ → RootPair) (A C : Set (Site 2)) (hAC : Disjoint A C)
    (a b : Site 2) (ha : ∀ j, a ∈ (Rj j).zero) (hb : ∀ j, b ∈ (Rj j).one)
    (hA : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).zero ↔ x ∈ A)
    (hC : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).one ↔ x ∈ C) : RootPair where
  zero := A
  one := C
  disjoint := hAC
  zero_nonempty := ⟨a, fixed_member_in_local_limit a ha hA⟩
  one_nonempty := ⟨b, fixed_member_in_local_limit b hb hC⟩

theorem fixed_vertices_in_limit (Rj : ℕ → RootPair) (A C : Set (Site 2))
    (a b : Site 2) (ha : ∀ j, a ∈ (Rj j).zero) (hb : ∀ j, b ∈ (Rj j).one)
    (hA : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).zero ↔ x ∈ A)
    (hC : ∀ x, ∀ᶠ j in atTop, x ∈ (Rj j).one ↔ x ∈ C) : a ∈ A ∧ b ∈ C :=
  ⟨fixed_member_in_local_limit a ha hA, fixed_member_in_local_limit b hb hC⟩

end FiniteAvalanches.Wilson.Lattice.ContinuityAudit
