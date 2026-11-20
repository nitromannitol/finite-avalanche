import FiniteAvalanches.Wilson.Lattice.WiredObservationGeometry

/-! Original lattice edges underlying all wired-box copies, including exits. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Every signed coordinate step is a square-lattice edge. -/
theorem lattice_adj_direction_step (x : Site 2) (d : FiniteWired.Direction) :
    (lattice 2).Adj x (x + FiniteWired.step d) := by
  rcases d with ⟨i, b⟩
  cases b
  · refine ⟨i, Or.inr ?_⟩
    simp only [FiniteWired.step, Bool.false_eq_true, if_false]
    abel
  · exact ⟨i, Or.inl (by simp [FiniteWired.step])⟩

/-- Each wired copy retains its original lattice edge, including edges exiting the box. -/
def wiredCopyLatticeEdge {B : ℕ} : FiniteWired.Edge B → LatticeEdge
  | .inl i => interiorEdge i
  | .inr i => ⟨s(FiniteWired.site i.val.1, FiniteWired.site i.val.1 + FiniteWired.step i.val.2),
      lattice_adj_direction_step (FiniteWired.site i.val.1) i.val.2⟩

/-- An interior copy records its original lattice edge. -/
theorem wiredCopyLatticeEdge_interior {B : ℕ} (i : FiniteWired.InteriorEdge B) :
    wiredCopyLatticeEdge (.inl i) = interiorEdge i := rfl

/-- Exit copies have one endpoint in the box and one endpoint outside it. -/
theorem exitEdge_inBox_and_outside {B : ℕ} (i : FiniteWired.ExitEdge B) :
    FiniteWired.inBox B (FiniteWired.site i.val.1) ∧
      ¬FiniteWired.inBox B (FiniteWired.site i.val.1 + FiniteWired.step i.val.2) :=
  ⟨fun j => (i.val.1 j).property, i.property⟩

/-- Different exit copies retain different original lattice edges. -/
theorem exitEdge_latticeEdge_injective (B : ℕ) :
    Function.Injective (fun i : FiniteWired.ExitEdge B => wiredCopyLatticeEdge (.inr i)) := by
  intro i j hij
  have hp := Sym2.eq_iff.mp (congrArg Subtype.val hij)
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hv : i.val.1 = j.val.1 := FiniteWired.site_injective B h1
    have hd : i.val.2 = j.val.2 := by
      apply FiniteWired.step_injective
      rw [← h1] at h2
      exact add_left_cancel h2
    apply Subtype.ext
    exact Prod.ext hv hd
  · have hinside := (exitEdge_inBox_and_outside i).1
    exact ((exitEdge_inBox_and_outside j).2 (h1 ▸ hinside)).elim

/-- An interior copy and an exit copy cannot represent the same lattice edge. -/
theorem interiorEdge_ne_exitEdge {B : ℕ} (i : FiniteWired.InteriorEdge B)
    (j : FiniteWired.ExitEdge B) : wiredCopyLatticeEdge (.inl i) ≠ wiredCopyLatticeEdge (.inr j) := by
  intro h
  have hp := Sym2.eq_iff.mp (congrArg Subtype.val h)
  rcases hp with ⟨_, h2⟩ | ⟨h1, _⟩
  · have hin : FiniteWired.inBox B (FiniteWired.site i.val.2) := fun d => (i.val.2 d).property
    exact (exitEdge_inBox_and_outside j).2 (h2 ▸ hin)
  · have hin : FiniteWired.inBox B (FiniteWired.site i.val.1) := fun d => (i.val.1 d).property
    exact (exitEdge_inBox_and_outside j).2 (h1 ▸ hin)

/-- The full wired edge-copy carrier injects into the original lattice edges. -/
theorem wiredCopyLatticeEdge_injective (B : ℕ) :
    Function.Injective (@wiredCopyLatticeEdge B) := by
  intro e f h
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (interiorEdge_injective B h)
    | inr f => exact (interiorEdge_ne_exitEdge e f h).elim
  | inr e =>
    cases f with
    | inl f => exact (interiorEdge_ne_exitEdge f e h.symm).elim
    | inr f => exact congrArg Sum.inr (exitEdge_latticeEdge_injective B h)

end
end FiniteAvalanches.Wilson.Lattice
