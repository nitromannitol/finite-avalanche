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

/-- A direction copy records exactly the lattice edge traversed from its source. -/
theorem wiredCopyLatticeEdge_directionEdge {B : ℕ} (x : FiniteWired.Active B)
    (d : FiniteWired.Direction) :
    wiredCopyLatticeEdge (FiniteWired.directionEdge x d) =
      ⟨s(FiniteWired.site x, FiniteWired.site x + FiniteWired.step d),
        lattice_adj_direction_step (FiniteWired.site x) d⟩ := by
  rcases d with ⟨i, b⟩
  cases b
  · by_cases h : FiniteWired.inBox B (FiniteWired.site x - unit i)
    · apply Subtype.ext
      simp only [FiniteWired.directionEdge, dif_pos h, wiredCopyLatticeEdge, interiorEdge,
        FiniteWired.site_activeOfSite, FiniteWired.step, Bool.false_eq_true, if_false,
        ← sub_eq_add_neg]
      exact Sym2.eq_swap
    · apply Subtype.ext
      simp only [FiniteWired.directionEdge, dif_neg h, wiredCopyLatticeEdge]
  · by_cases h : FiniteWired.inBox B (FiniteWired.site x + unit i)
    · apply Subtype.ext
      simp only [FiniteWired.directionEdge, dif_pos h, wiredCopyLatticeEdge, interiorEdge,
        FiniteWired.site_activeOfSite, FiniteWired.step, if_true]
    · apply Subtype.ext
      simp only [FiniteWired.directionEdge, dif_neg h, wiredCopyLatticeEdge]

/-- Every lattice edge incident to the box is represented by a wired copy. -/
theorem exists_wiredCopy_of_endpoint_inBox (B : ℕ) (e : LatticeEdge)
    (hbox : ∃ z ∈ e.val, FiniteWired.inBox B z) :
    ∃ q : FiniteWired.Edge B, wiredCopyLatticeEdge q = e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxy : (lattice 2).Adj x y := he
    have hxory : FiniteWired.inBox B x ∨ FiniteWired.inBox B y := by
      obtain ⟨z, hz, hzbox⟩ := hbox
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact Or.inl hzbox
      · exact Or.inr hzbox
    have hstep (u v : Site 2) (hu : FiniteWired.inBox B u) (huv : (lattice 2).Adj u v) :
        ∃ q : FiniteWired.Edge B, (wiredCopyLatticeEdge q).val = s(u, v) := by
      obtain ⟨i, hi | hi⟩ := huv
      · let a := FiniteWired.activeOfSite B u hu
        refine ⟨FiniteWired.directionEdge a (i, true), ?_⟩
        rw [wiredCopyLatticeEdge_directionEdge]
        simp only [FiniteWired.step, if_true]
        change s(u, u + unit i) = s(u, v)
        rw [hi]
      · let a := FiniteWired.activeOfSite B u hu
        refine ⟨FiniteWired.directionEdge a (i, false), ?_⟩
        rw [wiredCopyLatticeEdge_directionEdge]
        simp only [FiniteWired.step, Bool.false_eq_true, if_false, ← sub_eq_add_neg]
        change s(u, u - unit i) = s(u, v)
        have hv : u - unit i = v := by rw [hi]; abel
        rw [hv]
    rcases hxory with hx | hy
    · obtain ⟨q, hq⟩ := hstep x y hx hxy
      exact ⟨q, Subtype.ext hq⟩
    · obtain ⟨q, hq⟩ := hstep y x hy hxy.symm
      refine ⟨q, Subtype.ext ?_⟩
      exact hq.trans Sym2.eq_swap

end
end FiniteAvalanches.Wilson.Lattice
