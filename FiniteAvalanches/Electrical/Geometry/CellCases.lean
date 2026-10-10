import FiniteAvalanches.Model.FiniteWired
import FiniteAvalanches.External.DiskAlternation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeCell
open LatticeProb
open scoped Classical

/-- Counterclockwise physical corners: southwest, southeast, northeast, northwest. -/
def corner (o : Site 2) (i : Fin 4) : Site 2 :=
  o + if i = 0 then 0 else if i = 1 then unit 0 else if i = 2 then unit 0 + unit 1 else unit 1

def NearWithin (D : Set (Site 2)) (o x y : Site 2) : Prop :=
  x = y ∨ (lattice 2).Adj x y ∨
    ∃ w, w ∈ D ∧ (∃ k, w = corner o k) ∧ (lattice 2).Adj x w ∧ (lattice 2).Adj w y

/-- Literal alternating membership of the four translated lattice corners. -/
def Alternating (D : Set (Site 2)) (o : Site 2) : Prop :=
  (corner o 0 ∈ D ∧ corner o 2 ∈ D ∧ corner o 1 ∉ D ∧ corner o 3 ∉ D) ∨
  (corner o 1 ∈ D ∧ corner o 3 ∈ D ∧ corner o 0 ∉ D ∧ corner o 2 ∉ D)

theorem adjacent01 (o : Site 2) : (lattice 2).Adj (corner o 0) (corner o 1) := by
  change ∃ i : Fin 2, corner o 1 = corner o 0 + unit i ∨ corner o 0 = corner o 1 + unit i
  exact ⟨0,Or.inl (by simp [corner])⟩
theorem adjacent12 (o : Site 2) : (lattice 2).Adj (corner o 1) (corner o 2) := by
  change ∃ i : Fin 2, corner o 2 = corner o 1 + unit i ∨ corner o 1 = corner o 2 + unit i
  exact ⟨1,Or.inl (by simp [corner,add_assoc])⟩
theorem adjacent23 (o : Site 2) : (lattice 2).Adj (corner o 2) (corner o 3) := by
  change ∃ i : Fin 2, corner o 3 = corner o 2 + unit i ∨ corner o 2 = corner o 3 + unit i
  exact ⟨0,Or.inr (by simp [corner]; abel)⟩
theorem adjacent30 (o : Site 2) : (lattice 2).Adj (corner o 3) (corner o 0) := by
  change ∃ i : Fin 2, corner o 0 = corner o 3 + unit i ∨ corner o 3 = corner o 0 + unit i
  exact ⟨1,Or.inr (by simp [corner])⟩

theorem diagonal02 (D : Set (Site 2)) (o : Site 2)
    (h1 : corner o 1 ∈ D ∨ corner o 3 ∈ D) : NearWithin D o (corner o 0) (corner o 2) := by
  rcases h1 with h1 | h3
  · exact Or.inr (Or.inr ⟨corner o 1,h1,⟨1,rfl⟩,adjacent01 o,adjacent12 o⟩)
  · exact Or.inr (Or.inr ⟨corner o 3,h3,⟨3,rfl⟩,(adjacent30 o).symm,(adjacent23 o).symm⟩)

theorem diagonal13 (D : Set (Site 2)) (o : Site 2)
    (h0 : corner o 0 ∈ D ∨ corner o 2 ∈ D) : NearWithin D o (corner o 1) (corner o 3) := by
  rcases h0 with h0 | h2
  · exact Or.inr (Or.inr ⟨corner o 0,h0,⟨0,rfl⟩,(adjacent01 o).symm,(adjacent30 o).symm⟩)
  · exact Or.inr (Or.inr ⟨corner o 2,h2,⟨2,rfl⟩,adjacent12 o,adjacent23 o⟩)

theorem NearWithin.symm {D : Set (Site 2)} {o x y : Site 2} (h : NearWithin D o x y) :
    NearWithin D o y x := by
  rcases h with h | h | ⟨w,hw,hc,hx,hy⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr ⟨w,hw,hc,hy.symm,hx.symm⟩)

/-- Exhaustive actual corner geometry: the sole failure of a two-step route is alternating color. -/
theorem near_or_alternating (D : Set (Site 2)) (o : Site 2) (i j : Fin 4)
    (hi : corner o i ∈ D) (hj : corner o j ∈ D) :
    NearWithin D o (corner o i) (corner o j) ∨ Alternating D o := by
  fin_cases i <;> fin_cases j
  all_goals try first
    | solve | exact Or.inl (Or.inl rfl)
    | solve | exact Or.inl (Or.inr (Or.inl (adjacent01 o)))
    | solve | exact Or.inl (Or.inr (Or.inl (adjacent12 o)))
    | solve | exact Or.inl (Or.inr (Or.inl (adjacent23 o)))
    | solve | exact Or.inl (Or.inr (Or.inl (adjacent30 o)))
    | solve | exact Or.inl (Or.inr (Or.inl (adjacent01 o).symm))
    | solve | exact Or.inl (Or.inr (Or.inl (adjacent12 o).symm))
    | solve | exact Or.inl (Or.inr (Or.inl (adjacent23 o).symm))
    | solve | exact Or.inl (Or.inr (Or.inl (adjacent30 o).symm))
  · by_cases h1 : corner o 1 ∈ D
    · exact Or.inl (diagonal02 D o (Or.inl h1))
    by_cases h3 : corner o 3 ∈ D
    · exact Or.inl (diagonal02 D o (Or.inr h3))
    exact Or.inr (Or.inl ⟨hi,hj,h1,h3⟩)
  · by_cases h0 : corner o 0 ∈ D
    · exact Or.inl (diagonal13 D o (Or.inl h0))
    by_cases h2 : corner o 2 ∈ D
    · exact Or.inl (diagonal13 D o (Or.inr h2))
    exact Or.inr (Or.inr ⟨hi,hj,h0,h2⟩)
  · by_cases h1 : corner o 1 ∈ D
    · exact Or.inl (diagonal02 D o (Or.inl h1)).symm
    by_cases h3 : corner o 3 ∈ D
    · exact Or.inl (diagonal02 D o (Or.inr h3)).symm
    exact Or.inr (Or.inl ⟨hj,hi,h1,h3⟩)
  · by_cases h0 : corner o 0 ∈ D
    · exact Or.inl (diagonal13 D o (Or.inl h0)).symm
    by_cases h2 : corner o 2 ∈ D
    · exact Or.inl (diagonal13 D o (Or.inr h2)).symm
    exact Or.inr (Or.inr ⟨hj,hi,h0,h2⟩)

/-- Genuine literal induced connectedness supplies a finite walk on exactly D. -/
theorem induced_reaches (D : Set (Site 2))
    (hD : ((lattice 2).induce D).Connected) (x y : Site 2) (hx : x ∈ D) (hy : y ∈ D) :
    Relation.ReflTransGen (fun u v => u ∈ D ∧ v ∈ D ∧ (lattice 2).Adj u v) x y := by
  have h := (SimpleGraph.reachable_iff_reflTransGen (⟨x,hx⟩ : D) (⟨y,hy⟩ : D)).mp
    (hD ⟨x,hx⟩ ⟨y,hy⟩)
  have lift {u v : D} (hr : Relation.ReflTransGen ((lattice 2).induce D).Adj u v) :
      Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ (lattice 2).Adj a b) u.val v.val := by
    induction hr with
    | refl => exact .refl
    | @tail u v _ huv ih => exact ih.tail ⟨u.property,v.property,huv⟩
  exact lift h

end FiniteAvalanches.Electrical.LatticeCell
