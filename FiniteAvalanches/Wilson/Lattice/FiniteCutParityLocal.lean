import FiniteAvalanches.Wilson.Lattice.FiniteDualCutParity
import Mathlib.Data.ZMod.Basic

/-! Local even-degree criterion for parity of intersections of finite cuts. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Trees
open scoped Classical BigOperators

noncomputable section

variable {V W E : Type*} [Fintype V] [Fintype W] [Fintype E] [DecidableEq E]

/-- Copies of a dual cut incident to a given primal vertex. -/
def dualCutIncidentCopies (G : Multigraph V E) (H : Multigraph W E)
    (D : Set W) (v : V) : Finset E :=
  Finset.univ.filter (fun e => H.crosses D e ∧ (G.left e = v ∨ G.right e = v))

/-- If every vertex has even incidence with a dual cut, then every primal cut
meets that dual cut in an even number of original copies. -/
theorem even_commonCutCopies_of_even_incidence (G : Multigraph V E) (H : Multigraph W E)
    (D : Set W) (hlocal : ∀ v, Even (dualCutIncidentCopies G H D v).card) (C : Set V) :
    Even (commonCutCopies G H C D).card := by
  let f : V → E → ZMod 2 := fun v e =>
    if H.crosses D e then (if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0) else 0
  have hvertex (v : V) : ∑ e : E, f v e = 0 := by
    have heq : (∑ e : E, f v e) = (dualCutIncidentCopies G H D v).card := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one]
      rw [dualCutIncidentCopies, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [f]
      by_cases hh : H.crosses D e
      · by_cases hl : G.left e = v <;> by_cases hr : G.right e = v
        · exact (G.loopless e (hl.trans hr.symm)).elim
        · simp [hh, hl, hr]
        · simp [hh, hl, hr]
        · simp [hh, hl, hr]
      · simp [hh]
    rw [heq]
    exact (hlocal v).natCast_zmod_two
  let T : Finset V := Finset.univ.filter (fun v => v ∈ C)
  have hsum : (∑ v ∈ T, ∑ e : E, f v e) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact hvertex v
  rw [Finset.sum_comm] at hsum
  have hedge (e : E) : (∑ v ∈ T, f v e) =
      if G.crosses C e ∧ H.crosses D e then 1 else 0 := by
    dsimp only [f]
    by_cases hh : H.crosses D e
    · simp only [hh, if_true, Finset.sum_add_distrib]
      have hl : (∑ v ∈ T, if G.left e = v then (1 : ZMod 2) else 0) =
          if G.left e ∈ C then 1 else 0 := by
        simp [T, eq_comm]
      have hr : (∑ v ∈ T, if G.right e = v then (1 : ZMod 2) else 0) =
          if G.right e ∈ C then 1 else 0 := by
        simp [T, eq_comm]
      rw [hl, hr]
      by_cases hleft : G.left e ∈ C <;> by_cases hright : G.right e ∈ C <;>
        simp [Multigraph.crosses, hleft, hright] <;> norm_num <;> exact ZMod.natCast_self 2
    · simp [hh]
  simp_rw [hedge] at hsum
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hcard : ((commonCutCopies G H C D).card : ZMod 2) =
      ∑ e : E, if G.crosses C e ∧ H.crosses D e then (1 : ZMod 2) else 0 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one, commonCutCopies, Finset.sum_filter]
  rw [hcard]
  exact hsum

/-- If all other vertices have even incidence with a dual cut, then so does a
specified vertex; every original copy has two distinct endpoints. -/
theorem even_dualCutIncidentCopies_of_others (G : Multigraph V E) (H : Multigraph W E)
    (D : Set W) (v₀ : V) (hothers : ∀ v, v ≠ v₀ → Even (dualCutIncidentCopies G H D v).card) :
    Even (dualCutIncidentCopies G H D v₀).card := by
  let f : V → E → ZMod 2 := fun v e =>
    if H.crosses D e then (if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0) else 0
  have hvertex (v : V) : (∑ e : E, f v e) = (dualCutIncidentCopies G H D v).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    rw [dualCutIncidentCopies, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [f]
    by_cases hh : H.crosses D e
    · by_cases hl : G.left e = v <;> by_cases hr : G.right e = v
      · exact (G.loopless e (hl.trans hr.symm)).elim
      · simp [hh, hl, hr]
      · simp [hh, hl, hr]
      · simp [hh, hl, hr]
    · simp [hh]
  have htotal : (∑ v : V, (dualCutIncidentCopies G H D v).card : ZMod 2) = 0 := by
    simp_rw [← hvertex]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro e _
    dsimp only [f]
    by_cases hh : H.crosses D e
    · simp only [hh, if_true, Finset.sum_add_distrib]
      simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact ZMod.natCast_self 2
    · simp [hh]
  have hsingle : (∑ v : V, (dualCutIncidentCopies G H D v).card : ZMod 2) =
      (dualCutIncidentCopies G H D v₀).card := by
    apply Finset.sum_eq_single v₀
    · intro v _ hv
      exact (hothers v hv).natCast_zmod_two
    · intro h
      exact (h (Finset.mem_univ v₀)).elim
  rw [hsingle] at htotal
  exact ZMod.natCast_eq_zero_iff_even.mp htotal

end
end FiniteAvalanches.Wilson.Lattice
