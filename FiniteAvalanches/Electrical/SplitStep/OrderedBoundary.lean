import FiniteAvalanches.Electrical.SplitTerminal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open scoped Classical BigOperators
noncomputable section

variable {V E : Type*}

/-- Inward current of one original copy at the vertex being split. Both loop incidences remain. -/
def copyInflow (a b : E → V) (alpha : V) (phi : V → ℝ) (e : E) : ℝ :=
  (if a e = alpha then phi (b e) - phi alpha else 0) +
    (if b e = alpha then phi (a e) - phi alpha else 0)

/-- The first i original boundary copies go to false and the remaining copies go to true. -/
def boundarySide (a b : E → V) (alpha : V) {m : ℕ}
    (copies : Fin m ≃ {e : E // a e = alpha ∨ b e = alpha}) (i : ℕ) (e : E) : Bool :=
  if h : a e = alpha ∨ b e = alpha then decide (i ≤ (copies.symm ⟨e, h⟩).val) else false

theorem boundarySide_copy (a b : E → V) (alpha : V) {m : ℕ}
    (copies : Fin m ≃ {e : E // a e = alpha ∨ b e = alpha}) (i : ℕ) (k : Fin m) :
    boundarySide a b alpha copies i (copies k).val = decide (i ≤ k.val) := by
  rw [boundarySide, dif_pos (copies k).property]
  change decide (i ≤ (copies.symm (copies k)).val) = decide (i ≤ k.val)
  rw [Equiv.symm_apply_apply]

theorem boundarySide_prefix (a b : E → V) (alpha : V) {m : ℕ}
    (copies : Fin m ≃ {e : E // a e = alpha ∨ b e = alpha}) (i : ℕ)
    (k : Fin m) (hk : k.val < i) :
    boundarySide a b alpha copies i (copies k).val = false := by
  rw [boundarySide_copy, decide_eq_false (not_le_of_gt hk)]

theorem boundarySide_suffix (a b : E → V) (alpha : V) {m : ℕ}
    (copies : Fin m ≃ {e : E // a e = alpha ∨ b e = alpha}) (i : ℕ)
    (k : Fin m) (hk : i ≤ k.val) :
    boundarySide a b alpha copies i (copies k).val = true := by
  rw [boundarySide_copy, decide_eq_true hk]

theorem splitEndpoint_eq_true (alpha : V) (side : E → Bool) (v : V) (e : E) :
    splitEndpoint alpha side v e = Sum.inr true ↔ v = alpha ∧ side e = true := by
  unfold splitEndpoint
  split_ifs with hv
  · simp only [Sum.inr.injEq, hv, true_and]
  · constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; exact (hv h).elim

variable [Fintype E]

/-- Splitting retains the original-copy sum, with exactly the selected alpha incidences. -/
theorem split_inflow_eq_selected_sum (a b : E → V) (alpha : V) (side : E → Bool)
    (phi : V → ℝ) :
    -laplacian (fun e => splitEndpoint alpha side (a e) e)
      (fun e => splitEndpoint alpha side (b e) e) (fun x => phi (collapse alpha x))
      (.inr true) = ∑ e, if side e = true then copyInflow a b alpha phi e else 0 := by
  rw [laplacian, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [splitEndpoint_eq_true, collapse_splitEndpoint, copyInflow]
  change -((if a e = alpha ∧ side e = true then phi alpha - phi (b e) else 0) +
    (if b e = alpha ∧ side e = true then phi alpha - phi (a e) else 0)) = _
  by_cases ha : a e = alpha <;> by_cases hb : b e = alpha <;>
    cases side e <;> simp [ha, hb]

/-- The inward current at alpha1 is precisely the suffix of the original ordered copy currents. -/
theorem split_inflow_eq_boundary_suffix (a b : E → V) (alpha : V) {m : ℕ}
    (copies : Fin m ≃ {e : E // a e = alpha ∨ b e = alpha}) (i : ℕ)
    (phi : V → ℝ) :
    -laplacian (fun e => splitEndpoint alpha (boundarySide a b alpha copies i) (a e) e)
      (fun e => splitEndpoint alpha (boundarySide a b alpha copies i) (b e) e)
      (fun x => phi (collapse alpha x)) (.inr true) =
        ∑ k : Fin m, if i ≤ k.val then copyInflow a b alpha phi (copies k).val else 0 := by
  rw [split_inflow_eq_selected_sum]
  let p := fun e => a e = alpha ∨ b e = alpha
  let g := fun e => if boundarySide a b alpha copies i e = true
    then copyInflow a b alpha phi e else 0
  have hz (e : E) (he : ¬p e) : g e = 0 := by
    change (if boundarySide a b alpha copies i e = true then copyInflow a b alpha phi e else 0) = 0
    have hn : ¬(a e = alpha ∨ b e = alpha) := he
    rw [boundarySide, dif_neg hn, if_neg (by decide)]
  have hsum : (∑ e, g e) = ∑ e : {e : E // p e}, g e.val := by
    calc
      _ = ∑ e, if p e then g e else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : p e
        · rw [if_pos he]
        · rw [if_neg he, hz e he]
      _ = ∑ e ∈ Finset.univ.filter p, g e := (Finset.sum_filter p g).symm
      _ = _ := Finset.sum_subtype (p := p) (Finset.univ.filter p) (by simp) g
  change (∑ e, g e) = _
  rw [hsum, ← copies.sum_comp (fun e => g e.val)]
  apply Finset.sum_congr rfl
  intro k _
  simp only [g, boundarySide_copy, decide_eq_true_eq]

end
end FiniteAvalanches.Electrical.SplitStep
