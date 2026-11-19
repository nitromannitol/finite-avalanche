import FiniteAvalanches.Wilson.Lattice.StackLaw
import FiniteAvalanches.Wilson.Lattice.WiredForestLaw
import FiniteAvalanches.Wilson.CyclePopping.RootDescent

/-! Direction stacks on wired square boxes terminate at the prescribed roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory ProbabilityTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

/-- Follow a lattice direction, sending an exit to the wired vertex. -/
def wiredHead (N : ℕ) : FiniteWired.Vertex N → FiniteWired.Direction → FiniteWired.Vertex N
  | none, _ => none
  | some x, d => wiredSite N (FiniteWired.site x + FiniteWired.step d)

/-- Distance to the left boundary, with zero assigned to the wired vertex. -/
def wiredLeftRank (N : ℕ) : FiniteWired.Vertex N → ℕ
  | none => 0
  | some x => Int.toNat (FiniteWired.site x 0 + (N : ℤ) + 1)

/-- The negative first-coordinate direction always decreases the rank. -/
theorem wiredHead_left_decreases (N : ℕ) (x : FiniteWired.Active N) :
    wiredLeftRank N (wiredHead N (some x) (0, false)) < wiredLeftRank N (some x) := by
  have hx := (x 0).property.1
  have hp : 0 ≤ FiniteWired.site x 0 + (N : ℤ) + 1 := by
    change -(N : ℤ) ≤ FiniteWired.site x 0 at hx
    omega
  have hp' : (0 : ℤ) < FiniteWired.site x 0 + (N : ℤ) + 1 := by
    change -(N : ℤ) ≤ FiniteWired.site x 0 at hx
    omega
  let y := FiniteWired.site x + FiniteWired.step (0, false)
  have hy : y 0 = FiniteWired.site x 0 - 1 := by
    simp [y, FiniteWired.step, unit, sub_eq_add_neg]
  change wiredLeftRank N (wiredSite N y) < wiredLeftRank N (some x)
  by_cases hb : FiniteWired.inBox N y
  · rw [wiredSite, dif_pos hb]
    have hypos : 0 ≤ y 0 + (N : ℤ) + 1 := by omega
    have hq := Int.toNat_of_nonneg hypos
    have hpq := Int.toNat_of_nonneg hp
    change Int.toNat (y 0 + (N : ℤ) + 1) <
      Int.toNat (FiniteWired.site x 0 + (N : ℤ) + 1)
    omega
  · rw [wiredSite, dif_neg hb]
    have hpq := Int.toNat_of_nonneg hp
    change 0 < Int.toNat (FiniteWired.site x 0 + (N : ℤ) + 1)
    omega

/-- In a wired box every nonroot has a direction decreasing the left-boundary rank. -/
theorem wiredHead_root_descent (R : RootPair) (N : ℕ) (v : FiniteWired.Vertex N)
    (hv : v ∉ (wiredRoots R N).val) :
    ∃ d, wiredLeftRank N (wiredHead N v d) < wiredLeftRank N v := by
  cases v with
  | none => exact (hv (Or.inr trivial)).elim
  | some x => exact ⟨(0, false), wiredHead_left_decreases N x⟩


/-- The wired graph admits a cycle-free selection of its lattice directions. -/
theorem wiredGoodArrows_nonempty (R : RootPair) (N : ℕ) :
    Nonempty (GoodArrows (wiredRoots R N).val (wiredHead N)) :=
  exists_goodArrows_of_descent _ _ (wiredLeftRank N) (wiredHead_root_descent R N)

/-- Independent uniform direction stacks in a wired box reach a terminal
configuration almost surely. -/
theorem wiredStack_ae_terminates (R : RootPair) (N : ℕ)
    (k : Cursor (FiniteWired.Vertex N)) :
    ∀ᵐ σ ∂directionStackLaw (FiniteWired.Vertex N),
      ∃ l, Relation.ReflTransGen
          (pop_step (wiredRoots R N).val (wiredHead N) (fun v i => σ (v, i))) k l ∧
        terminal (wiredRoots R N).val (wiredHead N) (fun v i => σ (v, i)) l := by
  apply ae_terminalEvent_of_descent (directionStackLaw (FiniteWired.Vertex N))
    (wiredRoots R N).val (wiredHead N) k (fun v i σ => σ (v, i))
    (rank := wiredLeftRank N)
  · exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  · intro v i
    exact measurable_pi_apply (v, i)
  · intro v i d
    rw [directionStackLaw_eval _ v i d, directionStackLaw_eval _ v 0 d]
  · exact wiredHead_root_descent R N
  · intro v d
    rw [directionStackLaw_eval _ v 0 d]
    norm_num


/-- Each cycle-free terminal direction assignment in a wired box is equally likely. -/
theorem wiredStack_terminal_uniform (R : RootPair) (N : ℕ)
    (k : Cursor (FiniteWired.Vertex N)) (a : GoodArrows (wiredRoots R N).val (wiredHead N)) :
    directionStackLaw (FiniteWired.Vertex N)
        (terminalOutputEvent (wiredRoots R N).val (wiredHead N) k (fun v i σ => σ (v, i)) a) =
      1 / (Fintype.card (GoodArrows (wiredRoots R N).val (wiredHead N)) : ℝ≥0∞) :=
  directionStackLaw_terminal_uniform _ _ _ _ a

end
end FiniteAvalanches.Wilson.Lattice
