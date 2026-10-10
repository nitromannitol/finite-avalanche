import FiniteAvalanches.Electrical.LoopDeletion
import FiniteAvalanches.Electrical.ChordSplit.IdentifiedResponse

/-! Total response transport to the convention-normalized identified split. -/
namespace FiniteAvalanches.Electrical.ChordSplit
open StatementGeometry Source
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- The literal identified graph, with precisely the nonloop original IDs. -/
def loopDeletedSplitGraph (J : CopiedGraph V E) (alpha beta : V) (side : E → Bool) :=
  deleteLoops (groundedSplitGraph J alpha beta side)

/-- The unique Dirichlet voltage, using the established extension and internally
proved boundary reachability. -/
def loopDeletedVoltage (J : CopiedGraph V E) (alpha beta : V) (side : E → Bool)
    (hc : (supportGraph J.left J.right).Preconnected) :
    GroundedSplitVertex alpha beta → ℝ :=
  harmonicExtension (loopDeletedSplitGraph J alpha beta side).left
    (loopDeletedSplitGraph J alpha beta side).right {.inr false,.inr true}
    (deleteLoops_boundary_reachable _ _ (identified_boundary_reachable J alpha beta side hc))
    (fun x => if x = .inr true then 1 else 0)

theorem loopDeletedVoltage_eq_identifiedVoltage (J : CopiedGraph V E)
    (alpha beta : V) (side : E → Bool) (hc : (supportGraph J.left J.right).Preconnected) :
    loopDeletedVoltage J alpha beta side hc = identifiedVoltage J alpha beta side hc := by
  have h := deleteLoops_harmonicExtension (groundedSplitGraph J alpha beta side)
    ({.inr false,.inr true} : Finset (GroundedSplitVertex alpha beta))
    (identified_boundary_reachable J alpha beta side hc)
    (fun x => if x = .inr true then (1 : ℝ) else 0)
  exact h

theorem loopDeletedVoltage_spec (J : CopiedGraph V E) (alpha beta : V) (side : E → Bool)
    (hc : (supportGraph J.left J.right).Preconnected) :
    loopDeletedVoltage J alpha beta side hc (.inr false) = 0 ∧
    loopDeletedVoltage J alpha beta side hc (.inr true) = 1 ∧
    ∀ x, x ≠ .inr false → x ≠ .inr true →
      laplacian (loopDeletedSplitGraph J alpha beta side).left
        (loopDeletedSplitGraph J alpha beta side).right (loopDeletedVoltage J alpha beta side hc) x = 0 := by
  have hs := harmonicExtension_spec (loopDeletedSplitGraph J alpha beta side).left
    (loopDeletedSplitGraph J alpha beta side).right {.inr false,.inr true}
    (deleteLoops_boundary_reachable _ _ (identified_boundary_reachable J alpha beta side hc))
    (fun x => if x = .inr true then (1 : ℝ) else 0)
  refine ⟨?_,?_,?_⟩
  · exact (hs.1 _ (by simp)).trans (if_neg (by intro h; cases h))
  · exact (hs.1 _ (by simp)).trans (if_pos rfl)
  · intro x h0 h1
    exact hs.2 x (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; exact ⟨h0,h1⟩)

theorem loopDeletedVoltage_unique (J : CopiedGraph V E) (alpha beta : V) (side : E → Bool)
    (hc : (supportGraph J.left J.right).Preconnected) (f : GroundedSplitVertex alpha beta → ℝ)
    (h0 : f (.inr false) = 0) (h1 : f (.inr true) = 1)
    (hh : ∀ x, x ≠ .inr false → x ≠ .inr true →
      laplacian (loopDeletedSplitGraph J alpha beta side).left
        (loopDeletedSplitGraph J alpha beta side).right f x = 0) :
    f = loopDeletedVoltage J alpha beta side hc := by
  apply harmonicExtension_eq
  constructor
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rw [h0,if_neg (by intro h; cases h)]
    · rw [Finset.mem_singleton.mp hx,h1,if_pos rfl]
  · intro x hx
    have hp : x ≠ .inr false ∧ x ≠ .inr true := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hx
    exact hh x hp.1 hp.2

theorem loopDeleted_energy_eq_total_response (J : CopiedGraph V E)
    (alpha beta : V) (hbeta : beta ≠ alpha) (side : E → Bool)
    (hc : (supportGraph J.left J.right).Preconnected) :
    energy (loopDeletedSplitGraph J alpha beta side).left
      (loopDeletedSplitGraph J alpha beta side).right (loopDeletedVoltage J alpha beta side hc) =
    responseEntry (splitGraph J alpha side).left (splitGraph J alpha side).right
      (splitTerminals alpha beta hbeta)
      (split_terminal_reachable J.left J.right alpha beta hbeta side hc) 1 1 := by
  calc
    _ = energy (loopDeletedSplitGraph J alpha beta side).left
        (loopDeletedSplitGraph J alpha beta side).right (identifiedVoltage J alpha beta side hc) :=
      congrArg (energy (loopDeletedSplitGraph J alpha beta side).left
        (loopDeletedSplitGraph J alpha beta side).right)
        (loopDeletedVoltage_eq_identifiedVoltage J alpha beta side hc)
    _ = energy (groundedSplitGraph J alpha beta side).left
        (groundedSplitGraph J alpha beta side).right (identifiedVoltage J alpha beta side hc) :=
      deleteLoops_energy (groundedSplitGraph J alpha beta side) (identifiedVoltage J alpha beta side hc)
    _ = _ := identified_energy_eq_total_response J alpha beta hbeta side hc

/-- Connectedness is the only additional input to this generic helper; actual
source applications prove it before invoking this equality. -/
theorem loopDeleted_effectiveConductance_eq_total_response (J : CopiedGraph V E)
    (alpha beta : V) (hbeta : beta ≠ alpha) (side : E → Bool)
    (hc : (supportGraph J.left J.right).Preconnected)
    (hK : (supportGraph (groundedSplitGraph J alpha beta side).left
      (groundedSplitGraph J alpha beta side).right).Preconnected) :
    effectiveConductance (loopDeletedSplitGraph J alpha beta side) (.inr false) (.inr true) (by intro h; cases h)
      (deleteLoops_preconnected _ hK) =
    responseEntry (splitGraph J alpha side).left (splitGraph J alpha side).right
      (splitTerminals alpha beta hbeta)
      (split_terminal_reachable J.left J.right alpha beta hbeta side hc) 1 1 := by
  have hv : Source.voltage (loopDeletedSplitGraph J alpha beta side) (.inr false) (.inr true)
      (deleteLoops_preconnected _ hK) = loopDeletedVoltage J alpha beta side hc := by
    obtain ⟨h0,h1,hh⟩ := Source.voltage_spec (loopDeletedSplitGraph J alpha beta side)
      (.inr false) (.inr true) (by intro h; cases h) (deleteLoops_preconnected _ hK)
    exact loopDeletedVoltage_unique J alpha beta side hc _ h0 h1 hh
  exact (congrArg (energy (loopDeletedSplitGraph J alpha beta side).left
    (loopDeletedSplitGraph J alpha beta side).right) hv).trans
    (loopDeleted_energy_eq_total_response J alpha beta hbeta side hc)

end
end FiniteAvalanches.Electrical.ChordSplit
