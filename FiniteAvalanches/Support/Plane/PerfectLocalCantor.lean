import FiniteAvalanches.Support.Plane.LoopResidual

/-!
# Cantor injections inside perfect sets

Every open neighborhood meeting a perfect set in a complete metric space
contains a continuous injection of Cantor space into that set.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric

/-- Every open set meeting a perfect set in a complete metric space contains
a continuous injective image of Cantor space inside that perfect set. -/
theorem Perfect.exists_nat_bool_injection_in_open
    {X : Type*} [MetricSpace X] [CompleteSpace X] {K U : Set X}
    (hK : Perfect K) (hU : IsOpen U) (hne : (U ∩ K).Nonempty) :
    ∃ f : (ℕ → Bool) → X, range f ⊆ U ∩ K ∧ Continuous f ∧ Function.Injective f := by
  obtain ⟨x, hxU, hxK⟩ := hne
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hxU
  have hr2 : 0 < r / 2 := by linarith
  obtain ⟨hD, hDne⟩ := hK.closure_nhds_inter x hxK (mem_ball_self hr2) isOpen_ball
  obtain ⟨f, hfD, hfc, hfi⟩ := hD.exists_nat_bool_injection hDne
  have hDK : closure (ball x (r / 2) ∩ K) ⊆ K :=
    closure_minimal inter_subset_right hK.closed
  have hDU : closure (ball x (r / 2) ∩ K) ⊆ U := by
    have hDball : closure (ball x (r / 2) ∩ K) ⊆ closedBall x (r / 2) :=
      closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
    exact hDball.trans ((closedBall_subset_ball (by linarith)).trans hrU)
  exact ⟨f, fun z hz => ⟨hDU (hfD hz), hDK (hfD hz)⟩, hfc, hfi⟩

end FiniteAvalanches.Electrical.StatementGeometry
