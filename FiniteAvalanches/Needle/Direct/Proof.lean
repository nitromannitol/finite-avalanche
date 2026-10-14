import FiniteAvalanches.Needle.Direct.GreedyPath
import FiniteAvalanches.Needle.Direct.Energy

/-! Dirichlet composition for the literal greedy path and clipped quotient. -/

namespace FiniteAvalanches.Needle
open LatticeProb Sandpile.FiniteWired
open scoped Classical

/-- The first-entry greedy path on the actual outer-box carrier. -/
noncomputable def needleGreedyInBox (h : ℕ) (w : Point) (hw : radius w = 2 * h) :
    InBoxVertices h (needleGreedyEntrance h w) :=
  ⟨needleGreedyPath h w, needle_greedy_path_in_box h w hw⟩

theorem needle_greedy_test_one_on_target (h : ℕ) (w x : Point) (hw : radius w = 2 * h)
    (hx : x ∈ target h (needleGreedyEntrance h w) (needleGreedyPath h w)) :
    needleTestFunction h w x = 1 := by
  rcases Finset.mem_union.mp hx with hb | hp
  · exact needle_test_function_eq_one_on_box h w x hw ((mem_boxPoints h x).mp hb)
  · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hp
    exact needle_test_function_eq_one_of_distance_le h w _
      (needle_greedy_path_distance_bound h w hw t)

/-- Conductance of the literal box/path union, with each original copied exit retained. -/
theorem needle_greedy_conductance (h : ℕ) (hh : 10 ≤ h) (w : Point) (hw : radius w = 2 * h) :
    wiredConductance (2 * h)
      (zeroVertices h (needleGreedyEntrance h w) (needleGreedyInBox h w hw)) ≤
        2304 * Real.log (h : ℝ) := by
  have htrial := wiredConductance_le_trial (2 * h)
    (zeroVertices h (needleGreedyEntrance h w) (needleGreedyInBox h w hw))
    (fun v => 1 - needleWiredTest h w v) (by simp [needleWiredTest])
    (fun x hx => by
      change 1 - needleTestFunction h w (site x) = 0
      rw [needle_greedy_test_one_on_target h w (site x) hw (Finset.mem_filter.mp hx).2]
      exact sub_self 1)
  calc
    _ ≤ Electrical.energy (fun e : Edge (2 * h) => (endpoints e).1)
        (fun e => (endpoints e).2) (fun v => 1 - needleWiredTest h w v) := htrial
    _ = Electrical.energy (fun e : Edge (2 * h) => (endpoints e).1)
        (fun e => (endpoints e).2) (needleWiredTest h w) := Electrical.energy_one_sub _ _ _
    _ ≤ 2304 * Real.log (h : ℝ) := needle_direct_energy_le_log_h h hh w hw

/-- An actual simple nearest-neighbor path from the boundary to the inner box,
with the conductance estimate produced by the incoming proof. -/
theorem needle_greedy_path_budget (h : ℕ) (hh : 10 ≤ h) (w : Point) (hw : radius w = 2 * h) :
    ∃ (L : ℕ) (p : InBoxVertices h L),
      Function.Injective p.val ∧ p.val ⟨0, by omega⟩ = w ∧
      p.val ⟨L, by omega⟩ ∈ box 2 h ∧
      (∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩)
        (p.val ⟨t.val + 1, by omega⟩)) ∧
      wiredConductance (2 * h) (zeroVertices h L p) ≤ 2304 * Real.log (h : ℝ) := by
  refine ⟨needleGreedyEntrance h w, needleGreedyInBox h w hw,
    needle_greedy_path_injective h w, needle_greedy_path_start h w,
    needle_greedy_path_end h w, needle_greedy_path_adj h w, ?_⟩
  exact needle_greedy_conductance h hh w hw

/-- The current source's uniform path-facing needle statement. -/
theorem source_needle_path : ∃ C : ℝ, ∀ h : ℕ, 10 ≤ h → ∀ w : Point,
    radius w = 2 * h → ∃ (L : ℕ) (p : InBoxVertices h L),
      Function.Injective p.val ∧ p.val ⟨0, by omega⟩ = w ∧
      p.val ⟨L, by omega⟩ ∈ box 2 h ∧
      (∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩)
        (p.val ⟨t.val + 1, by omega⟩)) ∧
      wiredConductance (2 * h) (zeroVertices h L p) ≤ C * Real.log (h : ℝ) := by
  exact ⟨2304, needle_greedy_path_budget⟩

end FiniteAvalanches.Needle
