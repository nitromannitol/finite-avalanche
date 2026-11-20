import FiniteAvalanches.Support.Plane.CrossingAccess

/-!
# Transverse accesses avoiding closed sets

Finite families of charted boundary arcs admit disjoint transverse accesses
that avoid a prescribed closed set away from the marked points.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- Transverse accesses to finitely many charted arcs can avoid a closed set
that does not contain the marked points. -/
theorem exists_disjoint_transverse_paths_avoiding_closed
    {ι : Type*} [DecidableEq ι] {U S K : Set (ℝ × ℝ)} (hU : IsOpen U)
    (s : Finset ι) {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hS : S.Finite) (hobsS : ∀ i ∈ s, Disjoint (range (p i)) S)
    (t : ι → unitInterval) (ht : ∀ i ∈ s, t i ≠ 1)
    (chart : ι → (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (c : ι → ℝ)
    (hvertical : ∀ i ∈ s, ∀ z ∈ range (p i), (chart i z).1 = c i)
    (hK : IsClosed K) (hmark : ∀ i ∈ s, p i (t i) ∉ K) :
    ∃ b : ι → ℝ × ℝ, ∃ w : ∀ i, Path (p i (t i)) (b i),
      (∀ i ∈ s, b i ≠ p i (t i) ∧ Function.Injective (w i) ∧
        range (w i) ⊆ (U \ (S ∪ ⋃ j ∈ s.erase i, range (p j))) \ K ∧
        range (w i) ∩ range (p i) = {p i (t i)}) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (w i)) (range (w j))) := by
  classical
  obtain ⟨ε, hε, hdisj⟩ :=
    exists_disjoint_balls_around_boundary_path_points hU s p hd hinside hS hobsS t ht
  have hex : ∀ i, ∃ b : ℝ × ℝ, ∃ w : Path (p i (t i)) b,
      i ∈ s → b ≠ p i (t i) ∧ Function.Injective w ∧
        range w ⊆ Metric.ball (p i (t i)) (ε i) \ K ∧
        range w ∩ range (p i) = {p i (t i)} := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨b, w, hb, hw, hwsub, hwmeet⟩ :=
        exists_transverse_path_to_vertical_arc
          (U := Metric.ball (p i (t i)) (ε i) \ K) (A := range (p i))
          (a := p i (t i)) (Metric.isOpen_ball.sdiff hK) (chart i)
          ⟨⟨Metric.mem_ball_self (hε i hi).1, hmark i hi⟩, ⟨t i, rfl⟩⟩
          (c i) (hvertical i hi)
      exact ⟨b, w, fun _ => ⟨hb, hw, hwsub, hwmeet⟩⟩
    · exact ⟨p i (t i), Path.refl _, fun h => (hi h).elim⟩
  choose b w hw using hex
  refine ⟨b, w, ?_, ?_⟩
  · intro i hi
    obtain ⟨hb, hinj, hsub, hmeet⟩ := hw i hi
    refine ⟨hb, hinj, ?_, hmeet⟩
    intro z hz
    exact ⟨(hε i hi).2 (hsub hz).1, (hsub hz).2⟩
  · intro i hi j hj hij
    exact (hdisj i hi j hj hij).mono
      (fun z hz => ((hw i hi).2.2.1 hz).1)
      (fun z hz => ((hw j hj).2.2.1 hz).1)

end FiniteAvalanches.Electrical.StatementGeometry
