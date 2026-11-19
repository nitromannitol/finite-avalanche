import FiniteAvalanches.Support.Plane.DualDrawingFromPaths

/-!
# Geometric dual from indexed arms

A single indexed family of separated arms supplies both sides of every crossing.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Set Source BSST

/-- The face incident to a chosen side of an edge chart. -/
noncomputable def dualSideFace {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e) (i : E × Bool) : Face D :=
  if i.2 then positiveChartFace D i.1 (charts i.1)
  else negativeChartFace D i.1 (charts i.1)

/-- Separated arms indexed by edge and side determine the geometric dual. -/
theorem exists_geometric_dual_of_separated_arms {V E : Type}
    [Fintype V] [Fintype E] [Nonempty E] {J : CopiedGraph V E}
    (D : Drawing J) [Fintype (Face D)] (charts : ∀ e, EdgeChart D e)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (point : Face D → ℝ × ℝ) (hpoint : Function.Injective point)
    (hpointface : ∀ F, point F ∈ faceRegion D F)
    (crossing : E → ℝ × ℝ)
    (arm : ∀ i : E × Bool, Path (point (dualSideFace D charts i)) (crossing i.1))
    (harm : ∀ i, Function.Injective (arm i))
    (hpair : ∀ i j, i ≠ j → range (arm i) ∩ range (arm j) ⊆
      {z | z = point (dualSideFace D charts i) ∧
        dualSideFace D charts i = dualSideFace D charts j} ∪
      {z | z = crossing i.1 ∧ i.1 = j.1})
    (havoid : ∀ i t, t ≠ 0 → arm i t ∉ range point)
    (hface : ∀ i t, t ≠ 1 → arm i t ∈ faceRegion D (dualSideFace D charts i))
    (hcross : ∀ e f s, D.curve f s = crossing e ↔ f = e ∧ s.val = 1 / 2)
    (r : E → ℝ) (hr : ∀ e, 0 < r e)
    (hneg : ∀ e s, 1 - 2 * r e < s.val →
      (charts e).chart.map (arm (e, false) s) = (1 / 2, (s.val - 1) / 2))
    (hpos : ∀ e s, 1 - 2 * r e < s.val →
      (charts e).chart.map (arm (e, true) s) = (1 / 2, (1 - s.val) / 2)) :
    let J' : CopiedGraph (Face D) E :=
      ⟨fun e => negativeChartFace D e (charts e), fun e => positiveChartFace D e (charts e)⟩
    ∃ D' : Drawing J', ∃ dualCharts : ∀ e, EdgeChart D' e,
      ∃ vertexFace : V ≃ Face D',
      (∀ F, D'.point F ∈ faceRegion D F) ∧
      (∀ v, D.point v ∈ faceRegion D' (vertexFace v)) ∧
      (∀ e f s t, D.curve e s = D'.curve f t ↔
        e = f ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
      (∀ e t, (t.val < 1 / 2 → D'.curve e t ∈ faceRegion D (J'.left e)) ∧
        (1 / 2 < t.val → D'.curve e t ∈ faceRegion D (J'.right e))) ∧
      (∀ e, ∃ radius : ℝ, 0 < radius ∧ radius < (charts e).radius ∧
        ∀ t, |t.val - 1 / 2| < radius →
          (charts e).chart.map (D'.curve e t) = (1 / 2, t.val - 1 / 2)) ∧
      (∀ e, positiveChartFace D' e (dualCharts e) = vertexFace (J.left e) ∧
        negativeChartFace D' e (dualCharts e) = vertexFace (J.right e)) := by
  let p := fun e => arm (e, false)
  let q := fun e => arm (e, true)
  apply exists_geometric_dual_of_crossing_paths D charts hconn point hpoint hpointface
    crossing p q (fun e => harm (e, false)) (fun e => harm (e, true)) (r := r)
  · intro e heq
    apply subset_antisymm
    · intro z hz
      rcases hpair (e, false) (e, true) (by simp) hz with h | h
      · simp only [mem_insert_iff, mem_singleton_iff]
        exact Or.inl (by simpa [dualSideFace] using h.1)
      · simp only [mem_insert_iff, mem_singleton_iff]
        exact Or.inr h.1
    · intro z hz
      simp only [mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · refine ⟨(p e).source_mem_range, ?_⟩
        have hq := (q e).source_mem_range
        change point (positiveChartFace D e (charts e)) ∈ range (q e) at hq
        rw [← heq] at hq
        exact hq
      · exact ⟨(p e).target_mem_range, (q e).target_mem_range⟩
  · intro e heq
    apply subset_antisymm
    · intro z hz
      rcases hpair (e, false) (e, true) (by simp) hz with h | h
      · exact (heq (congrArg point (by simpa [dualSideFace] using h.2))).elim
      · simpa using h.1
    · intro z hz
      simp only [mem_singleton_iff] at hz
      subst z
      exact ⟨(p e).target_mem_range, (q e).target_mem_range⟩
  · exact fun e => havoid (e, false)
  · exact fun e => havoid (e, true)
  · intro e f hef z hz
    rw [Path.trans_range, Path.trans_range, Path.symm_range, Path.symm_range] at hz
    rcases hz.1 with hp | hq <;> rcases hz.2 with hp' | hq'
    all_goals
      first
      | have h := hpair (e, false) (f, false) (by simpa using hef) ⟨hp, hp'⟩
        rcases h with h | h
        · exact ⟨_, h.1.symm⟩
        · exact (hef h.2).elim
      | have h := hpair (e, false) (f, true) (by simp) ⟨hp, hq'⟩
        rcases h with h | h
        · exact ⟨_, h.1.symm⟩
        · exact (hef h.2).elim
      | have h := hpair (e, true) (f, false) (by simp) ⟨hq, hp'⟩
        rcases h with h | h
        · exact ⟨_, h.1.symm⟩
        · exact (hef h.2).elim
      | have h := hpair (e, true) (f, true) (by simpa using hef) ⟨hq, hq'⟩
        rcases h with h | h
        · exact ⟨_, h.1.symm⟩
        · exact (hef h.2).elim
  · exact fun e => hface (e, false)
  · exact fun e => hface (e, true)
  · exact hcross
  · exact hr
  · exact hneg
  · exact hpos

end FiniteAvalanches.Electrical.StatementGeometry
