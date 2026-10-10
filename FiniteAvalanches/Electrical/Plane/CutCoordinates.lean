import FiniteAvalanches.Electrical.Plane.VoltageCuts
import FiniteAvalanches.Electrical.Plane.UnitBoundary

/-! Actual original voltage-cut copy IDs, oriented by their physical positive currents. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- The actual original copies crossing the voltage threshold. -/
abbrev CutCopy {V E : Type*} [Fintype E] (a b : E → V) (phi : V → ℝ) (t : ℝ) :=
  {e : E // e ∈ crossingEdges a b phi t}

/-- The crossing copy is oriented from its higher-voltage endpoint to its lower one. -/
noncomputable def cutDart {V E : Type*} [Fintype E] (a b : E → V) (phi : V → ℝ) (t : ℝ)
    (e : CutCopy a b phi t) : Dart E :=
  if phi (a e.val) < t then (e.val,true) else (e.val,false)

noncomputable def cutA {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (t : ℝ) (e : CutCopy a b phi t) :
    ArcFace R da db := arcRightFace R da db (.inl (cutDart a b phi t e))

noncomputable def cutB {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (t : ℝ) (e : CutCopy a b phi t) :
    ArcFace R da db := arcLeftFace R da db (.inl (cutDart a b phi t e))

theorem cut_faces_of_lt {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (t : ℝ) (e : CutCopy a b phi t)
    (h : phi (a e.val) < t) :
    cutA R da db phi t e = dualB R da db (.inl e.val) ∧
      cutB R da db phi t e = dualA R da db (.inl e.val) := by
  simp only [cutA,cutB,cutDart,if_pos h]
  exact ⟨rfl,rfl⟩

theorem cut_faces_of_not_lt {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (t : ℝ) (e : CutCopy a b phi t)
    (h : ¬ phi (a e.val) < t) :
    cutA R da db phi t e = dualA R da db (.inl e.val) ∧
      cutB R da db phi t e = dualB R da db (.inl e.val) := by
  simp only [cutA,cutB,cutDart,if_neg h]
  exact ⟨rfl,rfl⟩

/-- Zero-current copies cannot occur in this actual cut carrier. -/
theorem cut_current_pos {V E : Type*} [Fintype E]
    (a b : E → V) (phi : V → ℝ) (t : ℝ) (e : CutCopy a b phi t) :
    0 < current a b phi (cutDart a b phi t e) := by
  have hm := (mem_crossingEdges a b phi t e.val).mp e.property
  by_cases ha : phi (a e.val) < t
  · have hb : t ≤ phi (b e.val) := by
      rcases hm with hm | hm
      · exact hm.2
      · exact (not_le_of_gt ha hm.2).elim
    simp only [cutDart,if_pos ha]
    exact sub_pos.mpr (ha.trans_le hb)
  · have hb : phi (b e.val) < t := by
      rcases hm with hm | hm
      · exact (ha hm.1).elim
      · exact hm.1
    simp only [cutDart,if_neg ha]
    exact sub_pos.mpr (hb.trans_le (le_of_not_gt ha))

/-- The actual crossing dual copies increase the proved stream strictly. -/
theorem cut_stream_increasing {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (M t : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (e : CutCopy a b phi t) : psi (cutA R da db phi t e) < psi (cutB R da db phi t e) := by
  have hj := hp (.inl (cutDart a b phi t e))
  exact sub_pos.mp ((cut_current_pos a b phi t e).trans_eq hj.symm)

/-- The positive increment is exactly the physical original copied current. -/
theorem cut_stream_increment {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (M t : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (e : CutCopy a b phi t) :
    psi (cutB R da db phi t e)-psi (cutA R da db phi t e) = current a b phi (cutDart a b phi t e) :=
  hp (.inl (cutDart a b phi t e))

end FiniteAvalanches.Electrical.Plane
