import FiniteAvalanches.Wilson.Lattice.WiredForestOrientation

/-! Wired rooted forests together with their unused root directions. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- An arbitrary direction at every prescribed wired root. -/
abbrev WiredRootDirections (R : RootPair) (N : ℕ) :=
  {v : FiniteWired.Vertex N // v ∈ (wiredRoots R N).val} → FiniteWired.Direction

/-- Extend a rooted forest's rootward directions by arbitrary directions at roots. -/
def forestDirectionsWithRoots (R : RootPair) (N : ℕ) (F : FiniteForest R N)
    (d : WiredRootDirections R N) : GoodArrows (wiredRoots R N).val (wiredHead N) := by
  let a : FiniteWired.Vertex N → FiniteWired.Direction := fun v =>
    if hv : v ∈ (wiredRoots R N).val then d ⟨v, hv⟩ else forestDirection R N F v
  refine ⟨a, ?_⟩
  intro c hc
  apply (forestDirections R N F).property c
  apply hc.congr
  intro v hv
  have hnot := hc.avoids_roots v hv
  simp only [a, dif_neg hnot, forestDirections]

/-- The arbitrary choices at roots do not alter the underlying forest. -/
theorem wiredArrowForest_forestDirectionsWithRoots (R : RootPair) (N : ℕ)
    (F : FiniteForest R N) (d : WiredRootDirections R N) :
    wiredArrowForest R N (forestDirectionsWithRoots R N F d) = F := by
  have he : wiredArrowForest R N (forestDirectionsWithRoots R N F d) =
      wiredArrowForest R N (forestDirections R N F) := by
    apply wiredArrowForest_eq_of_nonroot_eq
    intro v hv
    simp only [forestDirectionsWithRoots, dif_neg hv, forestDirections]
  exact he.trans (wiredArrowForest_forestDirections R N F)

/-- Good wired directions are exactly a rooted forest and independent root directions. -/
def wiredArrowForestEquiv (R : RootPair) (N : ℕ) :
    GoodArrows (wiredRoots R N).val (wiredHead N) ≃
      FiniteForest R N × WiredRootDirections R N where
  toFun a := (wiredArrowForest R N a, fun r => a.val r.val)
  invFun p := forestDirectionsWithRoots R N p.1 p.2
  left_inv a := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ (wiredRoots R N).val
    · simp only [forestDirectionsWithRoots, dif_pos hv]
    · have he := wiredArrowForest_eq_imp_nonroot_eq R N
        (forestDirections R N (wiredArrowForest R N a)) a
        (wiredArrowForest_forestDirections R N (wiredArrowForest R N a)) hv
      simpa only [forestDirectionsWithRoots, dif_neg hv, forestDirections] using he
  right_inv p := by
    apply Prod.ext
    · exact wiredArrowForest_forestDirectionsWithRoots R N p.1 p.2
    · funext r
      simp only [forestDirectionsWithRoots, dif_pos r.property]

end
end FiniteAvalanches.Wilson.Lattice
