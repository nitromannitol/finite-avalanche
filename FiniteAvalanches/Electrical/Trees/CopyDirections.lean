import FiniteAvalanches.Electrical.Trees.TwoCopyGroves

/-! Endpoint reorientation changes neither original copies nor tree/grove subsets. -/
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- Reverse selected endpoint conventions without changing the copy carrier. -/
def reorient (rev : E → Bool) : CopiedGraph V E where
  left e := if rev e then J.right e else J.left e
  right e := if rev e then J.left e else J.right e

omit [Fintype V] [Fintype E] in
theorem reorient_reaches (rev : E → Bool) (F : Finset E) :
    (reorient J rev).reaches F = J.reaches F := by
  unfold CopiedGraph.reaches
  congr 1
  funext x y
  apply propext
  apply exists_congr
  intro e
  cases h : rev e <;> simp [reorient,h,or_comm]

omit [Fintype V] [Fintype E] in
theorem reorient_forest (rev : E → Bool) (F : Finset E) :
    (∀ e ∈ F, ¬(reorient J rev).reaches (F.erase e)
      ((reorient J rev).left e) ((reorient J rev).right e)) ↔
    (∀ e ∈ F, ¬J.reaches (F.erase e) (J.left e) (J.right e)) := by
  simp only [reorient_reaches]
  apply forall_congr'
  intro e
  apply imp_congr_right
  intro _
  cases h : rev e
  · simp [reorient,h]
  · simp only [reorient,h,↓reduceIte]
    exact not_congr ⟨reaches_symm J,reaches_symm J⟩

/-- Both maps retain the exact same finite subset of original IDs. -/
def reorientTreeEquiv (rev : E → Bool) : J.SpanningTree ≃ (reorient J rev).SpanningTree :=
  Equiv.subtypeEquivRight (fun F => by
    rw [reorient_forest]
    simp only [reorient_reaches])

/-- Every component and every forest certificate is invariant under endpoint reorientation. -/
def reorientGroveEquiv (rev : E → Bool) (u a b c d v : V) :
    PathGrove J u a b c d v ≃ PathGrove (reorient J rev) u a b c d v :=
  Equiv.subtypeEquivRight (fun F => by
    rw [reorient_forest]
    simp only [reorient_reaches])

/-- Orient the two designated copies from `a` and `c`, retaining their original IDs. -/
def boundaryDirections (e f : E) (a c : V) : E → Bool :=
  fun g => if g = e then decide (J.left e ≠ a)
    else if g = f then decide (J.left f ≠ c) else false

omit [Fintype V] [Fintype E] in
private theorem orient_endpoints (g : E) (a b : V) (rev : E → Bool)
    (hrev : rev g = decide (J.left g ≠ a))
    (hends : (J.left g = a ∧ J.right g = b) ∨ (J.right g = a ∧ J.left g = b)) :
    (reorient J rev).left g = a ∧ (reorient J rev).right g = b := by
  rcases hends with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simp [reorient,hrev,ha,hb]
  · by_cases h : J.left g = a
    · have hab : a = b := h.symm.trans hb
      simp [reorient,hrev,h,ha,hab]
    · have hrev' : rev g = true := by rw [hrev]; exact decide_eq_true h
      simp only [reorient,hrev',↓reduceIte]
      exact ⟨ha,hb⟩

omit [Fintype V] [Fintype E] in
theorem boundaryDirections_endpoints (e f : E) (hef : e ≠ f) (a b c d : V)
    (he : (J.left e = a ∧ J.right e = b) ∨ (J.right e = a ∧ J.left e = b))
    (hf : (J.left f = c ∧ J.right f = d) ∨ (J.right f = c ∧ J.left f = d)) :
    let H := reorient J (boundaryDirections J e f a c)
    H.left e = a ∧ H.right e = b ∧ H.left f = c ∧ H.right f = d := by
  have he' := orient_endpoints J e a b (boundaryDirections J e f a c) (by simp [boundaryDirections]) he
  have hf' := orient_endpoints J f c d (boundaryDirections J e f a c)
    (by simp [boundaryDirections,hef.symm]) hf
  exact ⟨he'.1,he'.2,hf'.1,hf'.2⟩

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
