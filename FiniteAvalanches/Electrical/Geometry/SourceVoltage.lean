import FiniteAvalanches.Electrical.Geometry.OrientedDrawing
import FiniteAvalanches.Electrical.Dirichlet
import FiniteAvalanches.Electrical.Energy

namespace FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.StatementGeometry
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
/-- Connectedness supplies the Dirichlet boundary condition before voltage choice. -/
theorem two_terminal_reachable (J : CopiedGraph V E) (alpha beta : V)
    (hc : (supportGraph J.left J.right).Preconnected) :
    ∀ x, ∃ y ∈ ({alpha,beta} : Finset V), (supportGraph J.left J.right).Reachable x y :=
  fun x => ⟨alpha,by simp,hc x alpha⟩

/-- The actual unique zero/one Dirichlet voltage of the original copied network. -/
def voltage (J : CopiedGraph V E) (alpha beta : V)
    (hc : (supportGraph J.left J.right).Preconnected) : V → ℝ :=
  harmonicExtension J.left J.right {alpha,beta} (two_terminal_reachable J alpha beta hc)
    (fun x => if x = beta then 1 else 0)

theorem voltage_spec (J : CopiedGraph V E) (alpha beta : V) (hne : alpha ≠ beta)
    (hc : (supportGraph J.left J.right).Preconnected) :
    voltage J alpha beta hc alpha = 0 ∧ voltage J alpha beta hc beta = 1 ∧
      ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right (voltage J alpha beta hc) x = 0 := by
  have h := harmonicExtension_spec J.left J.right {alpha,beta}
    (two_terminal_reachable J alpha beta hc) (fun x => if x = beta then (1 : ℝ) else 0)
  refine ⟨?_,?_,?_⟩
  · simpa only [voltage,if_neg hne] using h.1 alpha (by simp)
  · simpa [voltage] using h.1 beta (by simp)
  · intro x ha hb
    exact h.2 x (by simp [ha,hb])

/-- The full source characterization uniquely determines the chosen voltage. -/
theorem voltage_unique (J : CopiedGraph V E) (alpha beta : V) (hne : alpha ≠ beta)
    (hc : (supportGraph J.left J.right).Preconnected) (f : V → ℝ)
    (ha : f alpha = 0) (hb : f beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right f x = 0) :
    f = voltage J alpha beta hc := by
  apply harmonicExtension_eq J.left J.right {alpha,beta}
    (two_terminal_reachable J alpha beta hc) (fun x => if x = beta then 1 else 0)
  constructor
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [ha,if_neg hne]
    · rw [hb,if_pos rfl]
  · intro x hx
    have h : x ≠ alpha ∧ x ≠ beta := by simpa only
      [Finset.mem_insert,Finset.mem_singleton,not_or] using hx
    exact hh x h.1 h.2

def mass (J : CopiedGraph V E) (phi : V → ℝ) : ℝ := energy J.left J.right phi

/-- Physical original-edge currents and closing-arc current +M; the arc is not an energy edge. -/
def stream_spec {J : CopiedGraph V E} (D : PlaneEmbedding J) (alpha beta : V)
    (A : OuterArc D alpha beta) (phi : V → ℝ) (psi : A.embedding.Face → ℝ) : Prop :=
  (∀ e, psi (A.embedding.leftFace (.inl e))-psi (A.embedding.rightFace (.inl e)) =
    phi (J.left e)-phi (J.right e)) ∧
  psi (A.embedding.leftFace (.inr ()))-psi (A.embedding.rightFace (.inr ())) = mass J phi ∧
  psi (A.embedding.rightFace (.inr ())) = 0 ∧
  psi (A.embedding.leftFace (.inr ())) = mass J phi

/-- Each original copy's closed voltage/stream rectangle; zero-current copies are points. -/
def edgeSquare {J : CopiedGraph V E} (D : PlaneEmbedding J) (alpha beta : V)
    (A : OuterArc D alpha beta) (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (e : E) : Set Plane :=
  Set.Icc (min (phi (J.left e)) (phi (J.right e))) (max (phi (J.left e)) (phi (J.right e))) ×ˢ
    Set.Icc (min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))))
      (max (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))))

end
end FiniteAvalanches.Electrical.Source
