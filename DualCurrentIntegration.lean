import TreeFlowIntegration

/-! Integrating a balanced primal current on its copied geometric dual. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LovaszStream
open StatementGeometry Plane
open scoped Classical BigOperators
noncomputable section
variable {V W E : Type} [Fintype V] [Fintype W] [Fintype E]

/-- Facial telescoping transposes to the primal Kirchhoff law for every dual potential. -/
theorem primalBoundary_dualGradient (J : CopiedGraph V E) (K : CopiedGraph W E)
    (hcycles : ∀ (q : V → ℝ) (F : W),
      copyBoundary K.left K.right (copyGradient J.left J.right q) F = 0)
    (psi : W → ℝ) (x : V) :
    copyBoundary J.left J.right (copyGradient K.left K.right psi) x = 0 := by
  let q : V → ℝ := fun y => if y = x then 1 else 0
  have hd := sum_mul_copyBoundary K.left K.right psi (copyGradient J.left J.right q)
  simp only [hcycles,mul_zero,Finset.sum_const_zero] at hd
  have hp := sum_mul_copyBoundary J.left J.right q (copyGradient K.left K.right psi)
  have hs : (∑ e, (q (J.left e)-q (J.right e))*copyGradient K.left K.right psi e) =
      ∑ e, (psi (K.left e)-psi (K.right e))*copyGradient J.left J.right q e := by
    apply Finset.sum_congr rfl
    intro e _
    exact mul_comm _ _
  have hb := hp.trans (hs.trans hd.symm)
  simpa only [q,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hb

/-- Complementary spanning trees and facial telescoping integrate every balanced copied current.
The tree integration is independent of the chosen tree, by uniqueness of the grounded potential. -/
theorem existsUnique_dual_gradient_of_tree_complement
    (J : CopiedGraph V E) (K : CopiedGraph W E) (root : V) (ground : W)
    (hc : (supportGraph J.left J.right).Preconnected)
    (hcomp : ∀ T : Finset E,
      (∃ t : J.SpanningTree, t.val = T) ↔
      (∃ t : K.SpanningTree, t.val = Finset.univ \ T))
    (hcycles : ∀ (q : V → ℝ) (F : W),
      copyBoundary K.left K.right (copyGradient J.left J.right q) F = 0)
    (j : E → ℝ) (hj : ∀ x, copyBoundary J.left J.right j x = 0) :
    ∃! psi : W → ℝ, psi ground = 0 ∧ ∀ e, psi (K.right e)-psi (K.left e) = j e := by
  obtain ⟨T⟩ := exists_spanningTree J root hc
  obtain ⟨U,hU⟩ := (hcomp T.val).mp ⟨T,rfl⟩
  obtain ⟨psi,hpsi,huniq⟩ := existsUnique_tree_gradient K U ground (fun e => -(j e.val))
  let r : E → ℝ := fun e => j e+copyGradient K.left K.right psi e
  have hoff (e : E) (he : e ∉ T.val) : r e = 0 := by
    have heU : e ∈ U.val := by
      rw [hU]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e,he⟩
    have h := hpsi.2 ⟨e,heU⟩
    dsimp [r,copyGradient]
    linarith only [h]
  have hb (x : V) : copyBoundary J.left J.right r x = 0 := by
    have ha := congrFun ((boundaryMap J.left J.right).map_add j (copyGradient K.left K.right psi)) x
    change copyBoundary J.left J.right r x = copyBoundary J.left J.right j x+
      copyBoundary J.left J.right (copyGradient K.left K.right psi) x at ha
    rw [ha,hj x,primalBoundary_dualGradient J K hcycles psi x,add_zero]
  have hr := flow_eq_zero_of_forest J T.val T.property.2.2 r hoff hb
  refine ⟨psi,⟨hpsi.1,?_⟩,?_⟩
  · intro e
    have h := congrFun hr e
    change j e+(psi (K.left e)-psi (K.right e)) = 0 at h
    linarith only [h]
  · intro chi hchi
    apply huniq chi
    refine ⟨hchi.1,?_⟩
    intro e
    have h := hchi.2 e.val
    linarith only [h]

end
end FiniteAvalanches.Electrical.LovaszStream

#print axioms FiniteAvalanches.Electrical.LovaszStream.primalBoundary_dualGradient
#print axioms FiniteAvalanches.Electrical.LovaszStream.existsUnique_dual_gradient_of_tree_complement
