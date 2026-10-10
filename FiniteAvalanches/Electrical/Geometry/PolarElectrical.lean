import FiniteAvalanches.Electrical.Geometry.PolarStream

/-! Conditional consumption of the exact UNREGISTERED finite-plane topology
candidate. All electrical equalities below are proved from actual copied incidence,
Poisson uniqueness and REGISTERED BSST. No electrical identity is assumed. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Source
open StatementGeometry Plane
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

private theorem polar_poisson_of_cycle_law (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta)
    [Fintype A.embedding.Face] (psi : A.embedding.Face → ℝ)
    (hpsi : stream_spec D alpha beta A (voltage J alpha beta hc) psi)
    (hcycle : ∀ F : A.embedding.Face,
      copyBoundary (augmentedDual A).left (augmentedDual A).right
        (copyGradient (augmentedGraph J alpha beta).left
          (augmentedGraph J alpha beta).right (voltage J alpha beta hc)) F = 0)
    (F : A.embedding.Face) (hF : F ≠ polarGround A) :
    laplacian (polarDual A).left (polarDual A).right psi F =
      if F = polarSource A then 1 else 0 := by
  let phi := voltage J alpha beta hc
  let j : E → ℝ := copyGradient J.left J.right phi
  have hphi := voltage_spec J alpha beta hne hc
  have hunit : ∀ u : Unit, u = () := fun u => Subsingleton.elim u ()
  have hc0 : copyBoundary (polarDual A).left (polarDual A).right j F +
      ((if polarGround A = F then (-1 : ℝ) else 0) -
       (if polarSource A = F then (-1 : ℝ) else 0)) = 0 := by
    convert hcycle F using 1
    simp [copyBoundary,Fintype.sum_sum_type,
        augmentedDual,polarDual,copyGradient,augmentedGraph,
        polarGround,polarSource,hunit,hphi.1,hphi.2.1,phi,j]
    ring_nf
  have hg : copyGradient (polarDual A).left (polarDual A).right psi = -j := by
    funext e
    have hs := hpsi.1 e
    change psi ((polarDual A).right e) - psi ((polarDual A).left e) = j e at hs
    change psi ((polarDual A).left e) - psi ((polarDual A).right e) = -(j e)
    linarith
  rw [← copyBoundary_gradient,hg]
  have hn := congrFun ((boundaryMap (polarDual A).left (polarDual A).right).map_neg j) F
  change copyBoundary (polarDual A).left (polarDual A).right (-j) F =
      -copyBoundary (polarDual A).left (polarDual A).right j F at hn
  rw [hn]
  by_cases hv : F = polarSource A
  · simp only [if_neg hF.symm,if_pos hv.symm,sub_neg_eq_add,zero_add] at hc0
    rw [if_pos hv]
    linarith
  · simp only [if_neg hF.symm,if_neg (Ne.symm hv),sub_self,add_zero] at hc0
    rw [if_neg hv,hc0,neg_zero]

/-- Complete polar Green/current/once-copy-energy correspondence. Only the exact
classical topology theorem is conditional; no requested electrical law or paper
estimate appears in that binder. The full actual face carrier is retained. -/
theorem polar_electrical_duality_of_classical
    (hclassical : ∀ {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (_hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (_hne : alpha ≠ beta) (A : OuterArc D alpha beta),
    ∃ finiteFaces : Fintype A.embedding.Face,
      letI : Fintype A.embedding.Face := finiteFaces
      polarGround A ≠ polarSource A ∧
      (supportGraph (polarDual A).left (polarDual A).right).Preconnected ∧
      (∀ T : Finset (E ⊕ Unit),
        (∃ t : (augmentedGraph J alpha beta).SpanningTree, t.val = T) ↔
        (∃ t : (augmentedDual A).SpanningTree, t.val = Finset.univ \ T)) ∧
      (∀ (q : V → ℝ) (F : A.embedding.Face),
        copyBoundary (augmentedDual A).left (augmentedDual A).right
          (copyGradient (augmentedGraph J alpha beta).left
            (augmentedGraph J alpha beta).right q) F = 0))
    (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) :
    ∃ finiteFaces : Fintype A.embedding.Face,
      letI : Fintype A.embedding.Face := finiteFaces
      polarGround A ≠ polarSource A ∧
      ∃ hd : (supportGraph (polarDual A).left (polarDual A).right).Preconnected,
        (∀ T : Finset (E ⊕ Unit),
          (∃ t : (augmentedGraph J alpha beta).SpanningTree, t.val = T) ↔
          (∃ t : (augmentedDual A).SpanningTree, t.val = Finset.univ \ T)) ∧
        let g := groundedGreen (polarDual A).left (polarDual A).right
          (polarGround A) hd (polarSource A)
        stream_spec D alpha beta A (voltage J alpha beta hc) g ∧
        g (polarSource A) = mass J (voltage J alpha beta hc) ∧
        (∀ e, g ((polarDual A).right e)-g ((polarDual A).left e) =
          voltage J alpha beta hc (J.left e)-voltage J alpha beta hc (J.right e)) ∧
        energy (polarDual A).left (polarDual A).right g = mass J (voltage J alpha beta hc) := by
  obtain ⟨finiteFaces,hp,hd,htrees,hcycle⟩ := hclassical J D hc alpha beta hne A
  letI : Fintype A.embedding.Face := finiteFaces
  obtain ⟨psi,hpsi,_⟩ := existsUnique_polar_stream J D hc alpha beta hne A
  have hg : psi = groundedGreen (polarDual A).left (polarDual A).right
      (polarGround A) hd (polarSource A) := by
    exact groundedPoisson_eq (polarDual A).left (polarDual A).right
      (polarGround A) hd (fun F => if F = polarSource A then 1 else 0) psi
      ⟨hpsi.2.2.1,fun F hF =>
      polar_poisson_of_cycle_law J D hc alpha beta hne A psi hpsi
        (hcycle (voltage J alpha beta hc)) F hF⟩
  refine ⟨finiteFaces,hp,hd,htrees,?_,?_,?_,?_⟩
  · rw [← hg]; exact hpsi
  · rw [← hg]; exact hpsi.2.2.2
  · intro e; rw [← hg]; exact hpsi.1 e
  · rw [energy_groundedGreen_eq,← hg]; exact hpsi.2.2.2


end
end FiniteAvalanches.Electrical.Source
