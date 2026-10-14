import DualCurrentIntegration
import FiniteAvalanches.External.TwoPoleTopology
import FiniteAvalanches.Electrical.Plane.DualIncidence

/-! A noncircular normalized current stream on actual augmented complement faces. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LovaszStream
open StatementGeometry Source Plane
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- The original harmonic current closes with +mass on the literal alpha-to-beta battery. -/
theorem physical_current_balanced (J : CopiedGraph V E) (alpha beta : V) (hne : alpha ≠ beta)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0) (x : V) :
    copyBoundary (augmentedGraph J alpha beta).left (augmentedGraph J alpha beta).right
      (physicalArcFlow J.left J.right phi (mass J phi)) x = 0 := by
  have ha : (augmentedGraph J alpha beta).left = arcA J.left alpha := by
    funext z
    cases z <;> rfl
  have hb : (augmentedGraph J alpha beta).right = arcB J.right beta := by
    funext z
    cases z <;> rfl
  rw [ha,hb,copyBoundary_physical]
  exact arcDivergence_eq_zero J.left J.right phi alpha beta hne hp0 hp1 hh x

/-- The complete grounded physical stream exists uniquely, with no tiling input.
All finite-face, tree-complement and facial-cycle obligations are supplied internally by topology. -/
theorem existsUnique_physical_stream (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0) :
    ∃! psi : A.embedding.Face → ℝ, stream_spec D alpha beta A phi psi := by
  obtain ⟨finiteFaces,_hpoles,hpolar,hcomp,hcycles⟩ :=
    FiniteAvalanches.External.finite_plane_two_pole_topology J D hc alpha beta hne A
  letI : Fintype A.embedding.Face := finiteFaces
  letI : DecidableEq (E ⊕ Unit) := Classical.decEq _
  have haug : (supportGraph (augmentedGraph J alpha beta).left
      (augmentedGraph J alpha beta).right).Preconnected := hc.mono (by
    intro x y h
    obtain ⟨hx,e,he⟩ := h
    exact ⟨hx,.inl e,he⟩)
  have hcomp' : ∀ T : Finset (E ⊕ Unit),
      (∃ t : (augmentedGraph J alpha beta).SpanningTree, t.val = T) ↔
      (∃ t : (augmentedDual A).SpanningTree, t.val = Finset.univ \ T) := by
    intro T
    constructor
    · intro ht
      obtain ⟨u,hu⟩ := (hcomp T).mp ht
      refine ⟨u,hu.trans ?_⟩
      ext e
      simp only [Finset.mem_sdiff,Finset.mem_univ]
    · rintro ⟨u,hu⟩
      apply (hcomp T).mpr
      refine ⟨u,hu.trans ?_⟩
      ext e
      simp only [Finset.mem_sdiff,Finset.mem_univ]
  obtain ⟨psi,hpsi,_hunique⟩ := existsUnique_dual_gradient_of_tree_complement
    (augmentedGraph J alpha beta) (augmentedDual A) alpha (polarGround A) haug hcomp' hcycles
    (physicalArcFlow J.left J.right phi (mass J phi))
    (physical_current_balanced J alpha beta hne phi hp0 hp1 hh)
  have hcurrent (e : E) :
      psi (A.embedding.leftFace (.inl e))-psi (A.embedding.rightFace (.inl e)) =
        phi (J.left e)-phi (J.right e) := hpsi.2 (.inl e)
  have hbattery : psi (polarSource A)-psi (polarGround A) = mass J phi := hpsi.2 (.inr ())
  have hsource : psi (polarSource A) = mass J phi := by
    rw [hpsi.1,sub_zero] at hbattery
    exact hbattery
  refine ⟨psi,⟨hcurrent,hpsi.2 (.inr ()),hpsi.1,hsource⟩,?_⟩
  intro chi hchi
  have hedge (e : E) : (chi-psi) ((polarDual A).left e) = (chi-psi) ((polarDual A).right e) := by
    have h1 := hchi.1 e
    have h2 := hcurrent e
    simp only [Pi.sub_apply]
    change chi (A.embedding.rightFace (.inl e))-psi (A.embedding.rightFace (.inl e)) =
      chi (A.embedding.leftFace (.inl e))-psi (A.embedding.leftFace (.inl e))
    linarith only [h1,h2]
  funext F
  have h := eq_of_reachable (polarDual A).left (polarDual A).right (chi-psi) hedge
    (hpolar F (polarGround A))
  have hz : (chi-psi) (polarGround A) = 0 := by
    change chi (polarGround A)-psi (polarGround A) = 0
    have hg : chi (polarGround A) = 0 := hchi.2.2.1
    rw [hg,hpsi.1,sub_self]
  rw [hz] at h
  exact sub_eq_zero.mp h

/-- The physical stream is selected only from its complete proved unique characterization. -/
def physicalStream (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0) :
    A.embedding.Face → ℝ :=
  (existsUnique_physical_stream J D hc alpha beta hne A phi hp0 hp1 hh).choose

/-- Full original-copy currents and both literal battery-face values. -/
theorem physicalStream_spec (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0) :
    stream_spec D alpha beta A phi (physicalStream J D hc alpha beta hne A phi hp0 hp1 hh) :=
  (existsUnique_physical_stream J D hc alpha beta hne A phi hp0 hp1 hh).choose_spec.1

/-- The characterization makes the selected field independent of every integration-tree choice. -/
theorem physicalStream_unique (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian J.left J.right phi x = 0)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi) :
    psi = physicalStream J D hc alpha beta hne A phi hp0 hp1 hh :=
  (existsUnique_physical_stream J D hc alpha beta hne A phi hp0 hp1 hh).choose_spec.2 psi hpsi

end
end FiniteAvalanches.Electrical.LovaszStream

#print axioms FiniteAvalanches.Electrical.LovaszStream.physical_current_balanced
#print axioms FiniteAvalanches.Electrical.LovaszStream.existsUnique_physical_stream
#print axioms FiniteAvalanches.Electrical.LovaszStream.physicalStream
#print axioms FiniteAvalanches.Electrical.LovaszStream.physicalStream_spec
#print axioms FiniteAvalanches.Electrical.LovaszStream.physicalStream_unique
