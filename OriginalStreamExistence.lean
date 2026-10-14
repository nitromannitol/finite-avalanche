import PhysicalStreamExistence
import FiniteAvalanches.Electrical.SplitStep.OriginalPhysicalGeometry

/-! The unique grounded stream on the original S7 full-H face carrier. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LovaszStream
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing SplitStep
open scoped Classical
noncomputable section

/-- The physical battery-right face, expressed in the original marked-copy storage orientation. -/
def originalGroundFace (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e) : Face Q :=
  if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
    (sourceDualGraph D P Q charts).left (markedPrimal D P marked)
  else (sourceDualGraph D P Q charts).right (markedPrimal D P marked)

/-- The physical battery-left face, on the same original copied edge and face carrier. -/
def originalSourceFace (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e) : Face Q :=
  if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
    (sourceDualGraph D P Q charts).right (markedPrimal D P marked)
  else (sourceDualGraph D P Q charts).left (markedPrimal D P marked)

/-- Literal original-copy signed-current equations and zero/mass battery-face values. -/
def originalStreamSpec (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (psi : Face Q → ℝ) : Prop :=
  (∀ e : Copy D P marked,
    psi ((sourceDeletedDualGraph D P marked Q charts).right e)-
      psi ((sourceDeletedDualGraph D P marked Q charts).left e) =
      Repair8.voltage D P hD marked (copyA D P marked e)-
        Repair8.voltage D P hD marked (copyB D P marked e)) ∧
  psi (originalGroundFace D P marked Q charts) = 0 ∧
  psi (originalSourceFace D P marked Q charts) =
    mass (originalGraph D P marked) (Repair8.voltage D P hD marked)

/-- The checked marked-side dictionary maps both original poles to their physical battery faces. -/
theorem original_poles_map (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (faces : Face Q ≃ A.embedding.Face)
    (hmarked : if (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P then
      faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.rightFace (.inr ()) ∧
      faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.leftFace (.inr ())
    else
      faces ((sourceDualGraph D P Q charts).left (markedPrimal D P marked)) = A.embedding.leftFace (.inr ()) ∧
      faces ((sourceDualGraph D P Q charts).right (markedPrimal D P marked)) = A.embedding.rightFace (.inr ())) :
    faces (originalGroundFace D P marked Q charts) = polarGround A ∧
      faces (originalSourceFace D P marked Q charts) = polarSource A := by
  by_cases ha : (LatticeDrawing.primalGraph D P).left (markedPrimal D P marked) = alpha D P
  · simp only [if_pos ha] at hmarked
    simp only [originalGroundFace,originalSourceFace,if_pos ha]
    exact hmarked
  · simp only [if_neg ha] at hmarked
    simp only [originalGroundFace,originalSourceFace,if_neg ha]
    exact ⟨hmarked.2,hmarked.1⟩

/-- The original S7 stream exists uniquely without an assumed stream, face equivalence or rotation. -/
theorem existsUnique_original_stream (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e) :
    ∃! psi : Face Q → ℝ, originalStreamSpec D P hD marked Q charts psi := by
  obtain ⟨B,A,faces,hretained,hmarked⟩ := original_marked_physical_geometry D P marked Q charts
  obtain ⟨hg,hs⟩ := original_poles_map D P marked Q charts B A faces hmarked
  have hp := Repair8.voltage_spec D P hD marked
  obtain ⟨psi,hpsi,huniq⟩ := existsUnique_physical_stream (originalGraph D P marked) B
    (Repair8.graph_connected D P hD marked).preconnected (alpha D P) (beta D P)
    (by intro h; cases h) A (Repair8.voltage D P hD marked) hp.1 hp.2.1 hp.2.2
  refine ⟨psi ∘ faces,⟨?_,?_,?_⟩,?_⟩
  · intro e
    simp only [Function.comp_apply,(hretained e).1,(hretained e).2]
    exact hpsi.1 e
  · change psi (faces (originalGroundFace D P marked Q charts)) = 0
    rw [hg]
    exact hpsi.2.2.1
  · change psi (faces (originalSourceFace D P marked Q charts)) = _
    rw [hs]
    exact hpsi.2.2.2
  · intro chi hchi
    have hgback : faces.symm (polarGround A) = originalGroundFace D P marked Q charts := by
      simpa only [Equiv.symm_apply_apply] using (congrArg faces.symm hg).symm
    have hsback : faces.symm (polarSource A) = originalSourceFace D P marked Q charts := by
      simpa only [Equiv.symm_apply_apply] using (congrArg faces.symm hs).symm
    have hc : stream_spec B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked)
        (chi ∘ faces.symm) := by
      refine ⟨?_,?_,?_,?_⟩
      · intro e
        have hr : faces.symm (A.embedding.rightFace (.inl e)) =
            (sourceDeletedDualGraph D P marked Q charts).left e := by
          simpa only [Equiv.symm_apply_apply] using (congrArg faces.symm (hretained e).1).symm
        have hl : faces.symm (A.embedding.leftFace (.inl e)) =
            (sourceDeletedDualGraph D P marked Q charts).right e := by
          simpa only [Equiv.symm_apply_apply] using (congrArg faces.symm (hretained e).2).symm
        change chi (faces.symm (A.embedding.leftFace (.inl e)))-
          chi (faces.symm (A.embedding.rightFace (.inl e))) = _
        rw [hl,hr]
        simpa only [originalGraph] using hchi.1 e
      · change chi (faces.symm (polarSource A))-chi (faces.symm (polarGround A)) = _
        rw [hsback,hgback,hchi.2.2,hchi.2.1,sub_zero]
      · change chi (faces.symm (polarGround A)) = 0
        rw [hgback]
        exact hchi.2.1
      · change chi (faces.symm (polarSource A)) = _
        rw [hsback]
        exact hchi.2.2
    have heq := huniq (chi ∘ faces.symm) hc
    funext F
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun heq (faces F)

/-- Selected from the proved full unique original-face characterization. -/
def originalStream (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e) : Face Q → ℝ :=
  (existsUnique_original_stream D P hD marked Q charts).choose

/-- Complete original-current and both-pole-value characterization of the chosen field. -/
theorem originalStream_spec (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e) :
    originalStreamSpec D P hD marked Q charts (originalStream D P hD marked Q charts) :=
  (existsUnique_original_stream D P hD marked Q charts).choose_spec.1

/-- Uniqueness makes every produced physical-face dictionary give this same original field. -/
theorem originalStream_unique (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (psi : Face Q → ℝ) (hpsi : originalStreamSpec D P hD marked Q charts psi) :
    psi = originalStream D P hD marked Q charts :=
  (existsUnique_original_stream D P hD marked Q charts).choose_spec.2 psi hpsi

/-- Chart witnesses for the actual source drawing are produced by the registered arc input. -/
theorem original_stream_supplier (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) :
    ∃ charts : ∀ e, EdgeChart Q e,
      ∃! psi : Face Q → ℝ, originalStreamSpec D P hD marked Q charts psi := by
  obtain ⟨charts⟩ := ChartExistence.consume_arc_straightening
    FiniteAvalanches.External.parametrized_plane_arc_straightening Q (primal_loopless D P)
  exact ⟨charts,existsUnique_original_stream D P hD marked Q charts⟩

end
end FiniteAvalanches.Electrical.LovaszStream

#print axioms FiniteAvalanches.Electrical.LovaszStream.existsUnique_original_stream
#print axioms FiniteAvalanches.Electrical.LovaszStream.originalStream
#print axioms FiniteAvalanches.Electrical.LovaszStream.originalStream_spec
#print axioms FiniteAvalanches.Electrical.LovaszStream.originalStream_unique
#print axioms FiniteAvalanches.Electrical.LovaszStream.original_stream_supplier
