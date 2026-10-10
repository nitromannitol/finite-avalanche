import FiniteAvalanches.Electrical.Geometry.DeletedArcFace
import FiniteAvalanches.Electrical.Geometry.SourcePrimalDrawing

/-! The original marked lattice arc in the actual contracted source drawing. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.DrawingContraction
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical
noncomputable section

/-- All original positive-coordinate IDs surviving source loop deletion in H. -/
abbrev PrimalCopy (D : Finset (Site 2)) (P : OneSet D) :=
  ↥((domainCopies D).filter (fun e =>
    project D P (originalA e) ≠ project D P (originalB e)))

def primalGraph (D : Finset (Site 2)) (P : OneSet D) :
    CopiedGraph (Vertex D P) (PrimalCopy D P) :=
  ⟨fun e => project D P (originalA e.val), fun e => project D P (originalB e.val)⟩

/-- The exact original marked ID, before its deletion from H. -/
def markedPrimal (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    PrimalCopy D P := by
  refine ⟨marked.val, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · apply (mem_domainCopies D marked.val).mpr
    rcases marked.property with h | h
    · right
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ((project_eq_beta_iff D P _).mp h.2)
      exact hv ▸ v.property
    · left
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ((project_eq_beta_iff D P _).mp h.1)
      exact hv ▸ v.property
  · rcases marked.property with h | h
    · rw [h.1, h.2]
      exact Sum.inl_injective.ne (by decide)
    · rw [h.1, h.2]
      exact Sum.inl_injective.ne (by decide)

/-- H0 copies embed into H by their unchanged original ID. -/
def retainedPrimal (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (e : Copy D P marked) : PrimalCopy D P :=
  ⟨e.val, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp e.property).1,
    (Finset.mem_filter.mp e.property).2.1⟩⟩

theorem retainedPrimal_injective (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : Function.Injective (retainedPrimal D P marked) := by
  intro e f h
  have hv := congrArg (fun z : PrimalCopy D P => z.val) h
  exact Subtype.ext hv

theorem retainedPrimal_ne_marked (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (e : Copy D P marked) :
    retainedPrimal D P marked e ≠ markedPrimal D P marked := by
  intro h
  exact (Finset.mem_filter.mp e.property).2.2 (congrArg Subtype.val h)

/-- Delete only the actual marked copy, retaining each other copy's parametrized arc. -/
def deleteMarkedDrawing (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (Q : Drawing (primalGraph D P)) :
    Drawing (⟨copyA D P marked, copyB D P marked⟩ :
      CopiedGraph (Vertex D P) (Copy D P marked)) :=
  restrictDrawing Q (retainedPrimal D P marked) (retainedPrimal_injective D P marked)
    (fun _ => rfl) (fun _ => rfl)

/-- The deleted original arc selects a unique common face in the same actual H0
embedding, including its full endpoint approach and its original lattice realization. -/
theorem source_marked_common_face (D : Finset (Site 2)) (P : OneSet D)
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    ∃ q : Plane → Plane, Continuous q ∧ ∃ Q : Drawing (primalGraph D P),
      (∀ v : D, Q.point (project D P v.val) = q (sitePoint v.val)) ∧
      (∀ e t, Q.curve e t = q (unitSegment e.val.1 e.val.2 t.val)) ∧
      ∃ Q0 : PlaneEmbedding (⟨copyA D P marked, copyB D P marked⟩ :
        CopiedGraph (Vertex D P) (Copy D P marked)),
        Q0.drawing = deleteMarkedDrawing D P marked Q ∧
        ∃ face : Face Q0.drawing,
          (∀ t : ArcParameter, 0 < t.val → t.val < 1 →
            Q.curve (markedPrimal D P marked) t ∉ drawingTrace Q0.drawing) ∧
          (∀ t : ArcParameter, 0 < t.val → t.val < 1 →
            Q.curve (markedPrimal D P marked) t ∈ faceRegion Q0.drawing face) ∧
          Set.range (Q.curve (markedPrimal D P marked)) ⊆ closure (faceRegion Q0.drawing face) ∧
          incident Q0.drawing (alpha D P) face ∧ incident Q0.drawing (beta D P) face ∧
          (∀ face' : Face Q0.drawing,
            (∀ t : ArcParameter, 0 < t.val → t.val < 1 →
              Q.curve (markedPrimal D P marked) t ∈ faceRegion Q0.drawing face') →
            face' = face) ∧
        (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
          Q.curve (markedPrimal D P marked) ⟨0, by constructor <;> norm_num⟩ ∈
            closure (Q.curve (markedPrimal D P marked) ''
              {t : ArcParameter | 0 < t.val ∧ t.val < epsilon}) ∧
          Q.curve (markedPrimal D P marked) ⟨1, by constructor <;> norm_num⟩ ∈
            closure (Q.curve (markedPrimal D P marked) ''
              {t : ArcParameter | 1 - epsilon < t.val ∧ t.val < 1}) ∧
          Q.curve (markedPrimal D P marked) ''
              {t : ArcParameter | 0 < t.val ∧ t.val < epsilon} ⊆ faceRegion Q0.drawing face ∧
          Q.curve (markedPrimal D P marked) ''
              {t : ArcParameter | 1 - epsilon < t.val ∧ t.val < 1} ⊆ faceRegion Q0.drawing face) := by
  obtain ⟨q, hq, Q, hp, hc⟩ := source_primal_realization D P hDc hP marked
  let R := deleteMarkedDrawing D P marked Q
  obtain ⟨charts⟩ := ChartExistence.consume_arc_straightening
    FiniteAvalanches.External.parametrized_plane_arc_straightening R (copy_loopless D P marked)
  let Q0 := ChartExistence.planeEmbeddingOfCharts R (copy_loopless D P marked) charts
  have hoff (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
      Q.curve (markedPrimal D P marked) t ∉ drawingTrace Q0.drawing :=
    DeletedArc.omitted_interior_off_trace Q (retainedPrimal D P marked)
      (retainedPrimal_injective D P marked) (fun _ => rfl) (fun _ => rfl)
      (markedPrimal D P marked) (retainedPrimal_ne_marked D P marked) t ht0 ht1
  obtain ⟨face, hf, hcl, hu⟩ := DeletedArc.common_face Q0.drawing
    (Q.curve (markedPrimal D P marked)) (Q.continuous _) hoff
  have endpoints :
      Q.point (project D P (originalA marked.val)) ∈ closure (faceRegion Q0.drawing face) ∧
      Q.point (project D P (originalB marked.val)) ∈ closure (faceRegion Q0.drawing face) := ⟨hcl ⟨⟨0, by constructor <;> norm_num⟩, Q.start _⟩,
    hcl ⟨⟨1, by constructor <;> norm_num⟩, Q.finish _⟩⟩
  have hab : incident Q0.drawing (alpha D P) face ∧ incident Q0.drawing (beta D P) face := by
    rcases marked.property with h | h
    · exact ⟨h.1 ▸ endpoints.1, h.2 ▸ endpoints.2⟩
    · exact ⟨h.2 ▸ endpoints.2, h.1 ▸ endpoints.1⟩
  refine ⟨q, hq, Q, hp, hc, Q0, rfl, face, hoff, hf, hcl, hab.1, hab.2, hu, ?_⟩
  intro epsilon he0 he1
  have hg := DeletedArc.endpoint_germs (Q.curve (markedPrimal D P marked))
    (Q.continuous _) epsilon he0 he1
  refine ⟨hg.1, hg.2, ?_, ?_⟩
  · rintro z ⟨t, ht, rfl⟩
    exact hf t ht.1 (ht.2.trans he1)
  · rintro z ⟨t, ht, rfl⟩
    exact hf t (by linarith [ht.1]) ht.2

end
end FiniteAvalanches.Electrical.LatticeDrawing
