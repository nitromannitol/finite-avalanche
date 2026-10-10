import FiniteAvalanches.Electrical.Geometry.PhysicalVertexRange
import FiniteAvalanches.External.PlaneVertexFaceStar
import FiniteAvalanches.Electrical.Geometry.PhysicalTilingStream

namespace FiniteAvalanches.Electrical.PhysicalFaceStar14
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open scoped Classical
noncomputable section

/-- Original copied paths remain copied paths after adding the actual closing arc. -/
theorem augmented_reaches {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta u v : V) :
    (Source.augmentedGraph J alpha beta).reaches Finset.univ u v := by
  have h := ((supportGraph J.left J.right).reachable_iff_reflTransGen u v).mp (hc u v)
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z h hyz ih =>
    obtain ⟨_,e,he⟩ := hyz
    exact ih.tail ⟨Sum.inl e,Finset.mem_univ _,he⟩

/-- The actual nonterminal physical face star is finite and connected through original IDs.
Only the closing arc is excluded, because neither of its endpoints is this vertex. -/
theorem physical_original_face_star {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (x : {v : V // v ≠ alpha ∧ v ≠ beta}) :
    {F : A.embedding.Face | incident A.embedding.drawing x.val F}.Nonempty ∧
    {F : A.embedding.Face | incident A.embedding.drawing x.val F}.Finite ∧
    (∀ F : A.embedding.Face, incident A.embedding.drawing x.val F ↔
      ∃ e : E, (J.left e=x.val ∨ J.right e=x.val) ∧
        F ∈ edgeFaces A.embedding.drawing (.inl e)) ∧
    (∀ F G : A.embedding.Face, incident A.embedding.drawing x.val F →
      incident A.embedding.drawing x.val G → Relation.ReflTransGen
        (fun B C : A.embedding.Face => ∃ e : E, (J.left e=x.val ∨ J.right e=x.val) ∧
          B ∈ edgeFaces A.embedding.drawing (.inl e) ∧
          C ∈ edgeFaces A.embedding.drawing (.inl e)) F G) := by
  letI : Nonempty (E ⊕ Unit) := ⟨Sum.inr ()⟩
  have h := FiniteAvalanches.External.plane_vertex_face_star V (E ⊕ Unit)
    (Source.augmentedGraph J alpha beta) A.embedding.drawing
    (augmented_reaches J hc alpha beta) x.val
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro F
    constructor
    · intro hF
      obtain ⟨z,hz,he⟩ := (h.2.2.1 F).mp hF
      cases z with
      | inl e => exact ⟨e,hz,he⟩
      | inr z =>
        rcases hz with hz | hz
        · exact (x.property.1 hz.symm).elim
        · exact (x.property.2 hz.symm).elim
    · rintro ⟨e,he,hF⟩
      exact (h.2.2.1 F).mpr ⟨Sum.inl e,he,hF⟩
  · intro F G hF hG
    have hr := h.2.2.2 F G hF hG
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail B C hr hBC ih =>
      obtain ⟨z,hz,hB,hC⟩ := hBC
      cases z with
      | inl e =>
        have hBi := edgeFaces_endpoints A.embedding.drawing (.inl e) B hB
        have hB' : incident A.embedding.drawing x.val B := by
          rcases hz with hl | hr
          · exact hl ▸ hBi.1
          · exact hr ▸ hBi.2
        exact (ih hB').tail ⟨e,hz,hB,hC⟩
      | inr z =>
        rcases hz with hz | hz
        · exact (x.property.1 hz.symm).elim
        · exact (x.property.2 hz.symm).elim

/-- Real stream values on the actual physical incident faces have attained extrema.
The infimum/supremum segment is exactly the segment between those minimum/maximum values. -/
theorem physical_incident_values_extrema {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ) (x : {v : V // v ≠ alpha ∧ v ≠ beta}) :
    (incidentValues A.embedding.drawing psi x.val).Finite ∧
    (incidentValues A.embedding.drawing psi x.val).Nonempty ∧
    ∃ F G : A.embedding.Face,
      incident A.embedding.drawing x.val F ∧ incident A.embedding.drawing x.val G ∧
      IsLeast (incidentValues A.embedding.drawing psi x.val) (psi F) ∧
      IsGreatest (incidentValues A.embedding.drawing psi x.val) (psi G) ∧
      sInf (incidentValues A.embedding.drawing psi x.val)=psi F ∧
      sSup (incidentValues A.embedding.drawing psi x.val)=psi G ∧
      vertexSegment (Source.voltage J alpha beta hc) x.val
        (sInf (incidentValues A.embedding.drawing psi x.val))
        (sSup (incidentValues A.embedding.drawing psi x.val)) =
      {Source.voltage J alpha beta hc x.val} ×ˢ Set.Icc (psi F) (psi G) := by
  obtain ⟨hne,hfinite,_,_⟩ := physical_original_face_star J D hc alpha beta A x
  have hvfinite : (incidentValues A.embedding.drawing psi x.val).Finite := hfinite.image psi
  have hvne : (incidentValues A.embedding.drawing psi x.val).Nonempty := hne.image psi
  obtain ⟨F,hF,hmin⟩ := Set.exists_min_image _ psi hfinite hne
  obtain ⟨G,hG,hmax⟩ := Set.exists_max_image _ psi hfinite hne
  have hlo : IsLeast (incidentValues A.embedding.drawing psi x.val) (psi F) := by
    refine ⟨⟨F,hF,rfl⟩,?_⟩
    rintro y ⟨H,hH,rfl⟩
    exact hmin H hH
  have hhi : IsGreatest (incidentValues A.embedding.drawing psi x.val) (psi G) := by
    refine ⟨⟨G,hG,rfl⟩,?_⟩
    rintro y ⟨H,hH,rfl⟩
    exact hmax H hH
  refine ⟨hvfinite,hvne,F,G,hF,hG,hlo,hhi,hlo.csInf_eq,hhi.csSup_eq,?_⟩
  rw [hlo.csInf_eq,hhi.csSup_eq]
  rfl

/-- The exact degree-four physical range, with all finite-star prerequisites discharged. -/
theorem physical_vertex_range {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (x : {v : V // v ≠ alpha ∧ v ≠ beta})
    (hdeg : Geometry.degree J.left J.right x.val ≤ 4) :
    let hx := Plane.incidenceDarts_nonempty J.left J.right alpha beta hne hc x.val
    sSup (incidentValues A.embedding.drawing psi x.val)-
      sInf (incidentValues A.embedding.drawing psi x.val) ≤
      4*Plane.largestCurrent J.left J.right (Source.voltage J alpha beta hc) x.val hx := by
  intro hx
  obtain ⟨hface,hfinite,_,hstar⟩ := physical_original_face_star J D hc alpha beta A x
  apply PhysicalVertexRange13.internal_physical_span_le_four_largest J D alpha beta A
    (Source.voltage J alpha beta hc) psi hpsi x.val hx hdeg
  · intro e
    exact (PhysicalTiling.physical_edgeFaces_eq J D hc alpha beta hne A (.inl e)).trans
      (Set.pair_comm _ _)
  · exact hfinite
  · exact hface
  · exact hstar

/-- The genuine unique physical stream satisfies the exact degree-four range. -/
theorem physical_unique_stream_range {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (x : {v : V // v ≠ alpha ∧ v ≠ beta})
    (hdeg : Geometry.degree J.left J.right x.val ≤ 4) :
    let hx := Plane.incidenceDarts_nonempty J.left J.right alpha beta hne hc x.val
    ∃! psi : A.embedding.Face → ℝ,
      Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi ∧
      sSup (incidentValues A.embedding.drawing psi x.val)-
        sInf (incidentValues A.embedding.drawing psi x.val) ≤
        4*Plane.largestCurrent J.left J.right (Source.voltage J alpha beta hc) x.val hx := by
  intro hx
  obtain ⟨psi,hpsi,huniq⟩ := (PhysicalTiling.physical_stream_tiling J D hc alpha beta hne A).1
  refine ⟨psi,⟨hpsi,physical_vertex_range J D hc alpha beta hne A psi hpsi x hdeg⟩,?_⟩
  intro psi' hpsi'
  exact huniq psi' hpsi'.1

end
end FiniteAvalanches.Electrical.PhysicalFaceStar14

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,_) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[`propext,`Classical.choice,`Quot.sound,
            `FiniteAvalanches.External.plane_vertex_face_star,
            `FiniteAvalanches.External.bsst_square_tiling].contains ax do
          throwError "UNEXPECTED_CLOSURE {name}: {ax}"
      logInfo m!"ALL_OWNED_CLOSURE {name}: {axs.toList}"
      count := count+1
  logInfo m!"FACE_STAR14_ALL_OWNED_CLOSURES={count}"
