import FiniteAvalanches.External.BSST

set_option autoImplicit false

open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open scoped Classical

/-! Physical chart adapter, face stream, and square tiling on the actual source carriers
`Source.PlaneEmbedding` and `Source.OuterArc`, derived from the registered classical BSST input. -/

namespace FiniteAvalanches.Electrical.PhysicalTiling

/-- The left face of an oriented edge chart is the chart's positive-side complement face. -/
theorem leftFace_eq_positiveChartFace {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (D : Source.PlaneEmbedding J) (e : E) :
    D.leftFace e = positiveChartFace D.drawing e (D.edgeChart e) := rfl

/-- The right face of an oriented edge chart is the chart's negative-side complement face. -/
theorem rightFace_eq_negativeChartFace {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (D : Source.PlaneEmbedding J) (e : E) :
    D.rightFace e = negativeChartFace D.drawing e (D.edgeChart e) := rfl

/-- Chart-compatible face labels agree with the actual physical sides of the edge chart. -/
theorem chart_sides_of_compatible {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (D : Source.PlaneEmbedding J) (face0 face1 : E → Face D.drawing)
    (hcharts : ∀ e (c : Source.EdgeChart D.drawing e),
      negativeChartFace D.drawing e c = face0 e ∧ positiveChartFace D.drawing e c = face1 e)
    (e : E) :
    D.rightFace e = face0 e ∧ D.leftFace e = face1 e :=
  ⟨(rightFace_eq_negativeChartFace D e).trans (hcharts e (D.edgeChart e)).1,
   (leftFace_eq_positiveChartFace D e).trans (hcharts e (D.edgeChart e)).2⟩

/-- The classical BSST face labels on the actual outer arc are the physical chart sides. -/
theorem physical_face_data {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta) :
    ∃ face0 face1 : E ⊕ Unit → Face A.embedding.drawing,
      (∀ z, A.embedding.rightFace z = face0 z ∧ A.embedding.leftFace z = face1 z) ∧
      ∀ z, edgeFaces A.embedding.drawing z = {face0 z, face1 z} := by
  obtain ⟨_, hA⟩ := FiniteAvalanches.External.bsst_square_tiling J D.drawing hc alpha beta hne
    A.face A.alpha_incident A.beta_incident A.unbounded
  obtain ⟨f0, f1, hfaces, hcharts, _⟩ := hA (auxiliaryArcOfOuterArc D alpha beta A)
  exact ⟨f0, f1, fun z => chart_sides_of_compatible A.embedding f0 f1 hcharts z, hfaces⟩

/-- The faces whose closure contains a whole arc are exactly its two physical chart sides. -/
theorem physical_edgeFaces_eq {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (z : E ⊕ Unit) :
    edgeFaces A.embedding.drawing z = {A.embedding.rightFace z, A.embedding.leftFace z} := by
  obtain ⟨f0, f1, hch, hfaces⟩ := physical_face_data J D hc alpha beta hne A
  rw [(hch z).1, (hch z).2]
  exact hfaces z

/-- Both physical side faces of every original copy are incident to both endpoints. -/
theorem physical_side_faces_incident {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta) (e : E) :
    A.embedding.incident (J.left e) (A.embedding.leftFace (.inl e)) ∧
    A.embedding.incident (J.right e) (A.embedding.leftFace (.inl e)) ∧
    A.embedding.incident (J.left e) (A.embedding.rightFace (.inl e)) ∧
    A.embedding.incident (J.right e) (A.embedding.rightFace (.inl e)) := by
  have hr : A.embedding.rightFace (.inl e) ∈ edgeFaces A.embedding.drawing (.inl e) := by
    rw [physical_edgeFaces_eq J D hc alpha beta hne A (.inl e)]
    exact Set.mem_insert _ _
  have hl : A.embedding.leftFace (.inl e) ∈ edgeFaces A.embedding.drawing (.inl e) := by
    rw [physical_edgeFaces_eq J D hc alpha beta hne A (.inl e)]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have h0 := edgeFaces_endpoints A.embedding.drawing (.inl e) _ hr
  have h1 := edgeFaces_endpoints A.embedding.drawing (.inl e) _ hl
  exact ⟨(charted_incident_eq A.embedding (J.left e) (A.embedding.leftFace (.inl e))).mp h1.1,
    (charted_incident_eq A.embedding (J.right e) (A.embedding.leftFace (.inl e))).mp h1.2,
    (charted_incident_eq A.embedding (J.left e) (A.embedding.rightFace (.inl e))).mp h0.1,
    (charted_incident_eq A.embedding (J.right e) (A.embedding.rightFace (.inl e))).mp h0.2⟩

/-- With physical side labels, the source edge square is the literal BSST copied square. -/
theorem edgeSquare_eq_copiedSquare_of_faces {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J) (alpha beta : V)
    (A : Source.OuterArc D alpha beta) (f0 f1 : E ⊕ Unit → Face A.embedding.drawing)
    (hf0 : ∀ z, A.embedding.rightFace z = f0 z) (hf1 : ∀ z, A.embedding.leftFace z = f1 z)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (e : E) :
    Source.edgeSquare D alpha beta A phi psi e =
      copiedSquare J phi psi (fun e => f0 (.inl e)) (fun e => f1 (.inl e)) e := by
  have h0 : A.embedding.rightFace (.inl e) = f0 (.inl e) := hf0 (.inl e)
  have h1 : A.embedding.leftFace (.inl e) = f1 (.inl e) := hf1 (.inl e)
  change Set.Icc (min (phi (J.left e)) (phi (J.right e))) (max (phi (J.left e)) (phi (J.right e))) ×ˢ
      Set.Icc (min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))))
        (max (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e)))) =
    Set.Icc (min (phi (J.left e)) (phi (J.right e))) (max (phi (J.left e)) (phi (J.right e))) ×ˢ
      Set.Icc (min (psi (f0 (.inl e))) (psi (f1 (.inl e))))
        (max (psi (f0 (.inl e))) (psi (f1 (.inl e))))
  rw [← h0, ← h1,
    min_comm (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))),
    max_comm (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e)))]

/-- Unique physical face stream, physical bounds, disjoint original edge squares, and full
rectangle coverage, from the registered classical BSST input. -/
theorem physical_stream_tiling {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta) :
    (∃! psi : A.embedding.Face → ℝ,
        Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi) ∧
    ∀ psi : A.embedding.Face → ℝ,
      Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi →
      (∀ F : A.embedding.Face,
        0 ≤ psi F ∧ psi F ≤ Source.mass J (Source.voltage J alpha beta hc)) ∧
      (∀ e f : E, e ≠ f → Disjoint
        (interior (Source.edgeSquare D alpha beta A (Source.voltage J alpha beta hc) psi e))
        (interior (Source.edgeSquare D alpha beta A (Source.voltage J alpha beta hc) psi f))) ∧
      (⋃ e : E, Source.edgeSquare D alpha beta A (Source.voltage J alpha beta hc) psi e) =
        Set.Icc 0 1 ×ˢ Set.Icc 0 (Source.mass J (Source.voltage J alpha beta hc)) := by
  obtain ⟨_, hA⟩ := FiniteAvalanches.External.bsst_square_tiling J D.drawing hc alpha beta hne
    A.face A.alpha_incident A.beta_incident A.unbounded
  obtain ⟨f0, f1, _, hcharts, hex, hgeom⟩ := hA (auxiliaryArcOfOuterArc D alpha beta A)
  have hf0 : ∀ z : E ⊕ Unit, A.embedding.rightFace z = f0 z :=
    fun z => (chart_sides_of_compatible A.embedding f0 f1 hcharts z).1
  have hf1 : ∀ z : E ⊕ Unit, A.embedding.leftFace z = f1 z :=
    fun z => (chart_sides_of_compatible A.embedding f0 f1 hcharts z).2
  have hiff : ∀ psi : A.embedding.Face → ℝ,
      Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi ↔
        ((∀ e : E, psi (f1 (.inl e)) - psi (f0 (.inl e)) =
            Source.voltage J alpha beta hc (J.left e) - Source.voltage J alpha beta hc (J.right e)) ∧
          psi (f0 (.inr ())) = 0 ∧
          psi (f1 (.inr ())) = Source.mass J (Source.voltage J alpha beta hc)) :=
    fun psi => source_stream_spec_iff J D alpha beta A f0 f1 psi
      (Source.voltage J alpha beta hc) hcharts
  obtain ⟨psi0, hpsi0, huniq⟩ := hex
  refine ⟨⟨psi0, (hiff psi0).mpr hpsi0, ?_⟩, ?_⟩
  · intro psi hpsi
    exact huniq psi ((hiff psi).mp hpsi)
  · intro psi hpsi
    obtain ⟨hbound, hdis, hcover⟩ := hgeom psi ((hiff psi).mp hpsi)
    have hsq : ∀ e : E,
        Source.edgeSquare D alpha beta A (Source.voltage J alpha beta hc) psi e =
          copiedSquare J (Source.voltage J alpha beta hc) psi
            (fun e => f0 (.inl e)) (fun e => f1 (.inl e)) e :=
      fun e => edgeSquare_eq_copiedSquare_of_faces J D alpha beta A f0 f1 hf0 hf1
        (Source.voltage J alpha beta hc) psi e
    refine ⟨hbound, ?_, ?_⟩
    · intro e f hef
      rw [hsq e, hsq f]
      exact hdis e f hef
    · have hfun : (fun e : E =>
          Source.edgeSquare D alpha beta A (Source.voltage J alpha beta hc) psi e) =
          fun e : E => copiedSquare J (Source.voltage J alpha beta hc) psi
            (fun e => f0 (.inl e)) (fun e => f1 (.inl e)) e := funext hsq
      exact (congrArg Set.iUnion hfun).trans hcover

/-- Every original edge square lies in the tiled rectangle, zero-current points included. -/
theorem physical_edgeSquare_subset_rectangle {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi) (e : E) :
    Source.edgeSquare D alpha beta A (Source.voltage J alpha beta hc) psi e ⊆
      Set.Icc 0 1 ×ˢ Set.Icc 0 (Source.mass J (Source.voltage J alpha beta hc)) := by
  obtain ⟨-, -, hcover⟩ := (physical_stream_tiling J D hc alpha beta hne A).2 psi hpsi
  intro p hp
  have hmem : p ∈ ⋃ e : E,
      Source.edgeSquare D alpha beta A (Source.voltage J alpha beta hc) psi e :=
    Set.mem_iUnion.mpr ⟨e, hp⟩
  rw [hcover] at hmem
  exact hmem

private theorem abs_sub_le_one_of_min_max {a b : ℝ} (h0 : 0 ≤ min a b) (h1 : max a b ≤ 1) :
    |a - b| ≤ 1 := by
  have h2 : min a b ≤ a := min_le_left a b
  have h3 : min a b ≤ b := min_le_right a b
  have h4 : a ≤ max a b := le_max_left a b
  have h5 : b ≤ max a b := le_max_right a b
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem abs_le_min_one_of_square_subset {a b ya yb M : ℝ}
    (hsub : Set.Icc (min a b) (max a b) ×ˢ Set.Icc (min ya yb) (max ya yb) ⊆
      Set.Icc 0 1 ×ˢ Set.Icc 0 M)
    (hcur : ya - yb = a - b) (hya : 0 ≤ ya ∧ ya ≤ M) (hyb : 0 ≤ yb ∧ yb ≤ M) :
    |a - b| ≤ min 1 M := by
  have hmin : (min a b, min ya yb) ∈
      Set.Icc (min a b) (max a b) ×ˢ Set.Icc (min ya yb) (max ya yb) :=
    Set.mem_prod.mpr
      ⟨Set.mem_Icc.mpr ⟨le_rfl, (min_le_left a b).trans (le_max_left a b)⟩,
       Set.mem_Icc.mpr ⟨le_rfl, (min_le_left ya yb).trans (le_max_left ya yb)⟩⟩
  have hmax : (max a b, min ya yb) ∈
      Set.Icc (min a b) (max a b) ×ˢ Set.Icc (min ya yb) (max ya yb) :=
    Set.mem_prod.mpr
      ⟨Set.mem_Icc.mpr ⟨(min_le_left a b).trans (le_max_left a b), le_rfl⟩,
       Set.mem_Icc.mpr ⟨le_rfl, (min_le_left ya yb).trans (le_max_left ya yb)⟩⟩
  have h0 : 0 ≤ min a b := (Set.mem_Icc.mp (Set.mem_prod.mp (hsub hmin)).1).1
  have h1 : max a b ≤ 1 := (Set.mem_Icc.mp (Set.mem_prod.mp (hsub hmax)).1).2
  refine le_min (abs_sub_le_one_of_min_max h0 h1) ?_
  exact abs_le.mpr ⟨by linarith [hya.1, hya.2, hyb.1, hyb.2, hcur],
    by linarith [hya.1, hya.2, hyb.1, hyb.2, hcur]⟩

/-- Downstream use of the tiling: every edge current is at most `θ = min 1 M`. -/
theorem physical_edge_current_le_theta {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta) (e : E) :
    |Source.voltage J alpha beta hc (J.left e) - Source.voltage J alpha beta hc (J.right e)| ≤
      min 1 (Source.mass J (Source.voltage J alpha beta hc)) := by
  obtain ⟨⟨psi, hpsi, -⟩, hall⟩ := physical_stream_tiling J D hc alpha beta hne A
  obtain ⟨hbd, -, -⟩ := hall psi hpsi
  have hcur : psi (A.embedding.leftFace (.inl e)) - psi (A.embedding.rightFace (.inl e)) =
      Source.voltage J alpha beta hc (J.left e) - Source.voltage J alpha beta hc (J.right e) :=
    hpsi.1 e
  exact abs_le_min_one_of_square_subset
    (a := Source.voltage J alpha beta hc (J.left e))
    (b := Source.voltage J alpha beta hc (J.right e))
    (ya := psi (A.embedding.leftFace (.inl e)))
    (yb := psi (A.embedding.rightFace (.inl e)))
    (M := Source.mass J (Source.voltage J alpha beta hc))
    (physical_edgeSquare_subset_rectangle J D hc alpha beta hne A psi hpsi e) hcur
    (hbd _) (hbd _)

/-- Membership in the set of stream values at faces incident to a vertex. -/
theorem mem_incidentValues {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
    (D : Drawing J) (psi : Face D → ℝ) (x : V) (y : ℝ) :
    y ∈ incidentValues D psi x ↔ ∃ F : Face D, BSST.incident D x F ∧ psi F = y := Iff.rfl

private theorem mem_Icc_sInf_sSup {S : Set ℝ} (hbb : BddBelow S) (hba : BddAbove S)
    {a b c : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hcm : min a b ≤ c ∧ c ≤ max a b) :
    sInf S ≤ c ∧ c ≤ sSup S :=
  ⟨(le_min (csInf_le hbb ha) (csInf_le hbb hb)).trans hcm.1,
   hcm.2.trans (max_le (le_csSup hba ha) (le_csSup hba hb))⟩

/-- Every square side or point at `φ x` of an edge at `x` lies in the vertical segment spanned
by the stream values of the physical faces incident to `x`. This is containment only; the range
bound is not asserted. -/
theorem physical_square_side_mem_incident_segment {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (x : V) (e : E) (hx : J.left e = x ∨ J.right e = x) (p : ℝ × ℝ)
    (hp : p ∈ Source.edgeSquare D alpha beta A (Source.voltage J alpha beta hc) psi e)
    (hpx : p.1 = Source.voltage J alpha beta hc x) :
    p ∈ BSST.vertexSegment (Source.voltage J alpha beta hc) x
      (sInf (incidentValues A.embedding.drawing psi x))
      (sSup (incidentValues A.embedding.drawing psi x)) := by
  obtain ⟨hbd, -, -⟩ := (physical_stream_tiling J D hc alpha beta hne A).2 psi hpsi
  obtain ⟨hl0, hl1, hr0, hr1⟩ := physical_side_faces_incident J D hc alpha beta hne A e
  have hL : A.embedding.incident x (A.embedding.leftFace (.inl e)) := by
    rcases hx with h | h
    · subst h
      exact hl0
    · subst h
      exact hl1
  have hR : A.embedding.incident x (A.embedding.rightFace (.inl e)) := by
    rcases hx with h | h
    · subst h
      exact hr0
    · subst h
      exact hr1
  have hmemL : psi (A.embedding.leftFace (.inl e)) ∈ incidentValues A.embedding.drawing psi x :=
    (mem_incidentValues A.embedding.drawing psi x _).mpr
      ⟨_, (charted_incident_eq A.embedding x (A.embedding.leftFace (.inl e))).mpr hL, rfl⟩
  have hmemR : psi (A.embedding.rightFace (.inl e)) ∈ incidentValues A.embedding.drawing psi x :=
    (mem_incidentValues A.embedding.drawing psi x _).mpr
      ⟨_, (charted_incident_eq A.embedding x (A.embedding.rightFace (.inl e))).mpr hR, rfl⟩
  have hbb : BddBelow (incidentValues A.embedding.drawing psi x) := by
    refine ⟨0, fun y hy => ?_⟩
    obtain ⟨F, -, rfl⟩ := (mem_incidentValues A.embedding.drawing psi x y).mp hy
    exact (hbd F).1
  have hba : BddAbove (incidentValues A.embedding.drawing psi x) := by
    refine ⟨Source.mass J (Source.voltage J alpha beta hc), fun y hy => ?_⟩
    obtain ⟨F, -, rfl⟩ := (mem_incidentValues A.embedding.drawing psi x y).mp hy
    exact (hbd F).2
  have hp2 : min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))) ≤
        p.2 ∧
      p.2 ≤ max (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))) := by
    simp only [Source.edgeSquare, Set.mem_prod, Set.mem_Icc] at hp
    exact hp.2
  have hseg := mem_Icc_sInf_sSup hbb hba hmemL hmemR hp2
  simp only [BSST.vertexSegment, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc]
  exact ⟨hpx, hseg⟩

/-- A copy whose endpoints have equal voltage has equal stream values on its two sides,
so its square is the single point. -/
theorem physical_zero_current_square {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J) (alpha beta : V)
    (A : Source.OuterArc D alpha beta) (phi : V → ℝ) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A phi psi) (e : E)
    (hz : phi (J.left e) = phi (J.right e)) :
    Source.edgeSquare D alpha beta A phi psi e =
      {(phi (J.left e), psi (A.embedding.rightFace (.inl e)))} := by
  have hcur : psi (A.embedding.leftFace (.inl e)) - psi (A.embedding.rightFace (.inl e)) =
      phi (J.left e) - phi (J.right e) := hpsi.1 e
  have h0 : psi (A.embedding.leftFace (.inl e)) - psi (A.embedding.rightFace (.inl e)) = 0 := by
    rw [hcur, hz, sub_self]
  have hψ : psi (A.embedding.leftFace (.inl e)) = psi (A.embedding.rightFace (.inl e)) :=
    sub_eq_zero.mp h0
  simp only [Source.edgeSquare, hz, hψ, min_self, max_self, Set.Icc_self,
    Set.singleton_prod_singleton]

/-- The point of a zero-current copy lies in the incident-face segment of both endpoints. -/
theorem physical_zero_current_point_mem_segments {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi) (e : E)
    (hz : Source.voltage J alpha beta hc (J.left e) = Source.voltage J alpha beta hc (J.right e)) :
    (Source.voltage J alpha beta hc (J.left e), psi (A.embedding.rightFace (.inl e))) ∈
      BSST.vertexSegment (Source.voltage J alpha beta hc) (J.left e)
        (sInf (incidentValues A.embedding.drawing psi (J.left e)))
        (sSup (incidentValues A.embedding.drawing psi (J.left e))) ∧
    (Source.voltage J alpha beta hc (J.left e), psi (A.embedding.rightFace (.inl e))) ∈
      BSST.vertexSegment (Source.voltage J alpha beta hc) (J.right e)
        (sInf (incidentValues A.embedding.drawing psi (J.right e)))
        (sSup (incidentValues A.embedding.drawing psi (J.right e))) := by
  have hmem : (Source.voltage J alpha beta hc (J.left e),
      psi (A.embedding.rightFace (.inl e))) ∈
      Source.edgeSquare D alpha beta A (Source.voltage J alpha beta hc) psi e := by
    rw [physical_zero_current_square J D alpha beta A (Source.voltage J alpha beta hc) psi hpsi e hz]
    exact Set.mem_singleton _
  exact ⟨physical_square_side_mem_incident_segment J D hc alpha beta hne A psi hpsi
      (J.left e) e (Or.inl rfl) _ hmem rfl,
    physical_square_side_mem_incident_segment J D hc alpha beta hne A psi hpsi
      (J.right e) e (Or.inr rfl) _ hmem hz⟩

end FiniteAvalanches.Electrical.PhysicalTiling

#print axioms FiniteAvalanches.Electrical.PhysicalTiling.leftFace_eq_positiveChartFace
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.rightFace_eq_negativeChartFace
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.chart_sides_of_compatible
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.physical_face_data
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.physical_edgeFaces_eq
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.physical_side_faces_incident
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.edgeSquare_eq_copiedSquare_of_faces
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.physical_stream_tiling
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.physical_edgeSquare_subset_rectangle
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.physical_edge_current_le_theta
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.mem_incidentValues
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.physical_square_side_mem_incident_segment
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.physical_zero_current_square
#print axioms FiniteAvalanches.Electrical.PhysicalTiling.physical_zero_current_point_mem_segments
