import FiniteAvalanches.Electrical.Geometry.SourceVoltage
import FiniteAvalanches.Electrical.Geometry.DrawingProperness
import Lean

/-! Uncharted proper drawings, their literal complement faces, and original-copy coordinates. -/
namespace FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source (Plane drawingTrace augmentedGraph voltage mass)
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Actual connected components of the complement of the full original drawn trace. -/
abbrev Face (D : Drawing J) := ConnectedComponents {z : Plane // z ∉ drawingTrace D}

/-- The actual plane region represented by a complement component. -/
def faceRegion (D : Drawing J) (F : Face D) : Set Plane :=
  {z | ∃ hz : z ∉ drawingTrace D,
    ConnectedComponents.mk (⟨z,hz⟩ : {w // w ∉ drawingTrace D}) = F}

/-- Literal geometric vertex incidence, including repeated visits of the same face. -/
def incident (D : Drawing J) (x : V) (F : Face D) : Prop :=
  D.point x ∈ closure (faceRegion D F)

/-- Actual faces whose closed boundary contains the whole original copied edge arc. -/
def edgeFaces (D : Drawing J) (e : E) : Set (Face D) :=
  {F | Set.range (D.curve e) ⊆ closure (faceRegion D F)}

/-- A genuine auxiliary arc in the chosen face, retaining every original point and curve. -/
structure AuxiliaryArc (D : Drawing J) (F : Face D) (alpha beta : V) where
  drawing : Drawing (augmentedGraph J alpha beta)
  point_eq : drawing.point = D.point
  curve_eq : ∀ e, drawing.curve (.inl e) = D.curve e
  interior_in_face : ∀ t : ArcParameter, 0 < t.val → t.val < 1 →
    drawing.curve (.inr ()) t ∈ faceRegion D F

/-- The source zero/one-voltage interval crossed with the actual dual-face voltage interval. -/
def copiedSquare (J : CopiedGraph V E) (phi : V → ℝ)
    {W : Type} (psi : W → ℝ) (face0 face1 : E → W) (e : E) : Set Plane :=
  Set.Icc (min (phi (J.left e)) (phi (J.right e)))
    (max (phi (J.left e)) (phi (J.right e))) ×ˢ
  Set.Icc (min (psi (face0 e)) (psi (face1 e)))
    (max (psi (face0 e)) (psi (face1 e)))

/-- The literal positive-Laplacian Dirichlet characterization on the polar dual.
The dual retains the original E; the added arc determines its two boundary faces only. -/
def dualVoltageSpec {W : Type} (face0 face1 : E → W) (pole0 pole1 : W)
    (M : ℝ) (psi : W → ℝ) : Prop :=
  psi pole0 = 0 ∧ psi pole1 = M ∧
    ∀ F, F ≠ pole0 → F ≠ pole1 → laplacian face0 face1 psi F = 0

/-- All actual incident-face voltages, without a finite orbit or default extremum. -/
def incidentValues (D : Drawing J) (psi : Face D → ℝ) (x : V) : Set ℝ :=
  {y | ∃ F, incident D x F ∧ psi F = y}

/-- The source vertical segment with explicitly attained lower and upper face values. -/
def vertexSegment (phi : V → ℝ) (x : V) (lo hi : ℝ) : Set Plane :=
  {phi x} ×ˢ Set.Icc lo hi

/-- Whole-arc face incidence includes each prescribed endpoint, without charts. -/
theorem edgeFaces_endpoints (D : Drawing J) (e : E) (F : Face D)
    (hF : F ∈ edgeFaces D e) :
    incident D (J.left e) F ∧ incident D (J.right e) F := by
  constructor
  · exact hF ⟨⟨0,by constructor <;> norm_num⟩,D.start e⟩
  · exact hF ⟨⟨1,by constructor <;> norm_num⟩,D.finish e⟩

/-- Erasing chart witnesses changes neither the actual complement nor vertex incidence. -/
theorem charted_incident_eq (D : Source.PlaneEmbedding J) (x : V) (F : D.Face) :
    incident D.drawing x F ↔ D.incident x F := Iff.rfl

/-- An existing physical outer arc supplies the uncharted auxiliary-arc data. -/
def auxiliaryArcOfOuterArc (D : Source.PlaneEmbedding J) (alpha beta : V)
    (A : Source.OuterArc D alpha beta) : AuxiliaryArc D.drawing A.face alpha beta where
  drawing := A.embedding.drawing
  point_eq := A.point_eq
  curve_eq := A.curve_eq
  interior_in_face := A.interior_in_face

/-- The actual augmented trace adds precisely one curve to the full original trace. -/
theorem auxiliary_trace (D : Drawing J) (F : Face D) (alpha beta : V)
    (A : AuxiliaryArc D F alpha beta) :
    drawingTrace A.drawing = drawingTrace D ∪ Set.range (A.drawing.curve (.inr ())) := by
  ext z
  simp only [drawingTrace,Set.mem_union,Set.mem_range,Set.mem_iUnion]
  constructor
  · rintro (⟨x,hx⟩ | ⟨e,t,ht⟩)
    · exact Or.inl (Or.inl ⟨x,by simpa only [A.point_eq] using hx⟩)
    · cases e with
      | inl e => exact Or.inl (Or.inr ⟨e,t,by simpa only [A.curve_eq] using ht⟩)
      | inr e => cases e; exact Or.inr ⟨t,ht⟩
  · rintro ((⟨x,hx⟩ | ⟨e,t,ht⟩) | ⟨t,ht⟩)
    · exact Or.inl ⟨x,by simpa only [A.point_eq] using hx⟩
    · exact Or.inr ⟨.inl e,t,by simpa only [A.curve_eq] using ht⟩
    · exact Or.inr ⟨.inr (),t,ht⟩

omit [Fintype V] [Fintype E] in
/-- A zero-current original copy becomes its actual common voltage/dual-voltage point. -/
theorem zero_current_square {W : Type} (J : CopiedGraph V E) (phi : V → ℝ)
    (psi : W → ℝ) (face0 face1 : E → W) (e : E)
    (hp : phi (J.left e) = phi (J.right e))
    (hdual : |psi (face0 e)-psi (face1 e)| = |phi (J.left e)-phi (J.right e)|) :
    copiedSquare J phi psi face0 face1 e = {(phi (J.left e),psi (face0 e))} := by
  have hpsi : psi (face0 e) = psi (face1 e) := by
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    simpa only [hp,sub_self,abs_zero] using hdual
  simp only [copiedSquare,hp,hpsi,min_self,max_self,Set.Icc_self,
    Set.singleton_prod_singleton]


/-- A chart's positive side point really belongs to the geometric complement. -/
theorem positive_chart_point_off_trace (D : Drawing J) (e : E)
    (c : Source.EdgeChart D e) :
    c.chart.map.symm (1/2,c.radius/2) ∉ drawingTrace D := by
  have h0 : |(1/2 : ℝ)-1/2| < c.radius := by simpa using c.radius_pos
  have hp : |c.radius/2| < c.radius := by
    rw [abs_of_pos (by linarith [c.radius_pos])]
    linarith [c.radius_pos]
  exact fun h => (by linarith [c.radius_pos] : c.radius/2 ≠ 0)
    ((c.trace_box _ h0 hp).mp h)

/-- A chart's negative side point really belongs to the geometric complement. -/
theorem negative_chart_point_off_trace (D : Drawing J) (e : E)
    (c : Source.EdgeChart D e) :
    c.chart.map.symm (1/2,-(c.radius/2)) ∉ drawingTrace D := by
  have h0 : |(1/2 : ℝ)-1/2| < c.radius := by simpa using c.radius_pos
  have hp : |-(c.radius/2)| < c.radius := by
    rw [abs_neg,abs_of_pos (by linarith [c.radius_pos])]
    linarith [c.radius_pos]
  exact fun h => (by linarith [c.radius_pos] : -(c.radius/2) ≠ 0)
    ((c.trace_box _ h0 hp).mp h)

/-- The actual complement component of an oriented chart's positive side point. -/
def positiveChartFace (D : Drawing J) (e : E) (c : Source.EdgeChart D e) : Face D :=
  ConnectedComponents.mk ⟨c.chart.map.symm (1/2,c.radius/2),
    positive_chart_point_off_trace D e c⟩

/-- The actual complement component of an oriented chart's negative side point. -/
def negativeChartFace (D : Drawing J) (e : E) (c : Source.EdgeChart D e) : Face D :=
  ConnectedComponents.mk ⟨c.chart.map.symm (1/2,-(c.radius/2)),
    negative_chart_point_off_trace D e c⟩

end
end FiniteAvalanches.Electrical.BSST
