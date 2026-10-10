import FiniteAvalanches.Electrical.Geometry.ConnectedDrawingQuotient
import FiniteAvalanches.Electrical.Geometry.BSST
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered

/-! The actual complementary face traversed by a deleted copied arc. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.DeletedArc
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.DrawingContraction
open scoped Classical
noncomputable section

variable {V E F : Type} [Fintype V] [Fintype E] [Fintype F]
  {J : CopiedGraph V E} {K : CopiedGraph V F}

/-- The open interior of an omitted original copy avoids the restricted trace. -/
theorem omitted_interior_off_trace (D : Drawing J) (i : F → E)
    (hi : Function.Injective i) (hl : ∀ f, J.left (i f) = K.left f)
    (hr : ∀ f, J.right (i f) = K.right f) (e : E) (he : ∀ f, i f ≠ e)
    (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    D.curve e t ∉ drawingTrace (restrictDrawing D i hi hl hr) := by
  rintro (⟨v, hv⟩ | h)
  · exact D.avoids e t ht0 ht1 v hv.symm
  · obtain ⟨f, s, hs⟩ := Set.mem_iUnion.mp h
    have hb := (D.intersects e (i f) (Ne.symm (he f)) t s hs.symm).1
    exact hb.elim (ne_of_gt ht0) (ne_of_lt ht1)

/-- Each endpoint of a genuine parameter subinterval is approached by its
open parameter interval, including at zero and one of the original arc. -/
theorem parameter_interval_closure (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a < b) (t : ArcParameter) (hta : a ≤ t.val) (htb : t.val ≤ b) :
    t ∈ closure {s : ArcParameter | a < s.val ∧ s.val < b} := by
  have himage : Subtype.val '' {s : ArcParameter | a < s.val ∧ s.val < b} =
      Set.Ioo a b := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hx
      exact ⟨⟨x, ha.trans hx.1.le, hx.2.le.trans hb⟩, hx, rfl⟩
  rw [closure_subtype, himage, closure_Ioo hab.ne]
  exact ⟨hta, htb⟩

/-- The actual parametrized approach germs retain the two endpoint occurrences. -/
theorem endpoint_germs (gamma : ArcParameter → Plane) (hc : Continuous gamma)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    gamma ⟨0, by constructor <;> norm_num⟩ ∈
      closure (gamma '' {t : ArcParameter | 0 < t.val ∧ t.val < epsilon}) ∧
    gamma ⟨1, by constructor <;> norm_num⟩ ∈
      closure (gamma '' {t : ArcParameter | 1 - epsilon < t.val ∧ t.val < 1}) := by
  constructor
  · exact mem_closure_image hc.continuousAt
      (parameter_interval_closure 0 epsilon le_rfl he1.le he0
        ⟨0, by constructor <;> norm_num⟩ le_rfl he0.le)
  · exact mem_closure_image hc.continuousAt
      (parameter_interval_closure (1 - epsilon) 1 (by linarith) le_rfl
        (by linarith) ⟨1, by constructor <;> norm_num⟩ (by linarith) le_rfl)

/-- A continuous open arc in the complement lies in one actual face, and its
closed arc lies in that face's closure. The face is uniquely determined. -/
theorem common_face (D : Drawing K) (gamma : ArcParameter → Plane)
    (hc : Continuous gamma)
    (hoff : ∀ t : ArcParameter, 0 < t.val → t.val < 1 →
      gamma t ∉ drawingTrace D) :
    ∃ face : Face D,
      (∀ t : ArcParameter, 0 < t.val → t.val < 1 → gamma t ∈ faceRegion D face) ∧
      Set.range gamma ⊆ closure (faceRegion D face) ∧
      (∀ face' : Face D,
        (∀ t : ArcParameter, 0 < t.val → t.val < 1 → gamma t ∈ faceRegion D face') →
        face' = face) := by
  let f (t : Set.Ioo (0 : ℝ) 1) : {z : Plane // z ∉ drawingTrace D} :=
    ⟨gamma ⟨t.val, t.property.1.le, t.property.2.le⟩,
      hoff _ t.property.1 t.property.2⟩
  have hf : Continuous f :=
    (hc.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  let mid : Set.Ioo (0 : ℝ) 1 := ⟨1/2, by constructor <;> norm_num⟩
  let face : Face D := ConnectedComponents.mk (f mid)
  letI : PreconnectedSpace (Set.Ioo (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hconn : IsPreconnected (Set.range f) := isPreconnected_range hf
  have hface (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
      gamma t ∈ faceRegion D face := by
    let s : Set.Ioo (0 : ℝ) 1 := ⟨t.val, ht0, ht1⟩
    refine ⟨hoff t ht0 ht1, ?_⟩
    exact ConnectedComponents.coe_eq_coe'.mpr
      (hconn.subset_connectedComponent (Set.mem_range_self mid) (Set.mem_range_self s))
  let interior : Set ArcParameter := {t | 0 < t.val ∧ t.val < 1}
  have himage : Subtype.val '' interior = Set.Ioo (0 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro ht
      exact ⟨⟨t, ht.1.le, ht.2.le⟩, ht, rfl⟩
  have hdense (t : ArcParameter) : t ∈ closure interior := by
    rw [closure_subtype, himage, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact t.property
  refine ⟨face, hface, ?_, ?_⟩
  · rintro z ⟨t, rfl⟩
    exact map_mem_closure hc (hdense t) (fun s hs => hface s hs.1 hs.2)
  · intro face' hface'
    obtain ⟨hz, he⟩ := hface' ⟨1/2, by constructor <;> norm_num⟩
      (by norm_num) (by norm_num)
    exact he.symm

end
end FiniteAvalanches.Electrical.DeletedArc
