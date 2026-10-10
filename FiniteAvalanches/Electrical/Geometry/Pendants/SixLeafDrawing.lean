import FiniteAvalanches.Electrical.Geometry.Pendants.FanParameters
import FiniteAvalanches.Electrical.Trees.Pendants.Reachability

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Every occurrence, including repeated original vertices, is a fresh finite Sum vertex. -/
def sixTerminals : Fin 6 → V ⊕ Fin 6 := Sum.inr

def extensionPoint (D : Drawing J) (α : Fin 6 → ℝ) (l : ℝ) : V ⊕ Fin 6 → ℝ × ℝ :=
  Sum.elim (fun v => scaledPoint (1-l) (D.point v)) (fun i => unitPoint (leafAngle α l i))

def extensionCurve (D : Drawing J) (x : Fin 6 → V) (α : Fin 6 → ℝ) (l : ℝ) :
    E ⊕ Fin 6 → ArcParameter → ℝ × ℝ :=
  Sum.elim (fun e t => scaledPoint (1-l) (D.curve e t))
    (fun i t => segment (scaledPoint (1-l) (D.point (x i))) (unitPoint (leafAngle α l i)) t.val)

theorem scaled_square (c : ℝ) (p : ℝ × ℝ) : square (scaledPoint c p)=c^2*square p :=
  scaledPoint_square c p

theorem contracted_square (l : ℝ) (hl0 : 0<l) (hl1 : l<1) : (1-l)^2<1 := by
  have h := mul_pos hl0 (sub_pos.mpr hl1)
  nlinarith only [hl0,h]

theorem explicit_old_bound (D : Drawing J) (l : ℝ)
    (hpoints : ∀ v, D.point v ∈ disk) (v : V) :
    square (scaledPoint (1-l) (D.point v)) ≤ (1-l)^2 := by
  rw [scaled_square]
  exact (mul_le_mul_of_nonneg_left (hpoints v) (sq_nonneg _)).trans_eq (mul_one _)

theorem explicit_curve_bound (D : Drawing J) (l : ℝ)
    (hcurves : ∀ e t, D.curve e t ∈ disk) (e : E) (t : ArcParameter) :
    square (scaledPoint (1-l) (D.curve e t)) ≤ (1-l)^2 := by
  rw [scaled_square]
  exact (mul_le_mul_of_nonneg_left (hcurves e t) (sq_nonneg _)).trans_eq (mul_one _)

/-- The explicit all-six construction; numerical separation inputs are proved by the existence export. -/
def explicitDrawing (D : Drawing J) (x : Fin 6 → V) (α : Fin 6 → ℝ)
    (hα : Monotone α) (hw : α 5 ≤ α 0+2*Real.pi)
    (hx : ∀ i, D.point (x i)=unitPoint (α i))
    (hpoints : ∀ v, D.point v ∈ disk) (hcurves : ∀ e t, D.curve e t ∈ disk)
    (l : ℝ) (hl0 : 0<l) (hl1 : l<1) (hlb : l*(4*Real.pi^2+1)<1)
    (hpairs : ∀ i j, unitPoint (α i) ≠ unitPoint (α j) →
      dist (scaledPoint (1-l) (unitPoint (α i))) (unitPoint (α i)) <
        dist (unitPoint (α i)) (unitPoint (α j))/3 ∧
      dist (unitPoint (leafAngle α l i)) (unitPoint (α i)) <
        dist (unitPoint (α i)) (unitPoint (α j))/3) : Drawing (J.withPendants x) where
  point := extensionPoint D α l
  point_injective := by
    have hleaf := ordered_unitPoints_injective (leafAngle α l)
      (leafAngle_strictMono α hα l hl0 hl1) (leafAngle_window α hα hw l hl0 hl1)
    have hsmall := contracted_square l hl0 hl1
    intro a b hab
    rcases a with a|a <;> rcases b with b|b
    · exact congrArg Sum.inl (D.point_injective (scaledPoint_injective _ (ne_of_gt (sub_pos.mpr hl1)) hab))
    · have hb : square (scaledPoint (1-l) (D.point a))=1 := by
        change scaledPoint (1-l) (D.point a)=unitPoint (leafAngle α l b) at hab
        rw [hab,square_unitPoint]
      have hbound := explicit_old_bound D l hpoints a
      rw [hb] at hbound
      exact (not_le_of_gt hsmall hbound).elim
    · have ha : square (scaledPoint (1-l) (D.point b))=1 := by
        change unitPoint (leafAngle α l a)=scaledPoint (1-l) (D.point b) at hab
        rw [← hab,square_unitPoint]
      have hbound := explicit_old_bound D l hpoints b
      rw [ha] at hbound
      exact (not_le_of_gt hsmall hbound).elim
    · exact congrArg Sum.inr (hleaf hab)
  curve := extensionCurve D x α l
  continuous := by
    intro e
    rcases e with e|i
    · exact (D.rescale (1-l) (ne_of_gt (sub_pos.mpr hl1))).continuous e
    · change Continuous (fun t : ArcParameter => segment _ _ t.val)
      unfold segment
      fun_prop
  injective := by
    intro e
    rcases e with e|i
    · exact (D.rescale (1-l) (ne_of_gt (sub_pos.mpr hl1))).injective e
    · intro s _ t _ h
      have ha : square (scaledPoint (1-l) (D.point (x i)))<1 :=
        (explicit_old_bound D l hpoints (x i)).trans_lt (contracted_square l hl0 hl1)
      have hb := square_unitPoint (leafAngle α l i)
      have hab : scaledPoint (1-l) (D.point (x i)) ≠ unitPoint (leafAngle α l i) := by
        intro he; rw [he,hb] at ha; exact lt_irrefl _ ha
      exact Subtype.ext (segment_injective _ _ hab h)
  start := by
    intro e
    rcases e with e|i
    · change scaledPoint (1-l) (D.curve e _)=scaledPoint (1-l) (D.point (J.left e))
      rw [D.start]
    · simp [extensionCurve,extensionPoint,segment,CopiedGraph.withPendants,pendantLeft]
  finish := by
    intro e
    rcases e with e|i
    · change scaledPoint (1-l) (D.curve e _)=scaledPoint (1-l) (D.point (J.right e))
      rw [D.finish]
    · simp [extensionCurve,extensionPoint,segment,CopiedGraph.withPendants,pendantRight]
  avoids := by
    intro e t ht0 ht1 v h
    have hc2 := contracted_square l hl0 hl1
    rcases e with e|i <;> rcases v with v|j
    · exact D.avoids e t ht0 ht1 v (scaledPoint_injective _ (ne_of_gt (sub_pos.mpr hl1)) h)
    · have he := explicit_curve_bound D l hcurves e t
      change scaledPoint (1-l) (D.curve e t)=unitPoint (leafAngle α l j) at h
      rw [h,square_unitPoint] at he
      exact (not_le_of_gt hc2 he).elim
    · have hout := segment_outside _ _ (leafAngle_outward α hα hw l hl0 hlb i) t.val ht0
      rw [← hx i] at hout
      change segment (scaledPoint (1-l) (D.point (x i))) (unitPoint (leafAngle α l i)) t.val =
        scaledPoint (1-l) (D.point v) at h
      rw [h,scaled_square,hx i,square_unitPoint,mul_one] at hout
      exact (not_lt_of_ge (explicit_old_bound D l hpoints v) hout).elim
    · have he := segment_strict_disk _ _
        ((explicit_old_bound D l hpoints (x i)).trans_lt hc2)
        (square_unitPoint (leafAngle α l i)) t.val t.property.1 ht1
      change segment (scaledPoint (1-l) (D.point (x i))) (unitPoint (leafAngle α l i)) t.val =
        unitPoint (leafAngle α l j) at h
      rw [h,square_unitPoint] at he
      exact lt_irrefl _ he
  intersects := by
    intro e f hef s t h
    have hc2 := contracted_square l hl0 hl1
    have hcnz : 1-l ≠ 0 := ne_of_gt (sub_pos.mpr hl1)
    have old_new (e : E) (i : Fin 6) (s t : ArcParameter)
        (h : scaledPoint (1-l) (D.curve e s) =
          segment (scaledPoint (1-l) (D.point (x i))) (unitPoint (leafAngle α l i)) t.val) :
        (s.val=0 ∨ s.val=1) ∧ (t.val=0 ∨ t.val=1) := by
      have ht0 : t.val=0 := by
        by_contra hn
        have hp : 0<t.val := lt_of_le_of_ne t.property.1 (Ne.symm hn)
        have hout := segment_outside _ _ (leafAngle_outward α hα hw l hl0 hlb i) t.val hp
        rw [← hx i,← h,scaled_square,hx i,square_unitPoint,mul_one] at hout
        exact (not_lt_of_ge (explicit_curve_bound D l hcurves e s) hout).elim
      have hv : D.curve e s=D.point (x i) := by
        apply scaledPoint_injective _ hcnz
        simpa [ht0,segment] using h
      rcases (D.curve_vertex_iff e s (x i)).mp hv with ⟨hs,_⟩|⟨hs,_⟩
      · exact ⟨Or.inl hs,Or.inl ht0⟩
      · exact ⟨Or.inr hs,Or.inl ht0⟩
    rcases e with e|i <;> rcases f with f|j
    · exact D.intersects e f (fun he => hef (congrArg Sum.inl he)) s t (scaledPoint_injective _ hcnz h)
    · exact old_new e j s t h
    · have he := old_new f i t s h.symm
      exact ⟨he.2,he.1⟩
    · have hij : i ≠ j := fun he => hef (congrArg Sum.inr he)
      have hleaf := ordered_unitPoints_injective (leafAngle α l)
        (leafAngle_strictMono α hα l hl0 hl1) (leafAngle_window α hα hw l hl0 hl1)
      by_cases hxij : x i=x j
      · have ha := (explicit_old_bound D l hpoints (x i)).trans_lt hc2
        change segment (scaledPoint (1-l) (D.point (x i))) (unitPoint (leafAngle α l i)) s.val =
          segment (scaledPoint (1-l) (D.point (x j))) (unitPoint (leafAngle α l j)) t.val at h
        rw [← hxij] at h
        have he := same_attachment_intersection _ _ _ ha
          (square_unitPoint _) (square_unitPoint _) (fun hh => hij (hleaf hh))
          s.val t.val s.property.1 t.property.1 h
        exact ⟨Or.inl he.1,Or.inl he.2⟩
      · have hpij : unitPoint (α i) ≠ unitPoint (α j) := by
          rw [← hx i,← hx j]
          exact fun hh => hxij (D.point_injective hh)
        have hi := hpairs i j hpij
        have hj := hpairs j i (Ne.symm hpij)
        rw [dist_comm (unitPoint (α j)) (unitPoint (α i))] at hj
        have hn := different_attachment_intersection _ _ _ _ _ _ hpij hi.1 hi.2 hj.1 hj.2
          s.val t.val s.property.1 s.property.2 t.property.1 t.property.2
        apply (hn ?_).elim
        change segment (scaledPoint (1-l) (D.point (x i))) (unitPoint (leafAngle α l i)) s.val =
          segment (scaledPoint (1-l) (D.point (x j))) (unitPoint (leafAngle α l j)) t.val at h
        simpa only [hx] using h

/-- Genuine all-six pendant disk extension, with all construction inputs proved internally. -/
theorem exists_six_leaf_drawing (D : Drawing J) (x : Fin 6 → V) (α : Fin 6 → ℝ)
    (hα : Monotone α) (hw : α 5 ≤ α 0+2*Real.pi)
    (hx : ∀ i, D.point (x i)=unitPoint (α i))
    (hpoints : ∀ v, D.point v ∈ disk) (hcurves : ∀ e t, D.curve e t ∈ disk) :
    ∃ (l : ℝ) (D' : Drawing (J.withPendants x)),
      0<l ∧ l<1 ∧
      (∀ v, D'.point (Sum.inl v)=scaledPoint (1-l) (D.point v)) ∧
      (∀ e t, D'.curve (Sum.inl e) t=scaledPoint (1-l) (D.curve e t)) ∧
      (∀ v, D'.point v ∈ disk) ∧ (∀ e t, D'.curve e t ∈ disk) ∧
      cyclic_order D' (sixTerminals (V:=V)) := by
  obtain ⟨l,hl0,hl1,hlb,hpairs⟩ := exists_fan_parameter α hα hw
  let D' := explicitDrawing D x α hα hw hx hpoints hcurves l hl0 hl1 hlb hpairs
  refine ⟨l,D',hl0,hl1,(fun _ => rfl),(fun _ _ => rfl),?_,?_,?_⟩
  · intro v
    rcases v with v|i
    · exact (explicit_old_bound D l hpoints v).trans (contracted_square l hl0 hl1).le
    · exact (square_unitPoint _).le
  · intro e t
    rcases e with e|i
    · exact (explicit_curve_bound D l hcurves e t).trans (contracted_square l hl0 hl1).le
    · exact segment_disk _ _
        ((explicit_old_bound D l hpoints (x i)).trans (contracted_square l hl0 hl1).le)
        (square_unitPoint _).le t.val t.property.1 t.property.2
  · exact ⟨leafAngle α l,leafAngle_strictMono α hα l hl0 hl1,
      leafAngle_window α hα hw l hl0 hl1,fun _ => rfl⟩

end
end FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
