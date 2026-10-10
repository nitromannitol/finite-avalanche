import FiniteAvalanches.Electrical.Geometry.PhysicalSharpRange
import FiniteAvalanches.Electrical.Geometry.Charging
import FiniteAvalanches.Electrical.Geometry.BoundaryMidpoints
import FiniteAvalanches.Electrical.Plane.SplitFormation

/-! Midpoint trial values and once-per-copy charging on physical squares.
The split-terminal height placement is an explicit geometric predecessor. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.PhysicalCharging
open StatementGeometry BSST Plane Geometry
open scoped Classical BigOperators
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- The original copy's closed physical square, including zero-current points. -/
def copySquare (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (e : E) : Square :=
  ⟨min (phi (J.left e)) (phi (J.right e)),
    min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))),
    |phi (J.left e)-phi (J.right e)|,abs_nonneg _⟩

/-- Midpoint of the full physical incident segment, using all incident faces. -/
def segmentMidpoint (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (x : V) : ℝ × ℝ :=
  (phi x,(sInf (incidentValues A.embedding.drawing psi x)+
    sSup (incidentValues A.embedding.drawing psi x))/2)

/-- Midpoint of the copied square's vertical side at a specified endpoint voltage. -/
def copySideMidpoint (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (x : V) (e : E) : ℝ × ℝ :=
  (phi x,(copySquare J D alpha beta A phi psi e).y+
    (copySquare J D alpha beta A phi psi e).side/2)

private lemma min_add_abs_sub_eq_max (u v : ℝ) : min u v + |u-v| = max u v := by
  rcases le_total u v with h | h
  · rw [min_eq_left h,max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h,max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
    ring

lemma copySquare_carrier (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A phi psi) (e : E) :
    (copySquare J D alpha beta A phi psi e).carrier =
      Source.edgeSquare D alpha beta A phi psi e := by
  change Set.Icc (min (phi (J.left e)) (phi (J.right e)))
      (min (phi (J.left e)) (phi (J.right e))+|phi (J.left e)-phi (J.right e)|) ×ˢ
    Set.Icc (min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))))
      (min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e)))+
        |phi (J.left e)-phi (J.right e)|) = _
  rw [min_add_abs_sub_eq_max,← hpsi.1 e,min_add_abs_sub_eq_max]
  rfl

private lemma square_eq_of_carrier_eq (Q R : Square) (h : Q.carrier = R.carrier) : Q = R := by
  have hQ : (Q.x,Q.y) ∈ Q.carrier :=
    ⟨⟨le_rfl,by linarith [Q.side_nonneg]⟩,⟨le_rfl,by linarith [Q.side_nonneg]⟩⟩
  have hR : (R.x,R.y) ∈ R.carrier :=
    ⟨⟨le_rfl,by linarith [R.side_nonneg]⟩,⟨le_rfl,by linarith [R.side_nonneg]⟩⟩
  have hQr : (Q.x,Q.y) ∈ R.carrier := h ▸ hQ
  have hRq : (R.x,R.y) ∈ Q.carrier := h.symm ▸ hR
  have hx : Q.x = R.x := le_antisymm hRq.1.1 hQr.1.1
  have hy : Q.y = R.y := le_antisymm hRq.2.1 hQr.2.1
  have hQt : (Q.x+Q.side,Q.y) ∈ Q.carrier :=
    ⟨⟨by linarith [Q.side_nonneg],le_rfl⟩,⟨le_rfl,by linarith [Q.side_nonneg]⟩⟩
  have hRt : (R.x+R.side,R.y) ∈ R.carrier :=
    ⟨⟨by linarith [R.side_nonneg],le_rfl⟩,⟨le_rfl,by linarith [R.side_nonneg]⟩⟩
  have hQrt : (Q.x+Q.side,Q.y) ∈ R.carrier := h ▸ hQt
  have hRqt : (R.x+R.side,R.y) ∈ Q.carrier := h.symm ▸ hRt
  have hs : Q.side = R.side := by linarith [hQrt.1.2,hRqt.1.2]
  cases Q; cases R
  simp_all

lemma copySideMidpoint_mem (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (x : V) (e : E)
    (he : J.left e=x ∨ J.right e=x) :
    copySideMidpoint J D alpha beta A phi psi x e ∈
      (copySquare J D alpha beta A phi psi e).carrier := by
  let Q := copySquare J D alpha beta A phi psi e
  have hx : min (phi (J.left e)) (phi (J.right e)) ≤ phi x ∧
      phi x ≤ max (phi (J.left e)) (phi (J.right e)) := by
    rcases he with he | he
    · rw [← he]; exact ⟨min_le_left _ _,le_max_left _ _⟩
    · rw [← he]; exact ⟨min_le_right _ _,le_max_right _ _⟩
  change phi x ∈ Set.Icc Q.x (Q.x+Q.side) ∧ Q.y+Q.side/2 ∈ Set.Icc Q.y (Q.y+Q.side)
  constructor
  · simpa only [Q,copySquare,min_add_abs_sub_eq_max,Set.mem_Icc] using hx
  · constructor <;> linarith [Q.side_nonneg]

lemma segmentMidpoint_mem (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ) (x : {v : V // v ≠ alpha ∧ v ≠ beta}) :
    segmentMidpoint J D alpha beta A (Source.voltage J alpha beta hc) psi x.val ∈
      BSST.vertexSegment (Source.voltage J alpha beta hc) x.val
        (sInf (incidentValues A.embedding.drawing psi x.val))
        (sSup (incidentValues A.embedding.drawing psi x.val)) := by
  obtain ⟨_,_,F,G,_,_,hlo,hhi,hmin,hmax,_⟩ :=
    PhysicalFaceStar14.physical_incident_values_extrema J D hc alpha beta A psi x
  have hle : psi F ≤ psi G := hlo.2 hhi.1
  simp only [segmentMidpoint,BSST.vertexSegment,Set.mem_prod,Set.mem_singleton_iff,Set.mem_Icc,
    hmin,hmax]
  exact ⟨True.intro,by constructor <;> linarith only [hle]⟩

/-- One actual maximizing original copy per free vertex. The full segment and
all zero-current points fit its triple dilation. Terminals receive no charge. -/
theorem exists_physical_selection (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree J.left J.right x ≤ 4) :
    let phi := Source.voltage J alpha beta hc
    let Q := copySquare J D alpha beta A phi psi
    ∃ q : V → Option E, q alpha = none ∧ q beta = none ∧
      (∀ x, x ≠ alpha → x ≠ beta → ∃ e, q x = some e) ∧
      ∀ x e, q x = some e →
        (J.left e=x ∨ J.right e=x) ∧ x ≠ alpha ∧ x ≠ beta ∧
        (Q e).side = largestCurrent J.left J.right phi x
          (incidenceDarts_nonempty J.left J.right alpha beta hne hc x) ∧
        BSST.vertexSegment phi x (sInf (incidentValues A.embedding.drawing psi x))
          (sSup (incidentValues A.embedding.drawing psi x)) ⊆
            ((Q e).dilate 3 (by norm_num)).carrier := by
  intro phi Q
  have hs : ∀ x : {v : V // v ≠ alpha ∧ v ≠ beta}, ∃ e,
      (J.left e=x.val ∨ J.right e=x.val) ∧
      (Q e).side = largestCurrent J.left J.right phi x.val
        (incidenceDarts_nonempty J.left J.right alpha beta hne hc x.val) ∧
      BSST.vertexSegment phi x.val (sInf (incidentValues A.embedding.drawing psi x.val))
        (sSup (incidentValues A.embedding.drawing psi x.val)) ⊆
          ((Q e).dilate 3 (by norm_num)).carrier := by
    intro x
    obtain ⟨e,hi,R,hR,hside,hseg,_⟩ :=
      PhysicalSharpRange.physical_exists_max_square_triple_contains_segment
        J D hc alpha beta hne A psi hpsi x (hdeg x.val x.property.1 x.property.2)
    have heq : R = Q e := square_eq_of_carrier_eq R (Q e)
      (hR.trans (copySquare_carrier J D alpha beta A phi psi hpsi e).symm)
    subst R
    exact ⟨e,hi,hside,hseg⟩
  choose sel hsel using hs
  let q : V → Option E := fun x => if hx : x ≠ alpha ∧ x ≠ beta then some (sel ⟨x,hx⟩) else none
  refine ⟨q,?_,?_,?_,?_⟩
  · simp [q]
  · simp [q]
  · intro x ha hb; exact ⟨sel ⟨x,ha,hb⟩,by simp [q,ha,hb]⟩
  · intro x e he
    by_cases hx : x ≠ alpha ∧ x ≠ beta
    · have hei : sel ⟨x,hx⟩ = e := by simpa only [q,dif_pos hx,Option.some.injEq] using he
      obtain ⟨hi,hm,hc⟩ := hsel ⟨x,hx⟩
      rw [hei] at hi hm hc
      exact ⟨hi,hx.1,hx.2,hm,hc⟩
    · simp only [q,dif_neg hx] at he
      cases he

/-- Source midpoint trial, beta grounded, with the two alpha copies at zero/one. -/
def splitMidpointTrial (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (alpha beta : V) (A : Source.OuterArc D alpha beta)
    (phi : V → ℝ) (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) : SplitVertex alpha → ℝ
  | .inl x => if x.val=beta then 0 else angular epsilon y0 (segmentMidpoint J D alpha beta A phi psi x.val)
  | .inr k => if k then 1 else 0

/-- Actual once-per-copy split charging with one exceptional original copy.
The terminal-height binder records the still separate split-order construction;
it is not an assumed endpoint comparison or summed-energy bound. -/
theorem physical_split_charging_of_terminal_heights
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree J.left J.right x ≤ 4)
    (side : E → Bool) (exception : E) (epsilon y0 : ℝ) (he : 0 < epsilon)
    (hheight : ∀ e, e ≠ exception → J.left e=alpha ∨ J.right e=alpha →
      if side e then y0+epsilon ≤
        (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y+
          (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side/2
      else (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).y+
          (copySquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).side/2 ≤ y0-epsilon) :
    let phi := Source.voltage J alpha beta hc
    let Q := copySquare J D alpha beta A phi psi
    let a := fun e => splitEndpoint alpha side (J.left e) e
    let b := fun e => splitEndpoint alpha side (J.right e) e
    let f := splitMidpointTrial J D alpha beta A phi psi epsilon y0
    let weight := fun v => 1-phi (collapse alpha v)
    (∑ e, weight (a e)*weight (b e)*(f (a e)-f (b e))^2) ≤
      1+27*∑ e, ((Q e).angularOsc epsilon y0 3 (by norm_num) he)^2 := by
  intro phi Q a b f weight
  obtain ⟨q,_hqa,hqb,hfree,hsel⟩ := exists_physical_selection J D hc alpha beta hne A psi hpsi hdeg
  let qs : SplitVertex alpha → Option E
    | .inl x => q x.val
    | .inr _ => none
  let p : SplitVertex alpha → ℝ × ℝ := fun v =>
    segmentMidpoint J D alpha beta A phi psi (collapse alpha v)
  let z := fun e => copySideMidpoint J D alpha beta A phi psi (J.left e) e
  let t := fun e => copySideMidpoint J D alpha beta A phi psi (J.right e) e
  have hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1 := by
    intro v
    cases v with
    | inl x =>
      dsimp only [f,splitMidpointTrial]
      split_ifs
      · norm_num
      · exact angular_mem_unitInterval epsilon y0 he _
    | inr k => cases k <;> norm_num [f,splitMidpointTrial]
  have hw : ∀ v, 0 ≤ weight v ∧ weight v ≤ 1 := by
    intro v
    have hspec := Source.voltage_spec J alpha beta hne hc
    have hr := voltage_range J.left J.right alpha beta hc phi hspec.1 hspec.2.1 hspec.2.2 (collapse alpha v)
    constructor <;> dsimp only [weight] <;> linarith only [hr.1,hr.2]
  have hqi : ∀ v e, qs v=some e → v=a e ∨ v=b e := by
    intro v e hv
    cases v with
    | inr k => simp only [qs] at hv; cases hv
    | inl x =>
      have hi := (hsel x.val e hv).1
      rcases hi with hi | hi
      · exact Or.inl ((splitEndpoint_eq_inl alpha side (J.left e) e x).mpr hi).symm
      · exact Or.inr ((splitEndpoint_eq_inl alpha side (J.right e) e x).mpr hi).symm
  have hqd : ∀ v, qs v ≠ none → degree a b v ≤ 4 := by
    intro v hv
    cases v with
    | inr k => exact (hv rfl).elim
    | inl x =>
      have hxb : x.val ≠ beta := fun h => hv (by simpa only [qs,h] using hqb)
      change degree (fun e => splitEndpoint alpha side (J.left e) e)
        (fun e => splitEndpoint alpha side (J.right e) e) (.inl x) ≤ 4
      rw [split_degree_inl]
      exact hdeg x.val x.property hxb
  have fit (x : V) (e : E) (hinc : J.left e=x ∨ J.right e=x)
      (hx : x ≠ beta) (hex : e ≠ exception) :
      endpointFits Q qs epsilon y0 3 (by norm_num) f p
        (splitEndpoint alpha side x e) (copySideMidpoint J D alpha beta A phi psi x e) := by
    by_cases hxa : x=alpha
    · subst x
      have hpa : phi alpha=0 := (Source.voltage_spec J alpha beta hne hc).1
      have hh := hheight e hex hinc
      have hsplit : splitEndpoint alpha side alpha e = .inr (side e) := by
        simp [splitEndpoint]
      rw [hsplit]
      change (if side e then (1:ℝ) else 0) =
        angular epsilon y0 (copySideMidpoint J D alpha beta A phi psi alpha e)
      cases hs : side e
      · simp only [hs,Bool.false_eq_true,if_false] at hh ⊢
        symm
        have hp := angular_axis_eq_zero epsilon y0
          ((Q e).y+(Q e).side/2) he hh
        simpa only [copySideMidpoint,hpa] using hp
      · simp only [hs,if_true] at hh ⊢
        symm
        have hp := angular_axis_eq_one epsilon y0
          ((Q e).y+(Q e).side/2) he hh
        simpa only [copySideMidpoint,hpa] using hp
    · let v : {v : V // v ≠ alpha} := ⟨x,hxa⟩
      have hsplit : splitEndpoint alpha side x e = .inl v :=
        (splitEndpoint_eq_inl alpha side x e v).mpr rfl
      rw [hsplit]
      have hmid := segmentMidpoint_mem J D hc alpha beta A psi ⟨x,hxa,hx⟩
      have hside : copySideMidpoint J D alpha beta A phi psi x e ∈
          BSST.vertexSegment phi x (sInf (incidentValues A.embedding.drawing psi x))
            (sSup (incidentValues A.embedding.drawing psi x)) :=
        PhysicalTiling.physical_square_side_mem_incident_segment J D hc alpha beta hne A psi hpsi
          x e hinc _ ((copySquare_carrier J D alpha beta A phi psi hpsi e) ▸
            copySideMidpoint_mem J D alpha beta A phi psi x e hinc) rfl
      obtain ⟨i,hi⟩ := hfree x hxa hx
      have hs := (hsel x i hi).2.2.2.2
      dsimp only [endpointFits,qs,v]
      rw [hi]
      exact ⟨by simp only [f,splitMidpointTrial,if_neg hx]; rfl,hs hmid,hs hside⟩
  have hnot (e : E) (h : weight (a e)*weight (b e) ≠ 0) :
      J.left e ≠ beta ∧ J.right e ≠ beta := by
    have hb : phi beta=1 := (Source.voltage_spec J alpha beta hne hc).2.1
    have hwab : weight (a e)*weight (b e) = (1-phi (J.left e))*(1-phi (J.right e)) := by
      simp only [weight,a,b,collapse_splitEndpoint]
    constructor
    · intro hleft; apply h; rw [hwab,hleft,hb]; ring
    · intro hright; apply h; rw [hwab,hright,hb]; ring
  have h := dirichlet_charging_le a b Q qs epsilon y0 3 4 he (by norm_num) (by norm_num)
    f weight p z t {exception}
    (fun e _ => ⟨(hf (a e)).1,(hf (a e)).2,(hf (b e)).1,(hf (b e)).2⟩)
    hw hqi hqd
    (fun e _ _ => ⟨(Q e).carrier_subset_dilate 3 (by norm_num)
      (copySideMidpoint_mem J D alpha beta A phi psi (J.left e) e (Or.inl rfl)),
      (Q e).carrier_subset_dilate 3 (by norm_num)
      (copySideMidpoint_mem J D alpha beta A phi psi (J.right e) e (Or.inr rfl))⟩)
    (fun e hbad hw => fit (J.left e) e (Or.inl rfl) (hnot e hw).1 (by simpa using hbad))
    (fun e hbad hw => fit (J.right e) e (Or.inr rfl) (hnot e hw).2 (by simpa using hbad))
  norm_num only [Finset.card_singleton,Nat.cast_one] at h
  exact h

end
end FiniteAvalanches.Electrical.PhysicalCharging
