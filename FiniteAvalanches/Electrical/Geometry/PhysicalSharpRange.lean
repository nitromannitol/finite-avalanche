import FiniteAvalanches.Electrical.Geometry.PhysicalFaceStar
import FiniteAvalanches.Electrical.Geometry.PolarStream
import FiniteAvalanches.Electrical.Geometry.Angular
import FiniteAvalanches.External.TwoPoleTopology
import FiniteAvalanches.Electrical.Plane.UnitBoundary
import FiniteAvalanches.Electrical.Plane.ZeroSegments
import FiniteAvalanches.Electrical.Geometry.PhysicalTilingStream
import Mathlib.Data.List.Nodup

/-! Sharp physical incident ranges and containment in the triple dilation
of an attained largest-current original-copy square. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.PhysicalSharpRange
open StatementGeometry BSST Plane
open scoped Classical BigOperators
noncomputable section

private def append {W I : Type*} {a b : I → W} {u v w : W}
    (p : ForwardPath a b u v) (q : ForwardPath a b v w) : ForwardPath a b u w :=
  match p with
  | .nil _ => q
  | .cons e p => .cons e (append p q)

/-- Balanced copied unit incidence makes every weak link traversable forwards.
The reachable-set cut, rather than an assumed Euler traversal, proves this. -/
theorem balanced_linked_forwardPath {W I : Type*} [Fintype W] [Fintype I]
    (a b : I → W) (hbal : ∀ z, unitBoundary a b Finset.univ z = 0)
    (u v : W)
    (hlink : Relation.ReflTransGen
      (fun z w => ∃ e : I, z ∈ ({a e,b e} : Set W) ∧ w ∈ ({a e,b e} : Set W)) u v) :
    Nonempty (ForwardPath a b u v) := by
  let R : W → W → Prop := fun z w => ∃ e : I, z = a e ∧ w = b e
  let C : W → Prop := fun z => Relation.ReflTransGen R u z
  let H : W → ℝ := fun z => if C z then 1 else 0
  have hfwd (e : I) (ha : C (a e)) : C (b e) :=
    ha.tail ⟨e,rfl,rfl⟩
  have hsum : (∑ e, (H (a e)-H (b e))) = 0 := by
    have h := sum_mul_unitBoundary a b Finset.univ H
    simpa only [hbal,mul_zero,Finset.sum_const_zero] using h.symm
  have hnonpos (e : I) : H (a e)-H (b e) ≤ 0 := by
    by_cases ha : C (a e)
    · simp [H,ha,hfwd e ha]
    · by_cases hb : C (b e) <;> simp [H,ha,hb]
  have hback (e : I) (hb : C (b e)) : C (a e) := by
    by_contra ha
    have ht : H (a e)-H (b e) = -1 := by simp [H,ha,hb]
    have hle := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : I => -(H (a j)-H (b j)))
      (fun j _ => neg_nonneg.mpr (hnonpos j)) (Finset.mem_univ e)
    rw [Finset.sum_neg_distrib,hsum,neg_zero,ht] at hle
    norm_num at hle
  have hr : C v := by
    induction hlink with
    | refl => exact Relation.ReflTransGen.refl
    | @tail w z h hz ih =>
      obtain ⟨e,hw,hz⟩ := hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw hz
      rcases hw with rfl | rfl <;> rcases hz with rfl | rfl
      · exact ih
      · exact hfwd e ih
      · exact hback e ih
      · exact ih
  change Relation.ReflTransGen R u v at hr
  clear hlink
  induction hr with
  | refl => exact ⟨.nil _⟩
  | @tail w z h hz ih =>
    obtain ⟨p⟩ := ih
    obtain ⟨e,rfl,rfl⟩ := hz
    exact ⟨append p (.cons e (.nil _))⟩

private theorem suffix_at_copy {W I : Type*} {a b : I → W} {u v : W}
    (p : ForwardPath a b u v) :
    ∀ e, e ∈ p.edges → ∃ q : ForwardPath a b (a e) v, q.edges.Sublist p.edges := by
  induction p with
  | nil => intro e he; exact (List.not_mem_nil he).elim
  | cons d p ih =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact ⟨.cons d p,List.Sublist.refl _⟩
    · obtain ⟨q,hq⟩ := ih e he
      exact ⟨q,List.sublist_cons_of_sublist d hq⟩

/-- Erase repeated original IDs without changing either endpoint or direction. -/
private theorem erase_repeated_copies {W I : Type*} {a b : I → W} {u v : W}
    (p : ForwardPath a b u v) :
    ∃ q : ForwardPath a b u v, q.edges.Nodup ∧ q.edges.Sublist p.edges := by
  induction p with
  | nil => exact ⟨.nil _,List.nodup_nil,List.Sublist.refl _⟩
  | cons e p ih =>
    obtain ⟨q,hq,hsub⟩ := ih
    by_cases he : e ∈ q.edges
    · obtain ⟨r,hr⟩ := suffix_at_copy q e he
      exact ⟨r,hq.sublist hr,List.sublist_cons_of_sublist e (hr.trans hsub)⟩
    · exact ⟨.cons e q,List.nodup_cons.mpr ⟨he,hq⟩,hsub.cons_cons e⟩

private theorem path_increment_sum {W I : Type*} {a b : I → W}
    (f : W → ℝ) {u v : W} (p : ForwardPath a b u v) :
    (p.edges.map (fun e => f (b e)-f (a e))).sum = f v-f u := by
  induction p with
  | nil => simp [ForwardPath.edges]
  | cons e p ih =>
    simp only [ForwardPath.edges,List.map_cons,List.sum_cons,ih]
    ring

/-- The rise between linked vertices is at most HALF the total absolute copy
variation on a balanced finite directed graph. Loops and parallel IDs are retained. -/
theorem balanced_linked_rise_le_half_variation {W I : Type*} [Fintype W] [Fintype I]
    (a b : I → W) (hbal : ∀ z, unitBoundary a b Finset.univ z = 0)
    (f : W → ℝ) (u v : W)
    (hlink : Relation.ReflTransGen
      (fun z w => ∃ e : I, z ∈ ({a e,b e} : Set W) ∧ w ∈ ({a e,b e} : Set W)) u v) :
    2*(f v-f u) ≤ ∑ e, |f (b e)-f (a e)| := by
  obtain ⟨p⟩ := balanced_linked_forwardPath a b hbal u v hlink
  obtain ⟨q,hnd,_⟩ := erase_repeated_copies p
  have ht : (∑ e ∈ q.edges.toFinset, (f (b e)-f (a e))) = f v-f u := by
    rw [List.sum_toFinset _ hnd]
    exact path_increment_sum f q
  have hbudget : f v-f u ≤ ∑ e, max (f (b e)-f (a e)) 0 := by
    calc
      _ = ∑ e ∈ q.edges.toFinset, (f (b e)-f (a e)) := ht.symm
      _ ≤ ∑ e ∈ q.edges.toFinset, max (f (b e)-f (a e)) 0 :=
        Finset.sum_le_sum (fun e _ => le_max_left _ _)
      _ ≤ ∑ e, max (f (b e)-f (a e)) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun e _ _ => le_max_right _ _)
  have hz : (∑ e, (f (b e)-f (a e))) = 0 := by
    have h := sum_mul_unitBoundary a b Finset.univ f
    simp only [hbal,mul_zero,Finset.sum_const_zero] at h
    rw [Finset.sum_sub_distrib] at h ⊢
    linarith only [h]
  have habs (t : ℝ) : |t| = 2*max t 0-t := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht,max_eq_left ht]
      ring
    · rw [abs_of_neg (lt_of_not_ge ht),max_eq_right (le_of_not_ge ht)]
      ring
  have hsum : (∑ e, |f (b e)-f (a e)|) =
      2*(∑ e, max (f (b e)-f (a e)) 0) := by
    simp_rw [habs]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hz,sub_zero]
  rw [hsum]
  linarith only [hbudget]

/-- Sharp actual physical incident range. Every needed local topology statement
is derived from the registered universal face-boundary law and actual face star. -/
theorem physical_vertex_range_le_two_largest {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (x : {v : V // v ≠ alpha ∧ v ≠ beta})
    (hdeg : Geometry.degree J.left J.right x.val ≤ 4) :
    let hx := incidenceDarts_nonempty J.left J.right alpha beta hne hc x.val
    sSup (incidentValues A.embedding.drawing psi x.val)-
      sInf (incidentValues A.embedding.drawing psi x.val) ≤
      2*largestCurrent J.left J.right (Source.voltage J alpha beta hc) x.val hx := by
  intro hx
  let phi := Source.voltage J alpha beta hc
  let s := largestCurrent J.left J.right phi x.val hx
  have hs : 0 ≤ s := largestCurrent_nonneg J.left J.right phi x.val hx
  change sSup (incidentValues A.embedding.drawing psi x.val)-
    sInf (incidentValues A.embedding.drawing psi x.val) ≤ 2*s
  obtain ⟨finiteFaces,_,_,_,hcycle⟩ :=
    FiniteAvalanches.External.finite_plane_two_pole_topology J D hc alpha beta hne A
  letI : Fintype A.embedding.Face := finiteFaces
  let q : V → ℝ := fun v => if v = x.val then 1 else 0
  let a : E → A.embedding.Face := fun e =>
    if J.left e=x.val then A.embedding.rightFace (.inl e) else A.embedding.leftFace (.inl e)
  let b : E → A.embedding.Face := fun e =>
    if J.right e=x.val then A.embedding.rightFace (.inl e) else A.embedding.leftFace (.inl e)
  have hqa : q alpha = 0 := by simp [q,x.property.1.symm]
  have hqb : q beta = 0 := by simp [q,x.property.2.symm]
  have hbal (F : A.embedding.Face) : unitBoundary a b Finset.univ F = 0 := by
    have heq : unitBoundary a b Finset.univ F =
        copyBoundary (Source.augmentedDual A).left (Source.augmentedDual A).right
          (copyGradient (Source.augmentedGraph J alpha beta).left
            (Source.augmentedGraph J alpha beta).right q) F := by
      unfold unitBoundary copyBoundary
      rw [Fintype.sum_sum_type]
      simp only [Fintype.sum_unique,Source.augmentedDual,copyGradient,
        Source.augmentedGraph,Sum.elim_inl,Sum.elim_inr,hqa,hqb,sub_self,ite_self,add_zero]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hl : J.left e=x.val <;> by_cases hr : J.right e=x.val <;>
        simp [a,b,q,hl,hr] <;> split_ifs <;> norm_num <;> contradiction
    rw [heq]
    exact hcycle q F
  have hcurrent (e : E) (he : J.left e=x.val ∨ J.right e=x.val) :
      |phi (J.left e)-phi (J.right e)| ≤ s := by
    rcases he with he | he
    · exact current_le_largestCurrent J.left J.right phi x.val hx (e,false) he
    · have h := current_le_largestCurrent J.left J.right phi x.val hx (e,true) he
      change |phi (J.right e)-phi (J.left e)| ≤ s at h
      rwa [abs_sub_comm] at h
  have hstep (e : E) : |psi (b e)-psi (a e)| ≤
      ((if J.left e=x.val then 1 else 0)+(if J.right e=x.val then 1 else 0))*s := by
    have hp := hpsi.1 e
    change psi (A.embedding.leftFace (.inl e))-psi (A.embedding.rightFace (.inl e)) =
      phi (J.left e)-phi (J.right e) at hp
    by_cases hl : J.left e=x.val
    · have hr : J.right e ≠ x.val := fun hr => D.endpoints_ne e (hl.trans hr.symm)
      simpa only [a,b,if_pos hl,if_neg hr,add_zero,one_mul,hp] using hcurrent e (Or.inl hl)
    · by_cases hr : J.right e=x.val
      · have hh := hcurrent e (Or.inr hr)
        rw [← hp,abs_sub_comm] at hh
        simpa only [a,b,if_neg hl,if_pos hr,zero_add,one_mul] using hh
      · simp only [a,b,if_neg hl,if_neg hr,sub_self,abs_zero,zero_add,zero_mul,le_refl]
  have htotal : (∑ e, |psi (b e)-psi (a e)|) ≤ 4*s := by
    calc
      _ ≤ ∑ e, ((if J.left e=x.val then 1 else 0)+(if J.right e=x.val then 1 else 0))*s :=
        Finset.sum_le_sum (fun e _ => hstep e)
      _ = Geometry.degree J.left J.right x.val*s := by
        rw [← Finset.sum_mul]
        rfl
      _ ≤ 4*s := mul_le_mul_of_nonneg_right hdeg hs
  obtain ⟨hstar_ne,hstar_finite,_,hstar⟩ :=
    PhysicalFaceStar14.physical_original_face_star J D hc alpha beta A x
  obtain ⟨F,hF,hmin⟩ := Set.exists_min_image _ psi hstar_finite hstar_ne
  obtain ⟨G,hG,hmax⟩ := Set.exists_max_image _ psi hstar_finite hstar_ne
  have hlo : sInf (incidentValues A.embedding.drawing psi x.val)=psi F := by
    apply IsLeast.csInf_eq
    refine ⟨⟨F,hF,rfl⟩,?_⟩
    rintro y ⟨H,hH,rfl⟩
    exact hmin H hH
  have hhi : sSup (incidentValues A.embedding.drawing psi x.val)=psi G := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨G,hG,rfl⟩,?_⟩
    rintro y ⟨H,hH,rfl⟩
    exact hmax H hH
  have hlink : Relation.ReflTransGen
      (fun U W => ∃ e : E, U ∈ ({a e,b e} : Set A.embedding.Face) ∧
        W ∈ ({a e,b e} : Set A.embedding.Face)) F G := by
    apply Relation.ReflTransGen.mono (p := fun U W => ∃ e : E,
      U ∈ ({a e,b e} : Set A.embedding.Face) ∧ W ∈ ({a e,b e} : Set A.embedding.Face))
      ?_ F G (hstar F G hF hG)
    intro U W h
    obtain ⟨e,he,hU,hW⟩ := h
    have hp : edgeFaces A.embedding.drawing (.inl e) =
        ({a e,b e} : Set A.embedding.Face) := by
      rw [PhysicalTiling.physical_edgeFaces_eq J D hc alpha beta hne A (.inl e)]
      rcases he with hl | hr
      · have hn : J.right e ≠ x.val := fun hr => D.endpoints_ne e (hl.trans hr.symm)
        simp [a,b,hl,hn]
      · have hn : J.left e ≠ x.val := fun hl => D.endpoints_ne e (hl.trans hr.symm)
        simp [a,b,hn,hr,Set.pair_comm]
    exact ⟨e,hp ▸ hU,hp ▸ hW⟩
  have h := balanced_linked_rise_le_half_variation a b hbal psi F G hlink
  rw [hhi,hlo]
  linarith only [h,htotal]

/-- Actual source stream construction and full characterization precede the sharp range.
No balance, traversal, cyclic order or desired range is an input. -/
theorem physical_unique_stream_range_le_two_largest
    {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (x : {v : V // v ≠ alpha ∧ v ≠ beta})
    (hdeg : Geometry.degree J.left J.right x.val ≤ 4) :
    let hx := incidenceDarts_nonempty J.left J.right alpha beta hne hc x.val
    ∃! psi : A.embedding.Face → ℝ,
      Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi ∧
      sSup (incidentValues A.embedding.drawing psi x.val)-
        sInf (incidentValues A.embedding.drawing psi x.val) ≤
        2*largestCurrent J.left J.right (Source.voltage J alpha beta hc) x.val hx := by
  intro hx
  obtain ⟨psi,hpsi,huniq⟩ := Source.existsUnique_polar_stream J D hc alpha beta hne A
  refine ⟨psi,⟨hpsi,physical_vertex_range_le_two_largest J D hc alpha beta hne A psi hpsi x hdeg⟩,?_⟩
  intro chi hchi
  exact huniq chi hchi.1

/-- The sharp incident span gives exactly the source's concentric3Q containment,
including a zero-side square, from literal side containment. -/
theorem vertical_segment_subset_triple_dilate (Q : Geometry.Square) (v L H : ℝ)
    (hv : v = Q.x ∨ v = Q.x+Q.side)
    (hL : L ≤ Q.y) (hH : Q.y+Q.side ≤ H)
    (hspan : H-L ≤ 2*Q.side) :
    ({v} ×ˢ Set.Icc L H : Set (ℝ × ℝ)) ⊆
      (Q.dilate 3 (by norm_num)).carrier := by
  intro z hz
  have hzv : z.1 = v := Set.mem_singleton_iff.mp hz.1
  have hs := Q.side_nonneg
  change (Q.x-(3-1)*Q.side/2 ≤ z.1 ∧
      z.1 ≤ Q.x-(3-1)*Q.side/2+3*Q.side) ∧
    (Q.y-(3-1)*Q.side/2 ≤ z.2 ∧
      z.2 ≤ Q.y-(3-1)*Q.side/2+3*Q.side)
  rw [hzv]
  rcases hv with rfl | rfl <;>
    exact ⟨⟨by linarith,by linarith⟩,
      ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩

private theorem min_add_abs_sub_eq_max (u v : ℝ) : min u v + |u-v| = max u v := by
  rcases le_total u v with h | h
  · rw [min_eq_left h,max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h,max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Actual chosen original-copy square and its concentric triple dilation.
The maximizer is obtained from the genuine incident-current maximum. All sides
of every original incident copy are retained, including zero-current points.
No positive-current assumption is required; at zero the segment equals the point square. -/
theorem physical_exists_max_square_triple_contains_segment
    {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (hne : alpha ≠ beta) (A : Source.OuterArc D alpha beta)
    (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (x : {v : V // v ≠ alpha ∧ v ≠ beta})
    (hdeg : Geometry.degree J.left J.right x.val ≤ 4) :
    let phi := Source.voltage J alpha beta hc
    let hx := incidenceDarts_nonempty J.left J.right alpha beta hne hc x.val
    let lo := sInf (incidentValues A.embedding.drawing psi x.val)
    let hi := sSup (incidentValues A.embedding.drawing psi x.val)
    ∃ e : E, (J.left e = x.val ∨ J.right e = x.val) ∧ ∃ Q : Geometry.Square,
      Q.carrier = Source.edgeSquare D alpha beta A phi psi e ∧
      Q.side = largestCurrent J.left J.right phi x.val hx ∧
      BSST.vertexSegment phi x.val lo hi ⊆ (Q.dilate 3 (by norm_num)).carrier ∧
      (Q.side = 0 → BSST.vertexSegment phi x.val lo hi = Q.carrier) ∧
      ∀ d : E, J.left d = x.val ∨ J.right d = x.val →
        {p : ℝ × ℝ | p ∈ Source.edgeSquare D alpha beta A phi psi d ∧ p.1 = phi x.val}
          ⊆ (Q.dilate 3 (by norm_num)).carrier := by
  intro phi hx lo hi
  obtain ⟨⟨e,k⟩,htail,hmax⟩ :=
    exists_incident_max_current J.left J.right phi x.val hx
  have he : J.left e = x.val ∨ J.right e = x.val := by
    cases k
    · exact Or.inl htail
    · exact Or.inr htail
  have hm : |phi (J.left e)-phi (J.right e)| =
      largestCurrent J.left J.right phi x.val hx := by
    cases k
    · exact hmax
    · change |phi (J.right e)-phi (J.left e)| = _ at hmax
      rwa [abs_sub_comm] at hmax
  let Q : Geometry.Square :=
    ⟨min (phi (J.left e)) (phi (J.right e)),
      min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))),
      |phi (J.left e)-phi (J.right e)|,abs_nonneg _⟩
  have hcarrier : Q.carrier = Source.edgeSquare D alpha beta A phi psi e := by
    change (Set.Icc (min (phi (J.left e)) (phi (J.right e)))
        (min (phi (J.left e)) (phi (J.right e)) + |phi (J.left e)-phi (J.right e)|) ×ˢ
      Set.Icc (min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))))
        (min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))) +
          |phi (J.left e)-phi (J.right e)|)) = _
    rw [min_add_abs_sub_eq_max,← hpsi.1 e,min_add_abs_sub_eq_max]
    rfl
  have hside : Q.side = largestCurrent J.left J.right phi x.val hx := hm
  have hv : phi x.val = Q.x ∨ phi x.val = Q.x+Q.side := by
    change phi x.val = min (phi (J.left e)) (phi (J.right e)) ∨
      phi x.val = min (phi (J.left e)) (phi (J.right e)) +
        |phi (J.left e)-phi (J.right e)|
    rw [min_add_abs_sub_eq_max]
    rcases he with he | he
    · rw [← he]
      rcases le_total (phi (J.left e)) (phi (J.right e)) with h | h
      · exact Or.inl (min_eq_left h).symm
      · exact Or.inr (max_eq_left h).symm
    · rw [← he]
      rcases le_total (phi (J.left e)) (phi (J.right e)) with h | h
      · exact Or.inr (max_eq_right h).symm
      · exact Or.inl (min_eq_right h).symm
  have hvI : phi x.val ∈ Set.Icc Q.x (Q.x+Q.side) := by
    rcases hv with hv | hv <;> rw [hv] <;>
      exact ⟨by linarith [Q.side_nonneg],by linarith [Q.side_nonneg]⟩
  have hbottom : (phi x.val,Q.y) ∈ Q.carrier :=
    ⟨hvI,⟨le_rfl,by linarith [Q.side_nonneg]⟩⟩
  have htop : (phi x.val,Q.y+Q.side) ∈ Q.carrier :=
    ⟨hvI,⟨by linarith [Q.side_nonneg],le_rfl⟩⟩
  have hbottomSeg := PhysicalTiling.physical_square_side_mem_incident_segment
    J D hc alpha beta hne A psi hpsi x.val e he _ (hcarrier ▸ hbottom) rfl
  have htopSeg := PhysicalTiling.physical_square_side_mem_incident_segment
    J D hc alpha beta hne A psi hpsi x.val e he _ (hcarrier ▸ htop) rfl
  have hL : lo ≤ Q.y := hbottomSeg.2.1
  have hH : Q.y+Q.side ≤ hi := htopSeg.2.2
  have hspan : hi-lo ≤ 2*Q.side := by
    rw [hside]
    exact physical_vertex_range_le_two_largest J D hc alpha beta hne A psi hpsi x hdeg
  have hcontain : BSST.vertexSegment phi x.val lo hi ⊆
      (Q.dilate 3 (by norm_num)).carrier :=
    vertical_segment_subset_triple_dilate Q (phi x.val) lo hi hv hL hH hspan
  refine ⟨e,he,Q,hcarrier,hside,hcontain,?_,?_⟩
  · intro hz
    have hdilate : (Q.dilate 3 (by norm_num)).carrier = Q.carrier := by
      simp only [Geometry.Square.carrier,Geometry.Square.dilate,hz,
        mul_zero,zero_div,sub_zero,add_zero]
    apply Set.Subset.antisymm
    · exact hdilate ▸ hcontain
    · intro p hp
      have hpx : p.1 = phi x.val := by
        have hp1 : Q.x ≤ p.1 ∧ p.1 ≤ Q.x+Q.side := hp.1
        rcases hv with hv | hv <;> simp only [hz,add_zero] at hp1 hv <;> linarith
      exact PhysicalTiling.physical_square_side_mem_incident_segment
        J D hc alpha beta hne A psi hpsi x.val e he p (hcarrier ▸ hp) hpx
  · intro d hd p hp
    exact hcontain (PhysicalTiling.physical_square_side_mem_incident_segment
      J D hc alpha beta hne A psi hpsi x.val d hd p hp.1 hp.2)

end
end FiniteAvalanches.Electrical.PhysicalSharpRange
