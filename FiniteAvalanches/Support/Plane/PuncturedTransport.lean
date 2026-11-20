import FiniteAvalanches.Electrical.Geometry.ConnectedDrawingQuotient
import FiniteAvalanches.Electrical.Geometry.BSST
import FiniteAvalanches.Support.Plane.FinitePointComplement
import FiniteAvalanches.Support.Plane.EndpointLocalConnectivity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.GDelta.Basic

/-!
# Topology of plane graph faces

Compactness of a finite drawing and openness of its complement components.
The proofs follow `FiniteAvalanches.Electrical.Source.drawingTrace_isCompact` and
`FiniteAvalanches.Electrical.PunctureTransport.faceRegion_isOpen`.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open Source Set
open scoped Classical

private theorem nowhereDense_union {s t : Set Plane} (hs : IsNowhereDense s)
    (ht : IsNowhereDense t) : IsNowhereDense (s ∪ t) := by
  unfold IsNowhereDense at *
  rw [closure_union, interior_union_isClosed_of_interior_empty isClosed_closure ht, hs]

private theorem nowhereDense_iUnion {ι : Type} [Fintype ι] (s : ι → Set Plane)
    (hs : ∀ i, IsNowhereDense (s i)) : IsNowhereDense (⋃ i, s i) := by
  classical
  have h : ∀ a : Finset ι, IsNowhereDense (⋃ i ∈ a, s i) := by
    intro a
    induction a using Finset.induction_on with
    | empty => simp
    | @insert i a hi ih =>
      simpa only [Finset.mem_insert, iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left] using
        nowhereDense_union (hs i) ih
  simpa using h Finset.univ

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Removing a point from an open preconnected region leaves it preconnected. -/
theorem IsOpen.isPreconnected_diff_singleton {U : Set Plane} (hU : IsOpen U)
    (hconn : IsPreconnected U) (p : Plane) : IsPreconnected (U \ {p}) := by
  by_cases hp : p ∈ U
  · obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU p hp
    let A := U \ {p}
    let B := Metric.ball p r \ {p}
    have hBA : B ⊆ A := fun z hz => ⟨hrU hz.1, hz.2⟩
    obtain ⟨x, hx⟩ := (isPathConnected_ball_diff_singleton p hr).nonempty
    let C := connectedComponentIn A x
    have hBC : B ⊆ C :=
      (isPathConnected_ball_diff_singleton p hr).isConnected.isPreconnected
        |>.subset_connectedComponentIn hx hBA
    have hCopen : IsOpen C := (hU.inter isClosed_singleton.isOpen_compl).connectedComponentIn
    have hCclosed : closure C ∩ A ⊆ C := by
      intro z hz
      have hxA : x ∈ A := hBA hx
      have himage : (Subtype.val : A → Plane) '' connectedComponent (⟨x, hxA⟩ : A) = C :=
        (connectedComponentIn_eq_image hxA).symm
      have hz' : (⟨z, hz.2⟩ : A) ∈ closure (connectedComponent (⟨x, hxA⟩ : A)) := by
        rw [closure_subtype, himage]
        exact hz.1
      have hz'' : (⟨z, hz.2⟩ : A) ∈ connectedComponent (⟨x, hxA⟩ : A) := by
        rwa [isClosed_connectedComponent.closure_eq] at hz'
      rw [← himage]
      exact ⟨⟨z, hz.2⟩, hz'', rfl⟩
    have hball : Metric.ball p r ⊆ closure C := by
      have hd : Metric.ball p r ⊆ closure B := by
        simpa only [B, Set.sdiff_eq] using
          (dense_compl_singleton p).open_subset_closure_inter Metric.isOpen_ball
      exact hd.trans (closure_mono hBC)
    have hclosed : closure (C ∪ Metric.ball p r) ∩ U ⊆ C ∪ Metric.ball p r := by
      intro z hz
      by_cases hzball : z ∈ Metric.ball p r
      · exact Or.inr hzball
      · left
        have hzC : z ∈ closure C :=
          closure_minimal (Set.union_subset subset_closure hball) isClosed_closure hz.1
        have hzp : z ≠ p := by
          intro heq
          apply hzball
          simpa [heq] using hr
        exact hCclosed ⟨hzC, hz.2, by simpa using hzp⟩
    have hUsub : U ⊆ C ∪ Metric.ball p r :=
      hconn.subset_of_closure_inter_subset (hCopen.union Metric.isOpen_ball)
        ⟨p, hp, Or.inr (Metric.mem_ball_self hr)⟩ hclosed
    have hAC : A ⊆ C := by
      intro z hz
      rcases hUsub hz.1 with hzC | hzB
      · exact hzC
      · exact hBC ⟨hzB, hz.2⟩
    have heq : A = C := Set.Subset.antisymm hAC (connectedComponentIn_subset A x)
    rw [show U \ {p} = C from heq]
    exact isPreconnected_connectedComponentIn
  · have heq : U \ {p} = U := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · exact And.left
      · intro hz
        exact ⟨hz, fun h => hp (h ▸ hz)⟩
    rw [heq]
    exact hconn

/-- Components of an open plane region are unchanged away from a removed point. -/
theorem IsOpen.connectedComponentIn_diff_singleton {U : Set Plane} (hU : IsOpen U)
    {x p : Plane} (hx : x ∈ U) (hxp : x ≠ p) :
    connectedComponentIn (U \ {p}) x = connectedComponentIn U x \ {p} := by
  apply Set.Subset.antisymm
  · intro z hz
    exact ⟨connectedComponentIn_mono x Set.sdiff_subset hz,
      (connectedComponentIn_subset (U \ {p}) x hz).2⟩
  · apply (IsOpen.isPreconnected_diff_singleton hU.connectedComponentIn
      isPreconnected_connectedComponentIn p).subset_connectedComponentIn
    · exact ⟨mem_connectedComponentIn hx, by simpa using hxp⟩
    · exact Set.sdiff_subset_sdiff_left (connectedComponentIn_subset U x)

private theorem component_mk_eq_iff {U : Set Plane} (x y : U) :
    ConnectedComponents.mk x = ConnectedComponents.mk y ↔
      x.val ∈ connectedComponentIn U y.val := by
  rw [ConnectedComponents.coe_eq_coe', connectedComponentIn_eq_image y.property]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have : z = x := Subtype.ext hzx
    exact this ▸ hz

/-- Inclusion after deleting one point induces an equivalence of components. -/
noncomputable def IsOpen.componentsDiffSingleton {U : Set Plane} (hU : IsOpen U)
    (p : Plane) : ConnectedComponents ↥(U \ {p}) ≃ ConnectedComponents U := by
  let f : ↥(U \ {p}) → U := fun x => ⟨x.val, x.property.1⟩
  have heq : ∀ x y : ↥(U \ {p}),
      ConnectedComponents.mk (f x) = ConnectedComponents.mk (f y) ↔
        ConnectedComponents.mk x = ConnectedComponents.mk y := by
    intro x y
    rw [component_mk_eq_iff, component_mk_eq_iff,
      IsOpen.connectedComponentIn_diff_singleton hU y.property.1 (by simpa using y.property.2)]
    simp only [f, Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨h, by simpa using x.property.2⟩, And.left⟩
  let g : ConnectedComponents ↥(U \ {p}) → ConnectedComponents U := fun F =>
    Quotient.liftOn F (fun x => ConnectedComponents.mk (f x)) (by
      intro x y hxy
      apply (heq x y).mpr
      exact Quotient.sound hxy)
  have hg : ∀ x : ↥(U \ {p}), g (ConnectedComponents.mk x) = ConnectedComponents.mk (f x) :=
    fun _ => rfl
  apply Equiv.ofBijective g
  constructor
  · intro F G hFG
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe F
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe G
    apply (heq x y).mp
    simpa only [hg] using hFG
  · intro F
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe F
    by_cases hy : y.val = p
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU.connectedComponentIn y.val
        (mem_connectedComponentIn y.property)
      obtain ⟨z, hz⟩ := (isPathConnected_ball_diff_singleton y.val hr).nonempty
      have hzcomp : z ∈ connectedComponentIn U y.val := hball hz.1
      have hzU : z ∈ U := connectedComponentIn_subset U y.val hzcomp
      let z' : ↥(U \ {p}) := ⟨z, hzU, by simpa only [← hy] using hz.2⟩
      refine ⟨ConnectedComponents.mk z', ?_⟩
      rw [hg, component_mk_eq_iff]
      exact hzcomp
    · let y' : ↥(U \ {p}) := ⟨y.val, y.property, by simpa using hy⟩
      refine ⟨ConnectedComponents.mk y', ?_⟩
      rw [hg, component_mk_eq_iff]
      exact mem_connectedComponentIn y.property

@[simp] theorem IsOpen.componentsDiffSingleton_mk {U : Set Plane} (hU : IsOpen U)
    (p : Plane) (x : ↥(U \ {p})) :
    IsOpen.componentsDiffSingleton hU p (ConnectedComponents.mk x) =
      ConnectedComponents.mk (⟨x.val, x.property.1⟩ : U) := rfl

/-- Removing a point and restricting to a set commute as subspace homeomorphisms. -/
def puncturedSetHomeomorph (U : Set Plane) (p : Plane) :
    ↥(U \ {p}) ≃ₜ {z : {z : Plane // z ≠ p} // z.val ∈ U} where
  toFun z := ⟨⟨z.val, by simpa using z.property.2⟩, z.property.1⟩
  invFun z := ⟨z.val.val, z.property, by simpa using z.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- A homeomorphism induces an equivalence of connected components. -/
noncomputable def homeomorphComponents {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y := by
  have hf : ∀ y, IsConnected (h ⁻¹' {y}) := by
    intro y
    have heq : h ⁻¹' {y} = {h.symm y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact h.toEquiv.eq_symm_apply.symm
    rw [heq]
    exact isConnected_singleton
  exact (h.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hf).toEquiv

@[simp] theorem homeomorphComponents_mk {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (x : X) :
    homeomorphComponents h (ConnectedComponents.mk x) = ConnectedComponents.mk (h x) := by
  simp [homeomorphComponents, Topology.IsCoinducing.connectedComponentsHomeomorph_mk]

/-- The trace of a finite drawing is compact. -/
theorem drawingTrace_isCompact (D : Drawing J) : IsCompact (drawingTrace D) :=
  (Set.finite_range D.point).isCompact.union
    (isCompact_iUnion fun e => isCompact_range (D.continuous e))

/-- The trace of a finite drawing is closed. -/
theorem drawingTrace_isClosed (D : Drawing J) : IsClosed (drawingTrace D) :=
  (drawingTrace_isCompact D).isClosed

private theorem arc_ball_contra {a b : ℝ} (f : Icc a b → Plane) (hf : Continuous f)
    (hi : Function.Injective f) {r : ℝ} (hr : 0 < r)
    (t l u : Icc a b) (hlt : l.val < t.val) (htu : t.val < u.val)
    (hl : f l ∈ Metric.ball (f t) r) (hu : f u ∈ Metric.ball (f t) r)
    (hball : Metric.ball (f t) r ⊆ range f) : False := by
  let A := Metric.ball (f t) r \ {f t}
  have hconn : IsPreconnected (f ⁻¹' A) :=
    (isPathConnected_ball_diff_singleton (f t) hr).isConnected.isPreconnected.preimage_of_isClosedMap
      hi hf.isClosedMap (fun x hx => hball hx.1)
  have hconn' : IsPreconnected ((Subtype.val : Icc a b → ℝ) '' (f ⁻¹' A)) :=
    hconn.image _ continuous_subtype_val.continuousOn
  have hl' : l.val ∈ (Subtype.val : Icc a b → ℝ) '' (f ⁻¹' A) := by
    refine ⟨l, ⟨hl, ?_⟩, rfl⟩
    simpa only [mem_singleton_iff] using (fun h : f l = f t => (ne_of_lt hlt) (congrArg Subtype.val (hi h)))
  have hu' : u.val ∈ (Subtype.val : Icc a b → ℝ) '' (f ⁻¹' A) := by
    refine ⟨u, ⟨hu, ?_⟩, rfl⟩
    simpa only [mem_singleton_iff] using (fun h : f u = f t => (ne_of_gt htu) (congrArg Subtype.val (hi h)))
  have ht' := hconn'.ordConnected.out hl' hu' ⟨hlt.le, htu.le⟩
  obtain ⟨v, hv, hv'⟩ := ht'
  have : v = t := Subtype.ext hv'
  subst v
  exact hv.2 (by simp)


private theorem compact_arc_interior {a b : ℝ} (hab : a < b) (f : Icc a b → Plane)
    (hf : Continuous f) (hi : Function.Injective f) : interior (range f) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  let a' : Icc a b := ⟨a, ⟨le_refl _, hab.le⟩⟩
  let b' : Icc a b := ⟨b, ⟨hab.le, le_refl _⟩⟩
  have hd : Dense ((Set.univ : Set Plane) \ {f a', f b'}) :=
    dense_univ.sdiff_finite (Set.toFinite _)
  obtain ⟨y, hy, hyend⟩ := hd.inter_open_nonempty (Metric.ball x r) Metric.isOpen_ball
    ⟨x, Metric.mem_ball_self hr⟩
  have hyRange : y ∈ range f := interior_subset (hrsub hy)
  obtain ⟨t, rfl⟩ := hyRange
  have hta : a < t.val := by
    have hne : t.val ≠ a := by
      intro h
      have : t = a' := Subtype.ext h
      subst t
      exact hyend.2 (by simp)
    exact lt_of_le_of_ne t.property.1 (Ne.symm hne)
  have htb : t.val < b := by
    have hne : t.val ≠ b := by
      intro h
      have : t = b' := Subtype.ext h
      subst t
      exact hyend.2 (by simp)
    exact lt_of_le_of_ne t.property.2 hne
  obtain ⟨q, hq, hqsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball (f t) hy
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hf.continuousAt q hq
  let d : ℝ := min ((t.val - a)/2) (min ((b - t.val)/2) (δ/2))
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hda : d ≤ (t.val - a)/2 := min_le_left _ _
  have hdb : d ≤ (b - t.val)/2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hdd : d ≤ δ/2 := le_trans (min_le_right _ _) (min_le_right _ _)
  let l : Icc a b := ⟨t.val - d, ⟨by linarith, by linarith [t.property.2]⟩⟩
  let u : Icc a b := ⟨t.val + d, ⟨by linarith [t.property.1], by linarith⟩⟩
  have hld : dist l t < δ := by
    change dist (t.val - d) t.val < δ
    rw [Real.dist_eq, show t.val - d - t.val = -d by ring, abs_neg, abs_of_pos hdpos]
    linarith
  have hud : dist u t < δ := by
    change dist (t.val + d) t.val < δ
    rw [Real.dist_eq, show t.val + d - t.val = d by ring, abs_of_pos hdpos]
    linarith
  exact arc_ball_contra f hf hi hq t l u (by dsimp [l]; linarith)
    (by dsimp [u]; linarith) (hδf hld) (hδf hud)
    (fun z hz => interior_subset (hrsub (hqsub hz)))

/-- The trace of a finite drawing has empty interior. -/
theorem drawingTrace_interior_eq_empty (D : Drawing J) : interior (drawingTrace D) = ∅ := by
  let f (e : E) (t : Icc (0 : ℝ) (1/2)) : Plane :=
    D.curve e ⟨t.val, ⟨t.property.1, by linarith [t.property.2]⟩⟩
  let g (e : E) (t : Icc (1/2 : ℝ) 1) : Plane :=
    D.curve e ⟨t.val, ⟨by linarith [t.property.1], t.property.2⟩⟩
  have hf (e : E) : Continuous (f e) := by
    exact (D.continuous e).comp (continuous_subtype_val.subtype_mk _)
  have hg (e : E) : Continuous (g e) := by
    exact (D.continuous e).comp (continuous_subtype_val.subtype_mk _)
  have hfi (e : E) : Function.Injective (f e) := by
    intro s t h
    apply Subtype.ext
    have h' := D.injective e (show (⟨s.val, ⟨s.property.1, by linarith [s.property.2]⟩⟩ : ArcParameter) ∈ {t | t.val < 1} by change s.val < (1 : ℝ); linarith [s.property.2])
      (show (⟨t.val, ⟨t.property.1, by linarith [t.property.2]⟩⟩ : ArcParameter) ∈ {t | t.val < 1} by change t.val < (1 : ℝ); linarith [t.property.2]) h
    exact congrArg (fun x : ArcParameter => x.val) h'
  have hgi (e : E) : Function.Injective (g e) := by
    intro s t h
    apply Subtype.ext
    by_cases hs : s.val = 1
    · by_cases ht : t.val = 1
      · exact hs.trans ht.symm
      · have ht1 : t.val < 1 := lt_of_le_of_ne t.property.2 ht
        have htp : 0 < t.val := by linarith [t.property.1]
        have hfinish := D.finish e
        have havoid := D.avoids e ⟨t.val, ⟨by linarith [t.property.1], t.property.2⟩⟩ htp ht1 (J.right e)
        have hseq : (⟨s.val, ⟨by linarith [s.property.1], s.property.2⟩⟩ : ArcParameter) = ⟨1, by norm_num⟩ := Subtype.ext hs
        exact (havoid (by rw [← hfinish, ← hseq]; exact h.symm)).elim
    · by_cases ht : t.val = 1
      · have hs1 : s.val < 1 := lt_of_le_of_ne s.property.2 hs
        have hsp : 0 < s.val := by linarith [s.property.1]
        have hfinish := D.finish e
        have havoid := D.avoids e ⟨s.val, ⟨by linarith [s.property.1], s.property.2⟩⟩ hsp hs1 (J.right e)
        have hteq : (⟨t.val, ⟨by linarith [t.property.1], t.property.2⟩⟩ : ArcParameter) = ⟨1, by norm_num⟩ := Subtype.ext ht
        exact (havoid (by rw [← hfinish, ← hteq]; exact h)).elim
      · have h' := D.injective e (show (⟨s.val, ⟨by linarith [s.property.1], s.property.2⟩⟩ : ArcParameter) ∈ {t | t.val < 1} by change s.val < (1 : ℝ); exact lt_of_le_of_ne s.property.2 hs)
          (show (⟨t.val, ⟨by linarith [t.property.1], t.property.2⟩⟩ : ArcParameter) ∈ {t | t.val < 1} by change t.val < (1 : ℝ); exact lt_of_le_of_ne t.property.2 ht) h
        exact congrArg (fun x : ArcParameter => x.val) h'
  have hn1 (e : E) : IsNowhereDense (range (f e)) := by
    have hc : IsClosed (range (f e)) := by simpa using (hf e).isClosedMap _ isClosed_univ
    apply hc.isNowhereDense_iff.mpr
    simpa using compact_arc_interior (by norm_num : (0 : ℝ) < 1/2) (f e) (hf e) (hfi e)
  have hn2 (e : E) : IsNowhereDense (range (g e)) := by
    have hc : IsClosed (range (g e)) := by simpa using (hg e).isClosedMap _ isClosed_univ
    apply hc.isNowhereDense_iff.mpr
    simpa using compact_arc_interior (by norm_num : (1/2 : ℝ) < 1) (g e) (hg e) (hgi e)
  have hnv : IsNowhereDense (range D.point) := by
    have hclosed : IsClosed (range D.point) := (Set.finite_range _).isClosed
    apply hclosed.isNowhereDense_iff.mpr
    have hd : Dense (range D.point)ᶜ := by
      simpa [Set.sdiff_eq] using (dense_univ.sdiff_finite (Set.finite_range D.point))
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨y, hy, hyn⟩ := hd.inter_open_nonempty (interior (range D.point)) isOpen_interior ⟨x, hx⟩
    exact hyn (interior_subset hy)
  have hn : IsNowhereDense (range D.point ∪ ⋃ e, (range (f e) ∪ range (g e))) :=
    nowhereDense_union hnv (nowhereDense_iUnion _ fun e => nowhereDense_union (hn1 e) (hn2 e))
  have hsub : drawingTrace D ⊆ range D.point ∪ ⋃ e, (range (f e) ∪ range (g e)) := by
    rintro z (hz | hz)
    · exact Or.inl hz
    · obtain ⟨e, t, rfl⟩ := Set.mem_iUnion.mp hz
      right
      apply Set.mem_iUnion.mpr
      refine ⟨e, ?_⟩
      by_cases ht : t.val ≤ 1/2
      · left
        exact ⟨⟨t.val, t.property.1, ht⟩, rfl⟩
      · right
        exact ⟨⟨t.val, le_of_not_ge ht, t.property.2⟩, rfl⟩
  have hresult := hn.mono hsub
  exact (drawingTrace_isClosed D).isNowhereDense_iff.mp hresult


/-- A face region is the complement component of any of its representatives. -/
theorem faceRegion_mk (D : Drawing J) (a : {z : Plane // z ∉ drawingTrace D}) :
    BSST.faceRegion D (ConnectedComponents.mk a) =
      connectedComponentIn (drawingTrace D)ᶜ a.val := by
  rw [connectedComponentIn_eq_image a.property]
  ext z
  constructor
  · rintro ⟨hz, he⟩
    exact ⟨⟨z, hz⟩, ConnectedComponents.coe_eq_coe'.mp he, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.property, ConnectedComponents.coe_eq_coe'.mpr hb⟩

/-- Each face of a finite drawing is an open subset of the plane. -/
theorem punctured_faceRegion_isOpen (D : Drawing J) (F : BSST.Face D) : IsOpen (BSST.faceRegion D F) := by
  obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe F
  rw [faceRegion_mk]
  exact (drawingTrace_isClosed D).isOpen_compl.connectedComponentIn

/-- Each face region is connected. -/
theorem faceRegion_isConnected (D : Drawing J) (F : BSST.Face D) :
    IsConnected (BSST.faceRegion D F) := by
  obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe F
  rw [faceRegion_mk]
  exact isConnected_connectedComponentIn_iff.mpr a.property

/-- Every face region contains a point. -/
theorem faceRegion_nonempty (D : Drawing J) (F : BSST.Face D) :
    (BSST.faceRegion D F).Nonempty := by
  obtain ⟨a, ha⟩ := ConnectedComponents.surjective_coe F
  exact ⟨a.val, a.property, ha⟩

/-- An open face meets the complement of a drawing whose trace has empty interior. -/
theorem exists_mem_faceRegion_not_mem_trace (D : Drawing J) {E₀ : Type} [Fintype E₀]
    {K : CopiedGraph V E₀} (R : Drawing K) (F : BSST.Face R)
    (hD : interior (drawingTrace D) = ∅) :
    ∃ p ∈ BSST.faceRegion R F, p ∉ drawingTrace D := by
  by_contra h
  push Not at h
  have hs : BSST.faceRegion R F ⊆ interior (drawingTrace D) :=
    interior_maximal h (punctured_faceRegion_isOpen R F)
  obtain ⟨p, hp⟩ := faceRegion_nonempty R F
  have : p ∈ (∅ : Set Plane) := hD ▸ hs hp
  exact this

/-- Translation to the origin followed by complex inversion on the punctured plane. -/
noncomputable def puncturedInversion (p : Plane) :
    {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)} := by
  let h : Plane ≃ₜ ℂ := (Homeomorph.addRight (-p)).trans
    Complex.equivRealProdCLM.symm.toHomeomorph
  let h₀ : Plane ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  have hp : ∀ z : Plane, z ≠ p ↔ h z ≠ 0 := by
    intro z
    have hpp : h p = 0 := by simp [h]
    rw [← hpp, h.injective.ne_iff]
  have hzero : ∀ z : Plane, z ≠ (0, 0) ↔ h₀ z ≠ 0 := by
    intro z
    have hz : h₀ (0, 0) = 0 := by simp [h₀]
    rw [← hz, h₀.injective.ne_iff]
  exact (h.subtype hp).trans ((Homeomorph.inv₀ ℂ).trans (h₀.subtype hzero).symm)

/-- The coordinate formula for punctured complex inversion. -/
theorem puncturedInversion_apply (p : Plane) (z : {z : Plane // z ≠ p}) :
    (puncturedInversion p z).val =
      ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
       -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2)) := by
  ext <;> simp [puncturedInversion, Homeomorph.inv₀, Homeomorph.subtype, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, sub_eq_add_neg, pow_two]

/-- A vertex of a drawing avoids every point outside the drawing trace. -/
theorem point_ne_of_not_mem_trace (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D) (v : V) : D.point v ≠ p := by
  intro h
  apply hp
  exact h ▸ (Or.inl (Set.mem_range_self v) : D.point v ∈ drawingTrace D)

/-- Every point of a drawn curve avoids every point outside the drawing trace. -/
theorem curve_ne_of_not_mem_trace (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D) (e : E) (t : ArcParameter) : D.curve e t ≠ p := by
  intro h
  apply hp
  exact h ▸ (Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_range_self t⟩) :
    D.curve e t ∈ drawingTrace D)

/-- Transport a drawing through a homeomorphism of punctured planes. -/
def Drawing.puncturedMap (D : Drawing J) {p : Plane} (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)}) : Drawing J where
  point v := (c ⟨D.point v, point_ne_of_not_mem_trace D hp v⟩).val
  point_injective := by
    intro v w h
    apply D.point_injective
    have hc := c.injective (Subtype.ext h)
    exact congrArg Subtype.val hc
  curve e t := (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).val
  continuous e := continuous_subtype_val.comp (c.continuous.comp
    ((D.continuous e).subtype_mk _))
  injective e := by
    intro s hs t ht h
    apply D.injective e hs ht
    exact congrArg Subtype.val (c.injective (Subtype.ext h))
  start e := congrArg (fun x => (c x).val) (Subtype.ext (D.start e))
  finish e := congrArg (fun x => (c x).val) (Subtype.ext (D.finish e))
  avoids e t h0 h1 v h := by
    apply D.avoids e t h0 h1 v
    exact congrArg Subtype.val (c.injective (Subtype.ext h))
  intersects e f hef s t h := by
    apply D.intersects e f hef s t
    exact congrArg Subtype.val (c.injective (Subtype.ext h))

/-- The image drawing avoids the origin. -/
theorem Drawing.puncturedMap_zero_not_mem_trace (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)}) :
    (0, 0) ∉ drawingTrace (D.puncturedMap hp c) := by
  rintro (⟨v, hv⟩ | h)
  · exact (c ⟨D.point v, point_ne_of_not_mem_trace D hp v⟩).property hv
  · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp h
    exact (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).property ht

/-- A punctured homeomorphism carries the trace onto the transported trace. -/
theorem Drawing.mem_trace_puncturedMap_iff (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (z : {z : Plane // z ≠ p}) :
    (c z).val ∈ drawingTrace (D.puncturedMap hp c) ↔ z.val ∈ drawingTrace D := by
  constructor
  · rintro (⟨v, hv⟩ | h)
    · left
      refine ⟨v, ?_⟩
      exact congrArg Subtype.val (c.injective (Subtype.ext hv))
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp h
      right
      refine Set.mem_iUnion.mpr ⟨e, t, ?_⟩
      exact congrArg Subtype.val (c.injective (Subtype.ext ht))
  · rintro (⟨v, hv⟩ | h)
    · left
      refine ⟨v, ?_⟩
      exact congrArg (fun x => (c x).val) (Subtype.ext hv)
    · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp h
      right
      refine Set.mem_iUnion.mpr ⟨e, t, ?_⟩
      exact congrArg (fun x => (c x).val) (Subtype.ext ht)

/-- Closure relations along any subset of a curve survive punctured transport. -/
theorem Drawing.puncturedMap_curve_mem_closure_iff (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (e : E) (S : Set ArcParameter) (t : ArcParameter) :
    D.curve e t ∈ closure (D.curve e '' S) ↔
      (D.puncturedMap hp c).curve e t ∈ closure ((D.puncturedMap hp c).curve e '' S) := by
  let f : ArcParameter → {z : Plane // z ≠ p} :=
    fun t => ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩
  have h₁ : (Subtype.val : {z : Plane // z ≠ p} → Plane) '' (f '' S) =
      D.curve e '' S := by rw [Set.image_image]
  have h₂ : (Subtype.val : {z : Plane // z ≠ (0, 0)} → Plane) '' (c '' (f '' S)) =
      (D.puncturedMap hp c).curve e '' S := by
    rw [Set.image_image, Set.image_image]
    rfl
  have hc : f t ∈ closure (f '' S) ↔ c (f t) ∈ closure (c '' (f '' S)) := by
    rw [← c.image_closure]
    exact ⟨fun h => ⟨f t, h, rfl⟩, fun ⟨x, hx, heq⟩ => c.injective heq ▸ hx⟩
  rw [closure_subtype, h₁, closure_subtype, h₂] at hc
  exact hc

/-- The punctured homeomorphism restricts to the complements of the two traces. -/
def Drawing.puncturedMap_complement (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)}) :
    {z : {z : Plane // z ≠ p} // z.val ∉ drawingTrace D} ≃ₜ
      {z : {z : Plane // z ≠ (0, 0)} // z.val ∉ drawingTrace (D.puncturedMap hp c)} :=
  c.subtype fun z => (D.mem_trace_puncturedMap_iff hp c z).not.symm

/-- A homeomorphism of trace complements induces an equivalence of their components. -/
noncomputable def Drawing.puncturedMap_components (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)}) :
    ConnectedComponents {z : {z : Plane // z ≠ p} // z.val ∉ drawingTrace D} ≃
      ConnectedComponents {z : {z : Plane // z ≠ (0, 0)} //
        z.val ∉ drawingTrace (D.puncturedMap hp c)} := by
  let h := D.puncturedMap_complement hp c
  have hf : ∀ y, IsConnected (h ⁻¹' {y}) := by
    intro y
    have heq : h ⁻¹' {y} = {h.symm y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact h.toEquiv.eq_symm_apply.symm
    rw [heq]
    exact isConnected_singleton
  exact (h.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hf).toEquiv

/-- A punctured homeomorphism induces an equivalence of the drawing's faces. -/
noncomputable def Drawing.puncturedMap_faces (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)}) :
    BSST.Face D ≃ BSST.Face (D.puncturedMap hp c) := by
  let U := (drawingTrace D)ᶜ
  let U' := (drawingTrace (D.puncturedMap hp c))ᶜ
  have hU : IsOpen U := (drawingTrace_isClosed D).isOpen_compl
  have hU' : IsOpen U' := (drawingTrace_isClosed (D.puncturedMap hp c)).isOpen_compl
  exact (IsOpen.componentsDiffSingleton hU p).symm |>.trans
    (homeomorphComponents (puncturedSetHomeomorph U p)) |>.trans
    (homeomorphComponents (D.puncturedMap_complement hp c)) |>.trans
    (homeomorphComponents (puncturedSetHomeomorph U' (0, 0))).symm |>.trans
    (IsOpen.componentsDiffSingleton hU' (0, 0))

/-- The face map sends the component of each punctured point to its image component. -/
theorem Drawing.puncturedMap_faces_mk (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (z : {z : Plane // z ≠ p}) (hz : z.val ∉ drawingTrace D) :
    D.puncturedMap_faces hp c (ConnectedComponents.mk ⟨z.val, hz⟩) =
      ConnectedComponents.mk ⟨(c z).val, (D.mem_trace_puncturedMap_iff hp c z).not.mpr hz⟩ := by
  let U := (drawingTrace D)ᶜ
  let U' := (drawingTrace (D.puncturedMap hp c))ᶜ
  have hU : IsOpen U := (drawingTrace_isClosed D).isOpen_compl
  have hU' : IsOpen U' := (drawingTrace_isClosed (D.puncturedMap hp c)).isOpen_compl
  let x : ↥(U \ {p}) := ⟨z.val, hz, by simpa using z.property⟩
  let y : ↥(U' \ {(0, 0)}) :=
    ⟨(c z).val, (D.mem_trace_puncturedMap_iff hp c z).not.mpr hz,
      by simpa using (c z).property⟩
  have hx : (IsOpen.componentsDiffSingleton hU p).symm
      (ConnectedComponents.mk ⟨z.val, hz⟩) = ConnectedComponents.mk x := by
    apply (IsOpen.componentsDiffSingleton hU p).injective
    simp [x]
  have hy : (homeomorphComponents (puncturedSetHomeomorph U' (0, 0))).symm
      (ConnectedComponents.mk ((D.puncturedMap_complement hp c) ⟨z, hz⟩)) =
        ConnectedComponents.mk y := by
    apply (homeomorphComponents (puncturedSetHomeomorph U' (0, 0))).injective
    rw [Equiv.apply_symm_apply, homeomorphComponents_mk]
    congr 1
  change (IsOpen.componentsDiffSingleton hU' (0, 0))
    ((homeomorphComponents (puncturedSetHomeomorph U' (0, 0))).symm
      (homeomorphComponents (D.puncturedMap_complement hp c)
        (homeomorphComponents (puncturedSetHomeomorph U p)
          ((IsOpen.componentsDiffSingleton hU p).symm (ConnectedComponents.mk ⟨z.val, hz⟩))))) = _
  rw [hx, homeomorphComponents_mk]
  change (IsOpen.componentsDiffSingleton hU' (0, 0))
    ((homeomorphComponents (puncturedSetHomeomorph U' (0, 0))).symm
      (homeomorphComponents (D.puncturedMap_complement hp c) (ConnectedComponents.mk ⟨z, hz⟩))) = _
  rw [homeomorphComponents_mk]
  change (IsOpen.componentsDiffSingleton hU' (0, 0))
    ((homeomorphComponents (puncturedSetHomeomorph U' (0, 0))).symm
      (ConnectedComponents.mk ((D.puncturedMap_complement hp c) ⟨z, hz⟩))) = _
  rw [hy]
  exact IsOpen.componentsDiffSingleton_mk hU' (0, 0) y

/-- The face equivalence transports membership at every point of the punctured plane. -/
theorem Drawing.mem_puncturedMap_faceRegion_iff (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (F : BSST.Face D) (z : {z : Plane // z ≠ p}) :
    z.val ∈ BSST.faceRegion D F ↔
      (c z).val ∈ BSST.faceRegion (D.puncturedMap hp c) (D.puncturedMap_faces hp c F) := by
  constructor
  · rintro ⟨hz, hF⟩
    refine ⟨(D.mem_trace_puncturedMap_iff hp c z).not.mpr hz, ?_⟩
    rw [← D.puncturedMap_faces_mk hp c z hz, hF]
  · rintro ⟨hz, hF⟩
    have hz' : z.val ∉ drawingTrace D := (D.mem_trace_puncturedMap_iff hp c z).not.mp hz
    refine ⟨hz', ?_⟩
    apply (D.puncturedMap_faces hp c).injective
    rw [D.puncturedMap_faces_mk hp c z hz']
    exact hF

private theorem closure_diff_singleton_of_isOpen {U : Set Plane} (hU : IsOpen U)
    (p : Plane) : closure (U \ {p}) = closure U := by
  apply Set.Subset.antisymm (closure_mono Set.sdiff_subset)
  apply closure_minimal _ isClosed_closure
  simpa only [Set.sdiff_eq] using (dense_compl_singleton p).open_subset_closure_inter hU

/-- Face closures correspond at every point of the punctured plane. -/
theorem Drawing.mem_closure_puncturedMap_faceRegion_iff (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (F : BSST.Face D) (z : {z : Plane // z ≠ p}) :
    z.val ∈ closure (BSST.faceRegion D F) ↔
      (c z).val ∈ closure (BSST.faceRegion (D.puncturedMap hp c) (D.puncturedMap_faces hp c F)) := by
  let A : Set {z : Plane // z ≠ p} := {z | z.val ∈ BSST.faceRegion D F}
  let B : Set {z : Plane // z ≠ (0, 0)} :=
    {z | z.val ∈ BSST.faceRegion (D.puncturedMap hp c) (D.puncturedMap_faces hp c F)}
  have hAB : c '' A = B := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (D.mem_puncturedMap_faceRegion_iff hp c F x).mp hx
    · intro hw
      change w.val ∈ BSST.faceRegion (D.puncturedMap hp c) (D.puncturedMap_faces hp c F) at hw
      refine ⟨c.symm w, ?_, c.apply_symm_apply w⟩
      apply (D.mem_puncturedMap_faceRegion_iff hp c F (c.symm w)).mpr
      simpa only [c.apply_symm_apply] using hw
  have hA : (Subtype.val : {z : Plane // z ≠ p} → Plane) '' A =
      BSST.faceRegion D F \ {p} := by
    ext w
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, A, Set.mem_setOf_eq]
    exact ⟨fun ⟨x, hx, he⟩ => ⟨he ▸ hx, he ▸ x.property⟩,
      fun ⟨hw, hwp⟩ => ⟨⟨w, hwp⟩, hw, rfl⟩⟩
  have hB : (Subtype.val : {z : Plane // z ≠ (0, 0)} → Plane) '' B =
      BSST.faceRegion (D.puncturedMap hp c) (D.puncturedMap_faces hp c F) \ {(0, 0)} := by
    ext w
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, B, Set.mem_setOf_eq]
    exact ⟨fun ⟨x, hx, he⟩ => ⟨he ▸ hx, he ▸ x.property⟩,
      fun ⟨hw, hw0⟩ => ⟨⟨w, hw0⟩, hw, rfl⟩⟩
  have hc : z ∈ closure A ↔ c z ∈ closure B := by
    rw [← hAB, ← c.image_closure]
    exact ⟨fun h => ⟨z, h, rfl⟩, fun ⟨x, hx, he⟩ => c.injective he ▸ hx⟩
  rw [closure_subtype, hA, closure_diff_singleton_of_isOpen (punctured_faceRegion_isOpen D F) p,
    closure_subtype, hB, closure_diff_singleton_of_isOpen
      (punctured_faceRegion_isOpen (D.puncturedMap hp c) (D.puncturedMap_faces hp c F)) (0, 0)] at hc
  exact hc

/-- Incidence of vertices with faces is preserved by punctured transport. -/
theorem Drawing.incident_puncturedMap_faces_iff (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    (F : BSST.Face D) (v : V) :
    BSST.incident D v F ↔ BSST.incident (D.puncturedMap hp c) v (D.puncturedMap_faces hp c F) :=
  D.mem_closure_puncturedMap_faceRegion_iff hp c F
    ⟨D.point v, point_ne_of_not_mem_trace D hp v⟩

/-- Inversion makes a face containing the puncture unbounded. -/
theorem Drawing.not_isBounded_puncturedInversion_face (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D) (F : BSST.Face D) (hpF : p ∈ BSST.faceRegion D F) :
    ¬ Bornology.IsBounded
      (BSST.faceRegion (D.puncturedMap hp (puncturedInversion p))
        (D.puncturedMap_faces hp (puncturedInversion p) F)) := by
  intro hb
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  obtain ⟨r, hr, hrF⟩ := Metric.isOpen_iff.mp (punctured_faceRegion_isOpen D F) p hpF
  let t : ℝ := max R r⁻¹ + 1
  have ht : 0 < t := by
    have : 0 < r⁻¹ := inv_pos.mpr hr
    dsimp [t]
    linarith [le_max_right R r⁻¹]
  have htR : R < t := by dsimp [t]; linarith [le_max_left R r⁻¹]
  have htr : t⁻¹ < r := by
    rw [inv_lt_comm₀ ht hr]
    dsimp [t]
    linarith [le_max_right R r⁻¹]
  let w : Plane := (p.1 + t⁻¹, p.2)
  have hwp : w ≠ p := by
    intro h
    have hfst := congrArg Prod.fst h
    dsimp [w] at hfst
    have : t⁻¹ = 0 := by linarith
    exact (inv_ne_zero ht.ne') this
  have hw : w ∈ BSST.faceRegion D F := by
    apply hrF
    rw [Metric.mem_ball]
    change dist (p.1 + t⁻¹, p.2) (p.1, p.2) < r
    rw [dist_prod_same_right, Real.dist_eq]
    simpa [abs_of_pos (inv_pos.mpr ht)] using htr
  let z : {z : Plane // z ≠ p} := ⟨w, hwp⟩
  have hc : (puncturedInversion p z).val = (t, 0) := by
    rw [puncturedInversion_apply]
    ext <;> simp only [z, w, add_sub_cancel_left, sub_self, neg_zero, zero_div]
    field_simp
    ring
  have hmem : (t, 0) ∈ BSST.faceRegion (D.puncturedMap hp (puncturedInversion p))
      (D.puncturedMap_faces hp (puncturedInversion p) F) := by
    rw [← hc]
    exact (D.mem_puncturedMap_faceRegion_iff hp (puncturedInversion p) F z).mp hw
  have hnorm := hR (t, 0) hmem
  simp only [Prod.norm_def, Real.norm_eq_abs, abs_of_pos ht, norm_zero, max_eq_left (le_of_lt ht)] at hnorm
  linarith

/-- Restricting the edges cannot enlarge a drawing's trace. -/
theorem drawingTrace_restrictDrawing_subset (D : Drawing J) {E₀ : Type} [Fintype E₀]
    {K : CopiedGraph V E₀} (i : E₀ → E) (hi : Function.Injective i)
    (hl : ∀ e, J.left (i e) = K.left e) (hr : ∀ e, J.right (i e) = K.right e) :
    drawingTrace (DrawingContraction.restrictDrawing D i hi hl hr) ⊆ drawingTrace D := by
  rintro z (⟨v, hv⟩ | h)
  · exact Or.inl ⟨v, hv⟩
  · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp h
    exact Or.inr (Set.mem_iUnion.mpr ⟨i e, t, ht⟩)

/-- Restricting a drawing commutes with applying a punctured homeomorphism. -/
theorem Drawing.puncturedMap_restrictDrawing (D : Drawing J) {p : Plane}
    (hp : p ∉ drawingTrace D)
    (c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)})
    {E₀ : Type} [Fintype E₀] {K : CopiedGraph V E₀} (i : E₀ → E)
    (hi : Function.Injective i) (hl : ∀ e, J.left (i e) = K.left e)
    (hr : ∀ e, J.right (i e) = K.right e) :
    (DrawingContraction.restrictDrawing D i hi hl hr).puncturedMap
        (fun h => hp (drawingTrace_restrictDrawing_subset D i hi hl hr h)) c =
      DrawingContraction.restrictDrawing (D.puncturedMap hp c) i hi hl hr := rfl


/-- Inversion transports a restricted drawing when the full trace has empty interior. -/
theorem Drawing.punctured_face_transport_of_interior_eq_empty (D : Drawing J)
    {E₀ : Type} [Fintype E₀] {K : CopiedGraph V E₀} (i : E₀ → E)
    (hi : Function.Injective i) (hl : ∀ e, J.left (i e) = K.left e)
    (hr : ∀ e, J.right (i e) = K.right e)
    (F : BSST.Face (DrawingContraction.restrictDrawing D i hi hl hr))
    (hD : interior (drawingTrace D) = ∅) :
    let R := DrawingContraction.restrictDrawing D i hi hl hr
    ∃ p : Plane, ∃ hp : p ∉ drawingTrace D,
      p ∈ BSST.faceRegion R F ∧
      ∃ c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)},
        (∀ z, (c z).val =
          ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
           -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) ∧
        ∃ D' : Drawing J,
          (∀ v, D'.point v = (c ⟨D.point v, point_ne_of_not_mem_trace D hp v⟩).val) ∧
          (∀ e t, D'.curve e t = (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).val) ∧
          let R' := DrawingContraction.restrictDrawing D' i hi hl hr
          ∃ faces : BSST.Face R ≃ BSST.Face R',
            (∀ G z, z.val ∈ BSST.faceRegion R G ↔ (c z).val ∈ BSST.faceRegion R' (faces G)) ∧
            (∀ G z, z.val ∈ closure (BSST.faceRegion R G) ↔
              (c z).val ∈ closure (BSST.faceRegion R' (faces G))) ∧
            (∀ G v, BSST.incident R v G ↔ BSST.incident R' v (faces G)) ∧
            (∀ e S t, D.curve e t ∈ closure (D.curve e '' S) ↔
              D'.curve e t ∈ closure (D'.curve e '' S)) ∧
            ¬Bornology.IsBounded (BSST.faceRegion R' (faces F)) := by
  dsimp only
  let R := DrawingContraction.restrictDrawing D i hi hl hr
  obtain ⟨p, hpF, hp⟩ := exists_mem_faceRegion_not_mem_trace D R F hD
  let hpR : p ∉ drawingTrace R := fun h => hp (drawingTrace_restrictDrawing_subset D i hi hl hr h)
  let c := puncturedInversion p
  refine ⟨p, hp, hpF, c, puncturedInversion_apply p, D.puncturedMap hp c, ?_, ?_, ?_⟩
  · intro v
    rfl
  · intro e t
    rfl
  · have hR : R.puncturedMap hpR c =
        DrawingContraction.restrictDrawing (D.puncturedMap hp c) i hi hl hr :=
      D.puncturedMap_restrictDrawing hp c i hi hl hr
    rw [← hR]
    refine ⟨R.puncturedMap_faces hpR c, ?_, ?_, ?_, ?_, ?_⟩
    · exact R.mem_puncturedMap_faceRegion_iff hpR c
    · exact R.mem_closure_puncturedMap_faceRegion_iff hpR c
    · exact R.incident_puncturedMap_faces_iff hpR c
    · exact D.puncturedMap_curve_mem_closure_iff hp c
    · exact R.not_isBounded_puncturedInversion_face hpR F hpF

/-- Inversion transports a restricted drawing and sends the chosen face to an unbounded face. -/
theorem Drawing.punctured_face_transport (D : Drawing J)
    {E₀ : Type} [Fintype E₀] {K : CopiedGraph V E₀} (i : E₀ → E)
    (hi : Function.Injective i) (hl : ∀ e, J.left (i e) = K.left e)
    (hr : ∀ e, J.right (i e) = K.right e)
    (F : BSST.Face (DrawingContraction.restrictDrawing D i hi hl hr))
    :
    let R := DrawingContraction.restrictDrawing D i hi hl hr
    ∃ p : Plane, ∃ hp : p ∉ drawingTrace D,
      p ∈ BSST.faceRegion R F ∧
      ∃ c : {z : Plane // z ≠ p} ≃ₜ {z : Plane // z ≠ (0, 0)},
        (∀ z, (c z).val =
          ((z.val.1 - p.1) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2),
           -(z.val.2 - p.2) / ((z.val.1 - p.1)^2 + (z.val.2 - p.2)^2))) ∧
        ∃ D' : Drawing J,
          (∀ v, D'.point v = (c ⟨D.point v, point_ne_of_not_mem_trace D hp v⟩).val) ∧
          (∀ e t, D'.curve e t = (c ⟨D.curve e t, curve_ne_of_not_mem_trace D hp e t⟩).val) ∧
          let R' := DrawingContraction.restrictDrawing D' i hi hl hr
          ∃ faces : BSST.Face R ≃ BSST.Face R',
            (∀ G z, z.val ∈ BSST.faceRegion R G ↔ (c z).val ∈ BSST.faceRegion R' (faces G)) ∧
            (∀ G z, z.val ∈ closure (BSST.faceRegion R G) ↔
              (c z).val ∈ closure (BSST.faceRegion R' (faces G))) ∧
            (∀ G v, BSST.incident R v G ↔ BSST.incident R' v (faces G)) ∧
            (∀ e S t, D.curve e t ∈ closure (D.curve e '' S) ↔
              D'.curve e t ∈ closure (D'.curve e '' S)) ∧
            ¬Bornology.IsBounded (BSST.faceRegion R' (faces F)) :=
  D.punctured_face_transport_of_interior_eq_empty i hi hl hr F (drawingTrace_interior_eq_empty D)

end FiniteAvalanches.Electrical.StatementGeometry
