import FiniteAvalanches.Support.Plane.PolarDualConnected
import FiniteAvalanches.Support.Plane.BoundaryIncidenceCount
import FiniteAvalanches.Support.Plane.BondDualCycle
import FiniteAvalanches.Electrical.Trees.PathUniqueCrossing
import FiniteAvalanches.Electrical.Trees.CopyDirections

/-!
# Face-boundary balance at bridge-only vertices

A bridge has the same dual face on both sides. Hence the face boundary of a
vertex-indicator gradient vanishes at any vertex incident only to bridges.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Plane Set
open scoped Classical BigOperators

variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- A non-loop edge on a cycle has a different non-loop cycle edge at its
first endpoint. Parallel edge copies are allowed. -/
theorem CopiedGraph.exists_other_incident_nonbridge (J : CopiedGraph V E)
    (e : E) (hne : J.left e ≠ J.right e)
    (hcycle : J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) :
    ∃ f : E, f ≠ e ∧ (J.left f = J.left e ∨ J.right f = J.left e) ∧
      J.left f ≠ J.right f ∧
      J.reaches (Finset.univ.erase f) (J.left f) (J.right f) := by
  classical
  obtain ⟨m, vertices, copies, hver, hfirst, hlast, hmem, hends⟩ :=
    J.exists_simple_ordered_path (Finset.univ.erase e) hcycle
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact hne (hfirst.symm.trans hlast)
  let i : Fin m := ⟨0, hm⟩
  let f := copies i
  have hfe : f ≠ e := (Finset.mem_erase.mp (hmem i)).1
  have hcopies := J.copies_injective_of_vertices_injective m vertices hver copies hends
  have hstart : vertices i.castSucc = J.left e := by
    rw [show i.castSucc = 0 from Fin.ext rfl]
    exact hfirst
  have hnext : vertices i.succ ≠ vertices i.castSucc := by
    intro h
    have hi := congrArg Fin.val (hver h)
    simp only [Fin.val_succ, Fin.val_castSucc] at hi
    omega
  have hsuffix : J.reaches (Finset.univ.erase f) (vertices i.succ)
      (vertices (Fin.last m)) := by
    apply J.path_interval_reaches (Finset.univ.erase f) m vertices i.succ (Fin.last m)
      (by simp only [Fin.val_succ, Fin.val_last]; omega)
    intro k hik _
    have hk : copies k ≠ f := by
      intro h
      have heq : k = i := hcopies h
      subst k
      simp only [Fin.val_succ] at hik
      omega
    exact .single ⟨copies k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩, hends k⟩
  have hepath : J.reaches (Finset.univ.erase f) (J.right e) (J.left e) :=
    .single ⟨e, Finset.mem_erase.mpr ⟨Ne.symm hfe, Finset.mem_univ _⟩,
      Or.inr ⟨rfl, rfl⟩⟩
  have halt : J.reaches (Finset.univ.erase f) (vertices i.succ) (vertices i.castSucc) := by
    rw [hlast] at hsuffix
    rw [hstart]
    exact hsuffix.trans hepath
  refine ⟨f, hfe, ?_, ?_, ?_⟩
  · rcases hends i with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact Or.inl (ha.trans hstart)
    · exact Or.inr (ha.trans hstart)
  · intro h
    rcases hends i with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hnext (hb.symm.trans (h.symm.trans ha))
    · exact hnext (hb.symm.trans (h.trans ha))
  · rcases hends i with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
      exact TwoCopy.reaches_symm J halt
    · rw [ha, hb]
      exact halt

omit [Fintype V] in
/-- Every endpoint of a non-loop cycle edge is incident to a second, distinct
non-loop cycle edge. -/
theorem CopiedGraph.exists_other_incident_nonbridge_of_mem (J : CopiedGraph V E)
    (e : E) (v : V) (hv : J.left e = v ∨ J.right e = v)
    (hne : J.left e ≠ J.right e)
    (hcycle : J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) :
    ∃ f : E, f ≠ e ∧ (J.left f = v ∨ J.right f = v) ∧
      J.left f ≠ J.right f ∧
      J.reaches (Finset.univ.erase f) (J.left f) (J.right f) := by
  classical
  rcases hv with hv | hv
  · obtain ⟨f, hfe, hf, hn, hc⟩ := J.exists_other_incident_nonbridge e hne hcycle
    exact ⟨f, hfe, by simpa only [hv] using hf, hn, hc⟩
  · let K := TwoCopy.reorient J (fun _ => true)
    have hn : K.left e ≠ K.right e := by
      simpa only [K, TwoCopy.reorient, ↓reduceIte] using hne.symm
    have hreaches (F : Finset E) : K.reaches F = J.reaches F :=
      TwoCopy.reorient_reaches J (fun _ => true) F
    have hc : K.reaches (Finset.univ.erase e) (K.left e) (K.right e) := by
      rw [hreaches]
      simpa only [K, TwoCopy.reorient, ↓reduceIte] using
        TwoCopy.reaches_symm J hcycle
    obtain ⟨f, hfe, hf, hfn, hfc⟩ := K.exists_other_incident_nonbridge e hn hc
    have hf' : J.left f = v ∨ J.right f = v := by
      simpa only [K, TwoCopy.reorient, ↓reduceIte, hv, or_comm] using hf
    have hfn' : J.left f ≠ J.right f := by
      simpa only [K, TwoCopy.reorient, ↓reduceIte] using hfn.symm
    have hfc' : J.reaches (Finset.univ.erase f) (J.left f) (J.right f) := by
      apply TwoCopy.reaches_symm J
      rw [hreaches] at hfc
      simpa only [K, TwoCopy.reorient, ↓reduceIte] using hfc
    exact ⟨f, hfe, hf', hfn', hfc'⟩

omit [Fintype V] in
/-- At each vertex, the number of incident non-loop cycle edges is either
zero or at least two. -/
theorem CopiedGraph.incident_nonbridge_card_ne_one (J : CopiedGraph V E) (v : V) :
    (Finset.univ.filter (fun e => (J.left e = v ∨ J.right e = v) ∧
      J.left e ≠ J.right e ∧
      J.reaches (Finset.univ.erase e) (J.left e) (J.right e))).card ≠ 1 := by
  classical
  let S := Finset.univ.filter (fun e => (J.left e = v ∨ J.right e = v) ∧
    J.left e ≠ J.right e ∧
    J.reaches (Finset.univ.erase e) (J.left e) (J.right e))
  intro hcard
  change S.card = 1 at hcard
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hnonempty
  have he' := (Finset.mem_filter.mp he).2
  obtain ⟨f, hfe, hv, hn, hc⟩ :=
    J.exists_other_incident_nonbridge_of_mem e v he'.1 he'.2.1 he'.2.2
  have hf : f ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hn, hc⟩
  have hlt : 1 < S.card := Finset.one_lt_card.mpr ⟨e, he, f, hf, Ne.symm hfe⟩
  omega

/-- The two chart sides of a bridge represent the same complementary face. -/
theorem chartFaces_eq_of_bridge {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (e : E)
    (hbridge : ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) :
    negativeChartFace D e (charts e) = positiveChartFace D e (charts e) := by
  classical
  letI : Nonempty E := ⟨e⟩
  have h := not_not.mp (mt (edge_path_duality D charts (Finset.univ.erase e) e
    (Finset.notMem_erase _ _)).mpr hbridge)
  have hs : (Finset.univ.erase e)ᶜ.erase e = (∅ : Finset E) := by
    ext f
    simp
  rw [hs] at h
  exact CopiedGraph.eq_of_reaches_empty _ h

/-- An edge is a bridge exactly when its two chart sides are in the same face. -/
theorem bridge_iff_chartFaces_eq {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (e : E) :
    (¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) ↔
      negativeChartFace D e (charts e) = positiveChartFace D e (charts e) := by
  classical
  constructor
  · exact chartFaces_eq_of_bridge D charts e
  · intro hface hreach
    letI : Nonempty E := ⟨e⟩
    have hnot := (edge_path_duality D charts (Finset.univ.erase e) e
      (Finset.notMem_erase _ _)).mp hreach
    apply hnot
    rw [hface]
    exact .refl

/-- If all but two crossing copies of a cut are bridges, the two chart
faces of a nonbridge crossing are the two chart faces of the other copy,
in one order or the other. -/
theorem chartFaces_eq_pair_of_two_nonbridges_in_cut {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e) (A : Finset V) (e f : E)
    (he : J.Crosses A e)
    (hcycle : J.reaches (Finset.univ.erase e) (J.left e) (J.right e))
    (hbridge : ∀ g, g ≠ e → g ≠ f → J.Crosses A g →
      ¬ J.reaches (Finset.univ.erase g) (J.left g) (J.right g)) :
    (negativeChartFace D e (charts e) = negativeChartFace D f (charts f) ∧
      positiveChartFace D e (charts e) = positiveChartFace D f (charts f)) ∨
    (negativeChartFace D e (charts e) = positiveChartFace D f (charts f) ∧
      positiveChartFace D e (charts e) = negativeChartFace D f (charts f)) := by
  classical
  let K : CopiedGraph (Face D) E := ⟨fun g => negativeChartFace D g (charts g),
    fun g => positiveChartFace D g (charts g)⟩
  let S := (Finset.univ.filter fun g => J.Crosses A g).erase e
  have hwalk : K.reaches S (K.left e) (K.right e) :=
    dual_reaches_other_cut_edges D charts A e he
  have hred {x y : Face D} (h : K.reaches S x y) : K.reaches {f} x y := by
    induction h with
    | refl => exact .refl
    | @tail u w _ hstep ih =>
      obtain ⟨g, hg, hends⟩ := hstep
      by_cases hgf : g = f
      · subst g
        exact ih.tail ⟨f, Finset.mem_singleton_self f, hends⟩
      · have hge : g ≠ e := (Finset.mem_erase.mp hg).1
        have hcross : J.Crosses A g := (Finset.mem_filter.mp (Finset.mem_erase.mp hg).2).2
        have hface : K.left g = K.right g := chartFaces_eq_of_bridge D charts g
          (hbridge g hge hgf hcross)
        have huw : u = w := by
          rcases hends with ⟨hu, hw⟩ | ⟨hu, hw⟩
          · exact hu.symm.trans (hface.trans hw)
          · exact hu.symm.trans (hface.symm.trans hw)
        simpa only [huw] using ih
  have hne : K.left e ≠ K.right e := by
    intro h
    exact ((bridge_iff_chartFaces_eq D charts e).mpr h) hcycle
  have hsingle : K.reaches (insert f ∅) (K.left e) (K.right e) := by
    exact hred hwalk
  rcases (CopiedGraph.TwoCopy.reaches_insert_iff K ∅ f (K.left e) (K.right e)).mp hsingle with
      h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact (hne (K.eq_of_reaches_empty h)).elim
  · exact Or.inl ⟨K.eq_of_reaches_empty h₁, (K.eq_of_reaches_empty h₂).symm⟩
  · exact Or.inr ⟨K.eq_of_reaches_empty h₁, (K.eq_of_reaches_empty h₂).symm⟩

/-- At a vertex incident only to bridges, every face has zero boundary of the
vertex-indicator gradient. -/
theorem indicator_face_boundary_eq_zero_of_incident_bridges {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e) (v : V)
    (hbridge : ∀ e : E, (J.left e = v ∨ J.right e = v) →
      ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e))
      (copyGradient J.left J.right (Pi.single v 1)) F = 0 := by
  classical
  unfold copyBoundary
  apply Finset.sum_eq_zero
  intro e _
  dsimp only
  by_cases he : J.left e = v ∨ J.right e = v
  · have heq := chartFaces_eq_of_bridge D charts e (hbridge e he)
    by_cases hn : negativeChartFace D e (charts e) = F
    · have hp : positiveChartFace D e (charts e) = F := heq.symm.trans hn
      simp only [hn, hp, if_true, sub_self]
    · have hp : positiveChartFace D e (charts e) ≠ F := fun h => hn (heq.trans h)
      simp only [hn, hp, if_false, sub_self]
  · have hl : v ≠ J.left e := fun h => he (Or.inl h.symm)
    have hr : v ≠ J.right e := fun h => he (Or.inr h.symm)
    simp [copyGradient, hl, hr]

/-- The dual boundary of every primal gradient vanishes in a forest drawing. -/
theorem face_boundary_gradient_eq_zero_of_forest {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e)
    (hforest : ∀ e : E, ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e))
    (q : V → ℝ) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e)) (copyGradient J.left J.right q) F = 0 := by
  apply ((copyBoundary_gradient_eq_zero_iff_indicators J.left J.right
    (fun e => negativeChartFace D e (charts e))
    (fun e => positiveChartFace D e (charts e))).mpr ?_) q F
  intro v G
  exact indicator_face_boundary_eq_zero_of_incident_bridges D charts v (fun e _ => hforest e) G


/-- For a vertex indicator, only incident non-loop edges whose chart sides
are distinct contribute to the dual boundary. -/
theorem indicator_face_boundary_eq_sum_relevant_edges {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e) (v : V) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e))
      (copyGradient J.left J.right (Pi.single v 1)) F =
    ∑ e ∈ Finset.univ.filter (fun e => (J.left e = v ∨ J.right e = v) ∧
        J.left e ≠ J.right e ∧
        J.reaches (Finset.univ.erase e) (J.left e) (J.right e)),
      ((if negativeChartFace D e (charts e) = F then
          copyGradient J.left J.right (Pi.single v 1) e else 0) -
       (if positiveChartFace D e (charts e) = F then
          copyGradient J.left J.right (Pi.single v 1) e else 0)) := by
  classical
  unfold copyBoundary
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e _ he
  have hn : ¬ ((J.left e = v ∨ J.right e = v) ∧
      J.left e ≠ J.right e ∧
      J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
  by_cases hi : J.left e = v ∨ J.right e = v
  · by_cases hl : J.left e = J.right e
    · simp only [copyGradient, hl, sub_self, ite_self]
    · have hb : ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e) :=
        fun h => hn ⟨hi, hl, h⟩
      have hf := chartFaces_eq_of_bridge D charts e hb
      rw [hf, sub_self]
  · have hl : v ≠ J.left e := fun h => hi (Or.inl h.symm)
    have hr : v ≠ J.right e := fun h => hi (Or.inr h.symm)
    simp [copyGradient, hl, hr]


/-- A vertex has zero indicator boundary when every incident non-loop edge
is a bridge; loops may be present. -/
theorem indicator_face_boundary_eq_zero_of_incident_nonloop_bridges {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e) (v : V)
    (hbridge : ∀ e : E, (J.left e = v ∨ J.right e = v) →
      J.left e ≠ J.right e →
      ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e)) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e))
      (copyGradient J.left J.right (Pi.single v 1)) F = 0 := by
  classical
  rw [indicator_face_boundary_eq_sum_relevant_edges]
  apply Finset.sum_eq_zero
  intro e he
  have he' := (Finset.mem_filter.mp he).2
  exact (hbridge e he'.1 he'.2.1 he'.2.2).elim

/-- The dual boundary of every gradient vanishes when all non-loop edges are
bridges, with arbitrary loop copies allowed. -/
theorem face_boundary_gradient_eq_zero_of_nonloop_bridges {J : CopiedGraph V E}
    (D : Drawing J) (charts : ∀ e, EdgeChart D e)
    (hbridge : ∀ e : E, J.left e ≠ J.right e →
      ¬ J.reaches (Finset.univ.erase e) (J.left e) (J.right e))
    (q : V → ℝ) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e)) (copyGradient J.left J.right q) F = 0 := by
  apply ((copyBoundary_gradient_eq_zero_iff_indicators J.left J.right
    (fun e => negativeChartFace D e (charts e))
    (fun e => positiveChartFace D e (charts e))).mpr ?_) q F
  intro v G
  exact indicator_face_boundary_eq_zero_of_incident_nonloop_bridges D charts v
    (fun e _ => hbridge e) G

end FiniteAvalanches.Electrical.StatementGeometry
