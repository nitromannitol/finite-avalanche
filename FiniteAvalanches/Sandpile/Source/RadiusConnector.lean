import FiniteAvalanches.Sandpile.SourceCounting.RadiusReduction
import FiniteAvalanches.Trees.Lattice.TreeContinuityProvider
import FiniteAvalanches.Trees.Lattice.FiniteFixedCut
import FiniteAvalanches.Sandpile.Law.Characterization
import FiniteAvalanches.Probability.Radius.RealThresholds

/-! The fixed horizontal connector, transported through the actual copied law.
The four direction slots overcount the positive first horizontal edge once;
this only enlarges the nonnegative error sum. -/
namespace FiniteAvalanches.Sandpile.Source
open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
open SourceCounting Components Waves Trees.Lattice TreeMeasurability11
open FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal BigOperators
noncomputable section

/-- Literal original lattice edges indexed independently of the wired volume. -/
def connectorEdge (r : ℕ) : Fin r ⊕ FiniteWired.Direction → LatticeEdge
  | .inl k => baseEdge (axisSite k.val, 0)
  | .inr d => ⟨s((0 : Site2), FiniteWired.step d), by
      rcases d with ⟨i, b⟩
      cases b
      · exact ⟨i, Or.inr (by simp [FiniteWired.step])⟩
      · exact ⟨i, Or.inl (by simp [FiniteWired.step])⟩⟩

/-- The corresponding actual original copied edges, including direction IDs. -/
def connectorCopy (N r : ℕ) (hrN : r ≤ N) :
    Fin r ⊕ FiniteWired.Direction → FiniteWired.Edge N
  | .inl k => horizontalEdge N r hrN k
  | .inr d => FiniteWired.directionEdge (origin N) d

theorem original_connector_copy {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    (j : Fin r ⊕ FiniteWired.Direction) :
    originalCopyEdge (connectorCopy N r hrN j) = connectorEdge r j := by
  cases j with
  | inl k =>
    apply Subtype.ext
    change s(axisSite k.val, axisSite (k.val+1)) = s(axisSite k.val, axisSite k.val + unit 0)
    rw [axisSite_succ]
  | inr d =>
    rcases d with ⟨i, b⟩
    cases b
    · have hb : FiniteWired.inBox N (FiniteWired.site (origin N) - unit i) := by
        rw [site_origin, zero_sub]
        exact neg_unit_inBox (by omega) i
      change originalCopyEdge (FiniteWired.directionEdge (origin N) (i, false)) = _
      rw [FiniteWired.directionEdge, dif_pos hb]
      apply Subtype.ext
      simpa only [connectorEdge, originalCopyEdge, interiorEdge, site_origin, FiniteWired.site_activeOfSite,
        FiniteWired.step, Bool.false_eq_true, ite_false, zero_sub] using
        (Sym2.eq_swap : s((-unit i : Site2), 0) = s(0, -unit i))
    · have hb : FiniteWired.inBox N (FiniteWired.site (origin N) + unit i) := by
        rw [site_origin, zero_add]
        exact unit_inBox (by omega) i
      change originalCopyEdge (FiniteWired.directionEdge (origin N) (i, true)) = _
      rw [FiniteWired.directionEdge, dif_pos hb]
      apply Subtype.ext
      simp only [connectorEdge, originalCopyEdge, interiorEdge, site_origin,
        FiniteWired.site_activeOfSite, FiniteWired.step, ite_true, zero_add]

theorem sourceEdges_subset_connector_copies {N r : ℕ} (hrN : r ≤ N) :
    sourceEdges N r hrN ⊆ Finset.univ.image (connectorCopy N r hrN) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨Sum.inl k, Finset.mem_univ _, rfl⟩
  · simp only [otherSourceEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨Sum.inr (0, false), Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨Sum.inr (1, false), Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨Sum.inr (1, true), Finset.mem_univ _, rfl⟩

theorem finite_marks_eq (N r : ℕ) :
    markedVertices (activeMarks N r) = finiteMarks N (sourceMarks r) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Finset.mem_filter.mp hx).2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

theorem finite_reciprocal_eq_finiteZN {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N)
    (t : (WiredTrees.graph N).SpanningTree) :
    WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t =
      finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t := by
  rw [finiteZN, dif_pos (fun _ hx => sourceMarks_inBox hr hrN hx)]
  congr 1
  exact finite_marks_eq N r

theorem finite_radius_probability_le_connector {N r M : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (hMN : M + 1 ≤ N) :
    (FiniteWired.finiteFieldLaw N).real {η | (M : WithTop ℕ) < radius η 0} ≤
      (∫ t, finiteZN N (sourceMarks r) (Finset.insert_nonempty _ _) t ∂WiredTrees.law N) +
      ∑ j : Fin r ⊕ FiniteWired.Direction,
        (WiredTrees.law N).real (finiteCutEscape 0 (connectorEdge r j) M N) := by
  have h := finiteFieldLaw_origin_radius_probability_le hr hrN hMN
  simp_rw [finite_reciprocal_eq_finiteZN hr hrN] at h
  refine h.trans (add_le_add le_rfl ?_)
  let b : FiniteWired.Edge N → ℝ := fun e => (WiredTrees.law N).real {t |
    e ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
      ¬cutSites (origin N) t e ⊆ boxSites M}
  calc
    ∑ e ∈ sourceEdges N r hrN, b e ≤
        ∑ e ∈ Finset.univ.image (connectorCopy N r hrN), b e :=
      Finset.sum_le_sum_of_subset_of_nonneg (sourceEdges_subset_connector_copies hrN)
        (fun _ _ _ => measureReal_nonneg)
    _ ≤ ∑ j : Fin r ⊕ FiniteWired.Direction, b (connectorCopy N r hrN j) :=
      Finset.sum_image_le_of_nonneg (fun _ _ => measureReal_nonneg)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      rintro t ⟨hp, hc⟩
      exact ⟨origin N, site_origin N, connectorCopy N r hrN j,
        original_connector_copy hr hrN j, hp, hc⟩

/-- Both tree limits are used at the same volume as the actual radius cylinder. -/
theorem infinite_radius_probability_le_connector {r M : ℕ} (hr : 2 ≤ r) :
    (infiniteVolumeLaw : Measure StableField).real {η | (M : WithTop ℕ) < radius η 0} ≤
      (∫ T, infiniteReciprocal (sourceMarks r) (Finset.insert_nonempty _ _) T ∂endedUST) +
      ∑ j : Fin r ⊕ FiniteWired.Direction,
        endedUST.real (infiniteCutEscape 0 (connectorEdge r j) M) := by
  have hμ := isInfiniteVolumeLaw_infiniteVolumeLaw.tendsto_boxes
  have hleft := (ENNReal.tendsto_toReal (measure_ne_top (infiniteVolumeLaw : Measure StableField) _)).comp
    (FiniteAvalanches.Probability.tendsto_radius_gt_of_weak infiniteVolumeLaw hμ 0 M)
  have hcuts : ∀ j : Fin r ⊕ FiniteWired.Direction,
      Tendsto (fun N : ℕ => (WiredTrees.law N).real
        (finiteCutEscape 0 (connectorEdge r j) M N)) atTop
        (nhds (endedUST.real (infiniteCutEscape 0 (connectorEdge r j) M))) := fun j =>
    (ENNReal.tendsto_toReal (measure_ne_top endedUST _)).comp
      (JointTreeContinuity.tree_continuity.2 0 (connectorEdge r j) M)
  apply le_of_tendsto_of_tendsto hleft
    ((JointTreeContinuity.tree_continuity.1 (sourceMarks r)
      (Finset.insert_nonempty _ _)).add (tendsto_finsetSum _ (fun j _ => hcuts j)))
  filter_upwards [eventually_ge_atTop r, eventually_ge_atTop (M+1)] with N hrN hMN
  exact finite_radius_probability_le_connector hr hrN hMN

#print axioms infinite_radius_probability_le_connector
#print axioms original_connector_copy
end
end FiniteAvalanches.Sandpile.Source
