import FiniteAvalanches.Sandpile.Waves.FiniteRadius
import FiniteAvalanches.Sandpile.SourceCounting.CountingApplication
import FiniteAvalanches.Sandpile.SourceCounting.CountingGeometry

/-! The finite-volume radius reduction with the literal source marks and copies. -/
namespace FiniteAvalanches.Sandpile.SourceCounting
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators
noncomputable section

/-- The finite wired entire-avalanche radius is exactly the counting event. -/
theorem finite_origin_radius_gt_iff_leaves {N : ℕ}
    (η : FiniteWired.Recurrent N) (M : ℕ) :
    M < finiteAvalancheRadius (origin N) η ↔
      finiteAvalancheLeaves (origin N) (boxSites M) η := by
  simpa only [site_origin, add_zero, Finset.image_id'] using
    finite_avalanche_radius_gt_iff_leaves (origin N) η M

/-- The full radius event is an actual visit of the complete inverse excursion. -/
theorem finite_origin_radius_gt_iff_excursion {N : ℕ}
    (η : SourceThree N (origin N)) (M : ℕ) :
    M < finiteAvalancheRadius (origin N) η.val ↔
      ∃ j : Fin (returnTime (inputExcursion η)),
        ¬core (inverse^[j.val] (inputExcursion η).val).val ⊆ boxSites M :=
  (finite_origin_radius_gt_iff_leaves η.val M).trans
    (finite_avalanche_leaves_source_three (boxSites M) η)

/-- Every nonempty complete excursion has the mass of one original input. -/
theorem finite_origin_radius_probability_eq_excursion_count {N M : ℕ} :
    (FiniteWired.law N).real {η | M < finiteAvalancheRadius (origin N) η} =
      (∑ h : TerminalState N (origin N),
        (if ∃ j : Fin (returnTime h), ¬core (inverse^[j.val] h.val).val ⊆ boxSites M
          then 1 else 0 : ℝ)) / Fintype.card (FiniteWired.Recurrent N) := by
  have he : {η : FiniteWired.Recurrent N | M < finiteAvalancheRadius (origin N) η} =
      {η | finiteAvalancheLeaves (origin N) (boxSites M) η} := by
    ext η
    exact finite_origin_radius_gt_iff_leaves η M
  rw [he, ← integral_finite_avalanche_leaves]
  have hl : FiniteWired.law N = uniformMeasure (FiniteWired.Recurrent N) := by
    simp only [FiniteWired.law, uniformMeasure, Nat.card_eq_fintype_card]
  rw [hl, integral_uniformMeasure, Nat.card_eq_fintype_card, sum_finite_avalanche_leaves]

/-- The actual finite recurrent probability, reciprocal and original-copy error. -/
theorem finite_origin_radius_probability_le {N r M : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    (FiniteWired.law N).real {η | M < finiteAvalancheRadius (origin N) η} ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t ∂WiredTrees.law N) +
      ∑ f ∈ sourceEdges N r hrN, (WiredTrees.law N).real {t |
        f ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
          ¬cutSites (origin N) t f ⊆ boxSites M} := by
  have he : {η : FiniteWired.Recurrent N | M < finiteAvalancheRadius (origin N) η} =
      {η | finiteAvalancheLeaves (origin N) (boxSites M) η} := by
    ext η
    exact finite_origin_radius_gt_iff_leaves η M
  rw [he]
  exact finite_source_counting hr hrN

/-- The same bound for the actual radius cylinder of the finite field law.
The extra layer is exactly the radius test's determining-volume condition. -/
theorem finiteFieldLaw_origin_radius_probability_le {N r M : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (hMN : M + 1 ≤ N) :
    (FiniteWired.finiteFieldLaw N).real {η | (M : WithTop ℕ) < radius η 0} ≤
      (∫ t, WiredTrees.reciprocal N (markedVertices (activeMarks N r))
        (marked_vertices_nonempty _ (source_mem_activeMarks N r)) t ∂WiredTrees.law N) +
      ∑ f ∈ sourceEdges N r hrN, (WiredTrees.law N).real {t |
        f ∈ (WiredTrees.graph N).rootPathCopies t (some (origin N)) none ∧
          ¬cutSites (origin N) t f ⊆ boxSites M} := by
  have hr0 : siteRadius 0 (FiniteWired.site (origin N)) = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [siteRadius_le_iff, site_origin]
    simp
  have hn : siteRadius 0 (FiniteWired.site (origin N)) + M + 1 ≤ N := by
    rw [hr0]
    simpa only [zero_add] using hMN
  have he := finiteFieldLaw_radius_tail_eq_wired (origin N) M hn
  simp only [site_origin, add_zero, Finset.image_id'] at he
  change (FiniteWired.finiteFieldLaw N {η | (M : WithTop ℕ) < radius η 0}).toReal ≤ _
  rw [he]
  exact finite_source_counting hr hrN

/-- A volume-spanning avalanche still cannot have radius larger than the box. -/
theorem finite_origin_radius_le_volume {N : ℕ} (η : FiniteWired.Recurrent N) :
    finiteAvalancheRadius (origin N) η ≤ N := by
  rw [← not_lt, finite_origin_radius_gt_iff_leaves]
  rintro ⟨w, hw, h⟩
  apply h
  intro x hx
  rw [listCounts_support, List.mem_toFinset] at hx
  exact hw.1 x hx

end
end FiniteAvalanches.Sandpile.SourceCounting

#print axioms FiniteAvalanches.Sandpile.SourceCounting.finite_origin_radius_probability_le
#print axioms FiniteAvalanches.Sandpile.SourceCounting.finiteFieldLaw_origin_radius_probability_le
#print axioms FiniteAvalanches.Sandpile.SourceCounting.finite_origin_radius_le_volume
#print FiniteAvalanches.Sandpile.FiniteWired.law
#print FiniteAvalanches.Sandpile.WiredTrees.reciprocal
#print FiniteAvalanches.Sandpile.SourceCounting.sourceMarks
#print FiniteAvalanches.Sandpile.SourceCounting.sourceEdges

#print axioms FiniteAvalanches.Sandpile.SourceCounting.finite_origin_radius_probability_eq_excursion_count


/-! Concrete wired-volume and empty-avalanche consumers. -/
namespace FiniteAvalanches.Sandpile.SourceCounting
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components MeasureTheory
open scoped Classical BigOperators
noncomputable section

theorem box_two_radius_bound :
    (FiniteWired.law 2).real {η | 1 < finiteAvalancheRadius (origin 2) η} ≤
      (∫ t, WiredTrees.reciprocal 2 (markedVertices (activeMarks 2 2))
        (marked_vertices_nonempty _ (source_mem_activeMarks 2 2)) t ∂WiredTrees.law 2) +
      ∑ f ∈ sourceEdges 2 2 (by omega), (WiredTrees.law 2).real {t |
        f ∈ (WiredTrees.graph 2).rootPathCopies t (some (origin 2)) none ∧
          ¬cutSites (origin 2) t f ⊆ boxSites 1} :=
  finite_origin_radius_probability_le (by omega) (by omega)

theorem box_two_original_marks_and_edges :
    markedSites (activeMarks 2 2) = insert (axisSite 2) (insert 0 (nbrFinset 0)) ∧
      (sourceEdges 2 2 (by omega)).card = 5 := by
  exact ⟨markedSites_activeMarks (by omega) (by omega),
    card_sourceEdges (by omega) (by omega)⟩

private theorem site_zero_volume (x : FiniteWired.Active 0) : FiniteWired.site x = 0 := by
  funext i
  have hl : (0 : ℤ) ≤ (x i).val := (x i).property.1
  have hu : (x i).val ≤ (0 : ℤ) := (x i).property.2
  change (x i).val = 0
  omega

private theorem zero_not_neighbor : (0 : Site2) ∉ nbrFinset (0 : Site2) := by
  rw [FiniteWired.mem_neighbors_iff]
  rintro ⟨i, hi | hi⟩ <;> have hh := congrFun hi i <;> simp [unit] at hh

/-- The singleton wired volume has a genuine recurrent height-two input. -/
def singletonTwo : FiniteWired.Recurrent 0 := ⟨fun _ => 2, by
  intro s hs
  obtain ⟨x, hx⟩ := hs.1
  have he : nbrFinset (FiniteWired.site x) ∩ s.image FiniteWired.site = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨hy, hz⟩ := Finset.mem_inter.mp hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hz
    rw [site_zero_volume x, site_zero_volume z] at hy
    exact zero_not_neighbor hy
  have h := hs.2 x hx
  simp only [FiniteWired.internalDegree, he, Finset.card_empty] at h
  omega⟩

theorem singleton_two_empty_avalanche :
    finiteAvalancheRadius (origin 0) singletonTwo = 0 ∧
      ∀ M : ℕ, ¬finiteAvalancheLeaves (origin 0) (boxSites M) singletonTwo := by
  have hh : singletonTwo.val (origin 0) ≠ 3 := by decide
  exact ⟨finite_avalanche_radius_eq_zero_of_source_lt _ _ hh,
    fun M => not_finite_avalanche_leaves_of_source_lt (boxSites M) _ hh⟩

/-- The singleton radius is zero even when its source fires and uses sink copies. -/
theorem singleton_all_three_radius :
    finiteAvalancheRadius (origin 0) ⟨FiniteWired.allThree 0, FiniteWired.allThree_recurrent 0⟩ = 0 :=
  Nat.eq_zero_of_le_zero (finite_origin_radius_le_volume _)

theorem singleton_all_three_source_fires :
    0 < finiteAvalancheCounts (origin 0)
      ⟨FiniteWired.allThree 0, FiniteWired.allThree_recurrent 0⟩ 0 := by
  let η : SourceThree 0 (origin 0) :=
    ⟨⟨FiniteWired.allThree 0, FiniteWired.allThree_recurrent 0⟩, rfl⟩
  change 0 < finiteAvalancheCounts (origin 0) η.val (FiniteWired.site (origin 0))
  obtain ⟨w, hw, he⟩ := finiteAvalancheCounts_spec (origin 0) η.val
  rw [← he, finite_wave_number_eq_source_count η.val hw,
    finite_wave_number_source_three η]
  exact return_time_pos (inputExcursion η)

/-- Opposite exits in the singleton graph remain distinct parallel edge copies. -/
theorem singleton_opposite_exit_copies :
    FiniteWired.directionEdge (origin 0) (0, true) ≠
      FiniteWired.directionEdge (origin 0) (0, false) ∧
    FiniteWired.endpoints (FiniteWired.directionEdge (origin 0) (0, true)) =
      (some (origin 0), none) ∧
    FiniteWired.endpoints (FiniteWired.directionEdge (origin 0) (0, false)) =
      (some (origin 0), none) := by
  have hp : ¬FiniteWired.inBox 0 (FiniteWired.site (origin 0) + FiniteWired.step (0, true)) := by
    intro h
    have hi := h 0
    norm_num [site_origin, FiniteWired.step, unit] at hi
  have hn : ¬FiniteWired.inBox 0 (FiniteWired.site (origin 0) + FiniteWired.step (0, false)) := by
    intro h
    have hi := h 0
    norm_num [site_origin, FiniteWired.step, unit] at hi
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have h := FiniteWired.direction_edge_exit_injective (origin 0) hp hn he
    cases h
  · rw [FiniteWired.direction_edge_exit _ _ hp]
    rfl
  · rw [FiniteWired.direction_edge_exit _ _ hn]
    rfl

end
end FiniteAvalanches.Sandpile.SourceCounting

#print axioms FiniteAvalanches.Sandpile.SourceCounting.box_two_radius_bound
#print axioms FiniteAvalanches.Sandpile.SourceCounting.singletonTwo
#print axioms FiniteAvalanches.Sandpile.SourceCounting.singleton_two_empty_avalanche
#print axioms FiniteAvalanches.Sandpile.SourceCounting.singleton_opposite_exit_copies

#print axioms FiniteAvalanches.Sandpile.SourceCounting.singleton_all_three_source_fires


#eval Lean.versionString

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let own : Array Name := #[`FiniteAvalanches.Sandpile.Waves.FiniteRadius]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let mod := match env.getModuleIdxFor? name with
      | some idx => env.header.modules[idx]!.module
      | none => Name.anonymous
    if own.contains mod || (mod == Name.anonymous && (name.toString.startsWith "FiniteAvalanches." ||
      name.toString.startsWith "_private.FiniteAvalanches.Sandpile.SourceCounting.RadiusReduction.")) then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do throwError "unauthorized input {ax} in {name}"
      logInfo m!"RADIUS19_OWNED_CLOSURE {name}: {axioms.toList}"
      unless name.isInternal do logInfo m!"RADIUS19_OWNED_TYPE {name}: {info.type}"
      count := count + 1
  unless count > 0 do throwError "empty audit scope"
  for mod in own do
    unless env.header.modules.any (fun h => h.module == mod) do
      throwError "missing module {mod}"
  unless env.contains `FiniteAvalanches.Sandpile.SourceCounting.singleton_opposite_exit_copies do
    throwError "missing consumer"
  logInfo m!"RADIUS19_ALL_OWNED={count}"
  logInfo "RADIUS19_NO_EXTERNAL_INPUT"
