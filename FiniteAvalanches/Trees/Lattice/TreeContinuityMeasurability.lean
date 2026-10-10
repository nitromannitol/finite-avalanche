import FiniteAvalanches.Trees.Lattice.TreeContinuityObjects
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option autoImplicit false
open LatticeProb MeasureTheory
open scoped Classical

namespace TreeMeasurability11
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.Lattice SimpleGraph
noncomputable section

private theorem measurable_adj (x y : Site 2) :
    Measurable (fun ω : EdgeField => (toGraph ω).Adj x y) := by
  by_cases h : (lattice 2).Adj x y
  · simp_rw [toGraph_adj_iff _ h]
    exact (measurable_pi_apply (⟨s(x,y), h⟩ : LatticeEdge) :
      Measurable (fun ω : EdgeField => ω ⟨s(x,y), h⟩)).eq_const true
  · have he : (fun ω : EdgeField => (toGraph ω).Adj x y) = fun _ => False := by
      funext ω; exact propext ⟨fun hx => h (toGraph_le_lattice _ hx), False.elim⟩
    rw [he]; exact measurable_const

private theorem measurable_cut_adj (e : Sym2 (Site 2)) (x y : Site 2) :
    Measurable (fun ω : EdgeField => ((toGraph ω).deleteEdges {e}).Adj x y) := by
  simp_rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  exact (measurable_adj x y).and measurable_const

private def lengthReach (G : SimpleGraph (Site 2)) : ℕ → Site 2 → Site 2 → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, G.Adj x z ∧ lengthReach G n z y

private theorem reachable_length (G : SimpleGraph (Site 2)) (x y : Site 2) :
    G.Reachable x y ↔ ∃ n, lengthReach G n x y := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact ⟨0, rfl⟩
    | @cons x z y h p ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, z, h, hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero =>
      change x = y at hn
      subst x
      exact .refl _
    | succ n ih =>
      obtain ⟨z, hxz, hz⟩ := hn
      exact hxz.reachable.trans (ih z hz)

private theorem measurable_cut_reachable (e : Sym2 (Site 2)) (x y : Site 2) :
    Measurable (fun ω : EdgeField => ((toGraph ω).deleteEdges {e}).Reachable x y) := by
  simp_rw [reachable_length]
  apply Measurable.exists
  intro n
  induction n generalizing x with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun ω => ∃ z,
      ((toGraph ω).deleteEdges {e}).Adj x z ∧ lengthReach _ n z y)
    exact Measurable.exists (fun z => (measurable_cut_adj e x z).and (ih z))

private theorem component_infinite_iff (G : SimpleGraph (Site 2)) (x : Site 2) :
    (G.connectedComponentMk x).supp.Infinite ↔
      ∀ F : Finset (Site 2), ∃ y, G.Reachable y x ∧ y ∉ F := by
  constructor
  · intro h F
    obtain ⟨y, hy, hyF⟩ := h.exists_notMem_finset F
    exact ⟨y, ConnectedComponent.exact hy, hyF⟩
  · intro h hfin
    obtain ⟨y, hy, hyF⟩ := h hfin.toFinset
    exact hyF (hfin.mem_toFinset.mpr (ConnectedComponent.sound hy))

private theorem measurable_infinite_cut (e : Sym2 (Site 2)) (x : Site 2) :
    Measurable (fun ω : EdgeField =>
      (((toGraph ω).deleteEdges {e}).connectedComponentMk x).supp.Infinite) := by
  simp_rw [component_infinite_iff]
  exact Measurable.forall (fun F => Measurable.exists
    (fun y => (measurable_cut_reachable e y x).and measurable_const))

/-- The actual uniquely selected outgoing neighbor is a measurable site. -/
theorem measurable_towardEnd (x : Site 2) :
    Measurable (fun T : EndedTree => towardEnd T.val T.property.1 T.property.2 x) := by
  apply measurable_to_countable'
  intro y
  change MeasurableSet {T : EndedTree | towardEnd T.val T.property.1 T.property.2 x = y}
  have hm : Measurable (fun T : EndedTree => (toGraph T.val).Adj x y ∧
      (((toGraph T.val).deleteEdges {s(x,y)}).connectedComponentMk y).supp.Infinite) :=
    ((measurable_adj x y).and (measurable_infinite_cut s(x,y) y)).comp measurable_subtype_coe
  convert hm.setOf using 1
  ext T
  exact (eq_comm.trans (towardEnd_characterization T.val T.property.1 T.property.2 x y))

/-- Every position on every genuine source ray is measurable, with no invalid-field extension. -/
theorem measurable_rayVertex (x : Site 2) (n : ℕ) :
    Measurable (fun T : EndedTree => (orientedRay T.val T.property.1 T.property.2 x).vertex n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hd : Measurable (fun p : EndedTree × Site 2 =>
        towardEnd p.1.val p.1.property.1 p.1.property.2 p.2) :=
      measurable_from_prod_countable_left (fun y => measurable_towardEnd y)
    convert hd.comp (measurable_id.prodMk ih) using 1
    funext T
    exact infiniteRay_succ T.val T.property.1
      (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) x n

private theorem measurable_rayVisits (x z : Site 2) :
    Measurable (fun T : EndedTree => z ∈ (orientedRay T.val T.property.1 T.property.2 x).vertices) :=
  Measurable.exists (fun n => (measurable_rayVertex x n).eq_const z)

/-- Countable ray-visit characterizations make the actual first common ancestor measurable. -/
theorem measurable_earliestCommonAncestor (S : Finset (Site 2)) (hS : S.Nonempty) :
    Measurable (fun T : EndedTree => earliestCommonAncestor T.val T.property.1 T.property.2 S hS) := by
  apply measurable_to_countable'
  intro c
  change MeasurableSet {T : EndedTree | earliestCommonAncestor T.val T.property.1 T.property.2 S hS = c}
  have hcommon (d : Site 2) : Measurable (fun T : EndedTree =>
      ∀ x ∈ S, d ∈ (orientedRay T.val T.property.1 T.property.2 x).vertices) :=
    Measurable.forall (fun x => measurable_const.imp (measurable_rayVisits x d))
  have hm := (hcommon c).and (Measurable.forall
    (fun d => (hcommon d).imp (measurable_rayVisits c d)))
  convert hm.setOf using 1
  ext T
  exact eq_comm.trans (earliestCommonAncestor_characterization T.val T.property.1 T.property.2 S hS c)

private def selectedWalk (ω : EdgeField) {x y : Site 2} : (lattice 2).Walk x y → Prop
  | .nil => True
  | @Walk.cons _ _ x z y h p => ω ⟨s(x,z), h⟩ = true ∧ selectedWalk ω p

private theorem measurable_selectedWalk {x y : Site 2} (p : (lattice 2).Walk x y) :
    Measurable (fun ω : EdgeField => selectedWalk ω p) := by
  induction p with
  | nil => exact measurable_const
  | @cons x z y h p ih =>
    exact ((measurable_pi_apply (⟨s(x,z), h⟩ : LatticeEdge) :
      Measurable (fun ω : EdgeField => ω ⟨s(x,z), h⟩)).eq_const true).and ih

private def liftSelectedWalk (ω : EdgeField) {x y : Site 2}
    (p : (lattice 2).Walk x y) (h : selectedWalk ω p) : (toGraph ω).Walk x y :=
  match p with
  | .nil => .nil
  | @Walk.cons _ _ x _z y hAdj q => .cons ⟨hAdj, h.1⟩ (liftSelectedWalk ω q h.2)

private theorem liftSelectedWalk_support (ω : EdgeField) {x y : Site 2}
    (p : (lattice 2).Walk x y) (h : selectedWalk ω p) :
    (liftSelectedWalk ω p h).support = p.support := by
  induction p with
  | nil => rfl
  | cons _ p ih => exact congrArg (List.cons _) (ih h.2)

private theorem selected_map {ω : EdgeField} {x y : Site 2} (p : (toGraph ω).Walk x y) :
    selectedWalk ω (p.mapLe (toGraph_le_lattice ω)) := by
  induction p with
  | nil => trivial
  | @cons x z y h p ih => exact ⟨(toGraph_adj_iff ω (toGraph_le_lattice ω h)).mp h, ih⟩

private theorem path_member_iff (T : EndedTree) (x y z : Site 2) :
    z ∈ (RootedPaths.path T.property.1 x y).support ↔
      ∃ p : (lattice 2).Path x y, selectedWalk T.val p.val ∧ z ∈ p.val.support := by
  constructor
  · intro hz
    let p := RootedPaths.path T.property.1 x y
    refine ⟨⟨p.mapLe (toGraph_le_lattice T.val), ?_⟩, selected_map p, ?_⟩
    · exact (RootedPaths.path_isPath T.property.1 x y).mapLe _
    · simpa only [Walk.support_mapLe_eq_support] using hz
  · rintro ⟨p, hp, hz⟩
    have hpath : (liftSelectedWalk T.val p.val hp).IsPath := by
      rw [Walk.isPath_def, liftSelectedWalk_support]
      exact p.property.support_nodup
    rw [RootedPaths.path_eq T.property.1 _ hpath, liftSelectedWalk_support]
    exact hz

private theorem measurable_path_member (x y z : Site 2) :
    Measurable (fun T : EndedTree => z ∈ (RootedPaths.path T.property.1 x y).support) := by
  letI : Countable ((lattice 2).Walk x y) := Walk.support_injective.countable
  simp_rw [path_member_iff]
  exact Measurable.exists (fun p =>
    ((measurable_selectedWalk p.val).comp measurable_subtype_coe).and measurable_const)

/-- Measurability of the true minimal selected subtree, not its ancestor past. -/
theorem measurable_connectingSites (S : Finset (Site 2)) (hS : S.Nonempty) :
    Measurable (fun T : EndedTree => connectingSites T.val T.property.1 T.property.2 S hS) := by
  rw [measurable_finset_iff]
  intro z
  have he : (fun T : EndedTree => z ∈ connectingSites T.val T.property.1 T.property.2 S hS) =
      fun T => ∃ x ∈ S, ∃ y ∈ S, z ∈ (RootedPaths.path T.property.1 x y).support := by
    funext T
    exact propext (show _ ↔ _ from by
      rw [← Finset.mem_coe, connectingSites_eq_span]
      rfl)
  rw [he]
  exact Measurable.exists (fun x => measurable_const.and (Measurable.exists
    (fun y => measurable_const.and (measurable_path_member x y z))))

private theorem measurable_past_member (x y : Site 2) :
    Measurable (fun T : EndedTree => y ∈ vertexPast T.val T.property.1 T.property.2 x) := by
  simp_rw [vertexPast_characterization]
  exact measurable_rayVisits y x

/-- The actual common-ancestor past's complement field is measurable. -/
theorem measurable_sourcePastComplement (S : Finset (Site 2)) (hS : S.Nonempty) :
    Measurable (fun T : EndedTree => sourcePastComplement T.val T.property.1 T.property.2 S hS) := by
  apply measurable_pi_lambda
  intro y
  have hc := measurable_earliestCommonAncestor S hS
  have hp : Measurable (fun T : EndedTree =>
      y ∈ vertexPast T.val T.property.1 T.property.2
        (earliestCommonAncestor T.val T.property.1 T.property.2 S hS)) := by
    have he : (fun T : EndedTree => y ∈ vertexPast T.val T.property.1 T.property.2
          (earliestCommonAncestor T.val T.property.1 T.property.2 S hS)) =
        fun T => ∃ c : Site 2, earliestCommonAncestor T.val T.property.1 T.property.2 S hS = c ∧
          y ∈ vertexPast T.val T.property.1 T.property.2 c := by
      funext T; exact propext (by simp)
    rw [he]
    exact Measurable.exists (fun c => (hc.eq_const c).and (measurable_past_member c y))
  apply measurable_to_countable'
  intro b
  cases b
  · convert hp.setOf using 1
    ext T
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      sourcePastComplement, decide_eq_false_iff_not, not_not]
  · convert hp.not.setOf using 1
    ext T
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      sourcePastComplement, decide_eq_true_eq]

private theorem measurable_contacts_pair :
    Measurable (fun p : ColorField × Finset (Site 2) => contacts p.2 p.1) :=
  measurable_from_prod_countable_left (fun K => (continuous_contacts K).measurable)

private theorem measurable_contacts_composition
    (K : EndedTree → Finset (Site 2)) (σ : EndedTree → ColorField)
    (hK : Measurable K) (hσ : Measurable σ) :
    Measurable (fun T => contacts (K T) (σ T)) := by
  have hp : Measurable (fun T : EndedTree => (σ T, K T)) := hσ.prodMk hK
  have hm := measurable_contacts_pair.comp hp
  simpa only [Function.comp_def] using hm

/-- The true random K and true random ancestor past are both consumed in this count. -/
theorem measurable_sourceBoundaryCount (S : Finset (Site 2)) (hS : S.Nonempty) :
    Measurable (fun T : EndedTree => sourceBoundaryCount T.val T.property.1 T.property.2 S hS) := by
  unfold sourceBoundaryCount
  exact measurable_contacts_composition
    (fun T => connectingSites T.val T.property.1 T.property.2 S hS)
    (fun T => sourcePastComplement T.val T.property.1 T.property.2 S hS)
    (measurable_connectingSites S hS) (measurable_sourcePastComplement S hS)

theorem measurable_infiniteReciprocal (S : Finset (Site 2)) (hS : S.Nonempty) :
    Measurable (infiniteReciprocal S hS) := by
  unfold infiniteReciprocal
  exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (measurable_sourceBoundaryCount S hS)).inv

/-- Actual canonical UST reciprocal, with no measurability premise. -/
theorem aemeasurable_infiniteReciprocal (S : Finset (Site 2)) (hS : S.Nonempty) :
    AEMeasurable (infiniteReciprocal S hS) endedUST :=
  (measurable_infiniteReciprocal S hS).aemeasurable

theorem infiniteReciprocal_bounds (S : Finset (Site 2)) (hS : S.Nonempty) (T : EndedTree) :
    0 ≤ infiniteReciprocal S hS T ∧ infiniteReciprocal S hS T ≤ 1 := by
  unfold infiniteReciprocal
  have hc : (1 : ℝ) ≤ (sourceBoundaryCount T.val T.property.1 T.property.2 S hS : ℝ) := by
    exact_mod_cast sourceBoundaryCount_ge_one T.val T.property.1 T.property.2 S hS
  constructor
  · exact inv_nonneg.mpr (le_trans zero_le_one hc)
  · simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hc

theorem integrable_infiniteReciprocal (S : Finset (Site 2)) (hS : S.Nonempty) :
    Integrable (infiniteReciprocal S hS) endedUST := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_infiniteReciprocal S hS).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro T
  rw [Real.norm_eq_abs, abs_of_nonneg (infiniteReciprocal_bounds S hS T).1]
  exact (infiniteReciprocal_bounds S hS T).2

/-- Every fixed-source, fixed-edge, integer-threshold event uses the full actual ray. -/
theorem measurableSet_infiniteCutEscape (o : Site 2) (f : LatticeEdge) (M : ℕ) :
    MeasurableSet (infiniteCutEscape o f M) := by
  have hray : Measurable (fun T : EndedTree => ∃ n : ℕ,
      f.val = s((orientedRay T.val T.property.1 T.property.2 o).vertex n,
        (orientedRay T.val T.property.1 T.property.2 o).vertex (n + 1))) := by
    apply Measurable.exists
    intro n
    have hm : Measurable (fun T : EndedTree => ∃ u v : Site 2,
        (orientedRay T.val T.property.1 T.property.2 o).vertex n = u ∧
        (orientedRay T.val T.property.1 T.property.2 o).vertex (n+1) = v ∧ f.val = s(u,v)) :=
      Measurable.exists (fun u => Measurable.exists (fun v =>
        (measurable_rayVertex o n).eq_const u |>.and
          ((measurable_rayVertex o (n+1)).eq_const v |>.and measurable_const)))
    convert hm using 1
    funext T
    exact propext (by simp)
  have hsubset : Measurable (fun T : EndedTree =>
      cutComponent T.val f o ⊆ (FiniteAvalanches.Sandpile.boxSites M : Set (Site 2))) := by
    change Measurable (fun T : EndedTree => ∀ y,
      y ∈ cutComponent T.val f o → y ∈ (FiniteAvalanches.Sandpile.boxSites M : Set (Site 2)))
    simp_rw [mem_cutComponent_iff]
    exact Measurable.forall (fun y =>
      ((measurable_cut_reachable f.val y o).comp measurable_subtype_coe).imp measurable_const)
  exact (hray.and hsubset.not).setOf

theorem nullMeasurableSet_infiniteCutEscape (o : Site 2) (f : LatticeEdge) (M : ℕ) :
    NullMeasurableSet (infiniteCutEscape o f M) endedUST :=
  (measurableSet_infiniteCutEscape o f M).nullMeasurableSet

end
end TreeMeasurability11
