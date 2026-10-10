import FiniteAvalanches.Wilson.ClassicalOrder
import FiniteAvalanches.Wilson.ClassicalTrees
import FiniteAvalanches.Trees.Existence
import FiniteAvalanches.Trees.Measure
import FiniteAvalanches.External.Wilson

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory FiniteAvalanches.Trees FiniteAvalanches.External
open scoped Classical ENNReal
noncomputable section
variable {V E I : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

theorem wilson_output_event_law [Countable I] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (out : Ω → Option (State (V := V) (E := E) (I := I))) (hout : Measurable out)
    (h : ∀ T : G.SpanningTree,
      P {ω | ∃ s, out ω = some s ∧ s.edges = T.val} = (Fintype.card G.SpanningTree : ℝ≥0∞)⁻¹)
    (A : Set G.SpanningTree) :
    P {ω | ∃ s, out ω = some s ∧ ∃ T ∈ A, s.edges = T.val} =
      (Nat.card A : ℝ≥0∞) / Nat.card G.SpanningTree := by
  have hm : ∀ T : G.SpanningTree, MeasurableSet {ω | ∃ s, out ω = some s ∧ s.edges = T.val} :=
    fun T => hout (show MeasurableSet {o : Option (State (V := V) (E := E) (I := I)) |
      ∃ s, o = some s ∧ s.edges = T.val} from trivial)
  have hsplit : {ω | ∃ s, out ω = some s ∧ ∃ T ∈ A, s.edges = T.val} =
      ⋃ T ∈ A.toFinset, {ω | ∃ s, out ω = some s ∧ s.edges = T.val} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨s, hs, T, hT, he⟩; exact ⟨T, hT, s, hs, he⟩
    · rintro ⟨T, hT, s, hs, he⟩; exact ⟨s, hs, T, hT, he⟩
  have hdisj : Set.PairwiseDisjoint (↑A.toFinset : Set G.SpanningTree)
      (fun T : G.SpanningTree => {ω | ∃ s, out ω = some s ∧ s.edges = T.val}) := by
    intro T _ T' _ hne
    refine Set.disjoint_left.mpr ?_
    rintro ω ⟨s, hs, hT⟩ ⟨s', hs', hT'⟩
    have hss : s = s' := Option.some.inj (hs.symm.trans hs')
    exact hne (Subtype.ext (hT.symm.trans ((congrArg State.edges hss).trans hT')))
  rw [hsplit, measure_biUnion_finset hdisj (fun T _ => hm T),
    Finset.sum_congr rfl (fun T _ => h T), Finset.sum_const, nsmul_eq_mul,
    ← Nat.card_eq_card_toFinset, Nat.card_eq_fintype_card (α := G.SpanningTree), div_eq_mul_inv]

variable [Nontrivial V] (hconn : ∀ x y : V, G.reaches Finset.univ x y) (ι : E ↪ I)

theorem wilson_classical_event_law [Countable I] (r : V) (order : List V) (hnodup : order.Nodup)
    (hspan : ∀ v : V, v ∈ order ↔ v ≠ r) (A : Set G.SpanningTree) :
    driversLaw G (uniformLetterLaw G hconn)
        {ω | ∃ s, classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω =
            some s ∧ ∃ T ∈ A, s.edges = T.val} =
      (Nat.card A : ℝ≥0∞) / Nat.card G.SpanningTree := by
  letI : Nonempty (Letter G) := ⟨fun v => @Classical.ofNonempty _ (incident_nonempty G hconn v)⟩
  exact wilson_output_event_law G (driversLaw G (uniformLetterLaw G hconn))
    (classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order)
    (measurable_classicalExplore G ι _ order)
    (fun T => wilson_classical_tree_probability G hconn ι r order hnodup hspan T) A

theorem wilson_list_tree_probability (r : V) (order : List V)
    (horder : ∀ v : V, v = r ∨ v ∈ order) (T : G.SpanningTree) :
    driversLaw G (uniformLetterLaw G hconn)
        {ω | ∃ s, classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω =
            some s ∧ s.edges = T.val} = (Fintype.card G.SpanningTree : ℝ≥0∞)⁻¹ := by
  have key := wilson_classical_tree_probability G hconn ι r (classicalOrder r order)
    (classicalOrder_nodup r order) (classicalOrder_spanning r order horder) T
  simpa only [classicalExplore_normalize G ι r order] using key

theorem wilson_slot_tree_probability [Countable I] (r : V) (order : List V)
    (horder : ∀ v : V, v = r ∨ v ∈ order) (T : G.SpanningTree) :
    driversLaw G (uniformLetterLaw G hconn)
        {ω | ∃ s, explore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω =
            some s ∧ s.edges = T.val} = (Fintype.card G.SpanningTree : ℝ≥0∞)⁻¹ := by
  letI : Nonempty (Letter G) := ⟨fun v => @Classical.ofNonempty _ (incident_nonempty G hconn v)⟩
  letI : ∀ v : V, MeasurableSpace (Incident G v) := fun _ => ⊤
  haveI : ∀ v : V, MeasurableSingletonClass (Incident G v) := fun _ => ⟨fun _ => trivial⟩
  have hB : MeasurableSet {o : Option (State (V := V) (E := E) (I := I)) |
      ∃ s, o = some s ∧ s.edges = T.val} := trivial
  have h1 := explorationLaw_eq_classical G ι (uniformLetterLaw G hconn)
    (initialState (V := V) (E := E) (I := I) ⟨{r}, Set.singleton_nonempty r⟩) order
  calc driversLaw G (uniformLetterLaw G hconn)
        {ω | ∃ s, explore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω = some s ∧
          s.edges = T.val}
      = (explorationLaw G ι (uniformLetterLaw G hconn)
          (initialState (V := V) (E := E) (I := I) ⟨{r}, Set.singleton_nonempty r⟩) order)
          {o | ∃ s, o = some s ∧ s.edges = T.val} :=
        (Measure.map_apply (measurable_explore G ι _ order) hB).symm
    _ = ((driversLaw G (uniformLetterLaw G hconn)).map
          (classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order))
          {o | ∃ s, o = some s ∧ s.edges = T.val} := by rw [h1]
    _ = driversLaw G (uniformLetterLaw G hconn)
        {ω | ∃ s, classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω =
          some s ∧ s.edges = T.val} :=
        Measure.map_apply (measurable_classicalExplore G ι _ order) hB
    _ = _ := wilson_list_tree_probability G hconn ι r order horder T

theorem wilson_classical_succeeds [Countable I] (r : V) (order : List V) (hnodup : order.Nodup)
    (hspan : ∀ v : V, v ∈ order ↔ v ≠ r) :
    driversLaw G (uniformLetterLaw G hconn)
      {ω | ∃ s, classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω =
        some s} = 1 := by
  haveI : Nonempty G.SpanningTree := G.nonempty_spanning_tree hconn
  have h := wilson_classical_event_law G hconn ι r order hnodup hspan Set.univ
  have horder : ∀ v : V, v = r ∨ v ∈ order := fun v =>
    if hv : v = r then Or.inl hv else Or.inr ((hspan v).2 hv)
  have hset : {ω | ∃ s, classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩)
        order ω = some s} =
      {ω | ∃ s, classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω =
        some s ∧ ∃ T ∈ (Set.univ : Set G.SpanningTree), s.edges = T.val} := by
    ext ω
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, hs, ⟨s.edges, (classical_spanning_output_is_tree G ι r order horder ω s hs).2⟩,
        Set.mem_univ _, rfl⟩
    · rintro ⟨s, hs, _⟩; exact ⟨s, hs⟩
  rw [hset, h, Nat.card_univ]
  exact ENNReal.div_self (by exact_mod_cast (Nat.card_pos (α := G.SpanningTree)).ne')
    (ENNReal.natCast_ne_top _)

theorem wilson_ancestorPast_probability [Countable I] [Nonempty G.SpanningTree] {C S : Set V}
    (r : V) (order : List V) (hnodup : order.Nodup) (hspan : ∀ v : V, v ∈ order ↔ v ≠ r)
    (hr : r ∉ C) (hS : S.Nonempty) (t : G.ComponentTree C) (hSC : S ⊆ C) :
    (driversLaw G (uniformLetterLaw G hconn)
      {ω | ∃ s, classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω =
          some s ∧ ∃ u : G.SpanningTree, (G.descendants u r (G.ancestorOf u r S hS) = C ∧
            G.internalEdges C u.val = t.val) ∧ s.edges = u.val}).toReal =
      (Fintype.card (G.ComponentTree Cᶜ) : ℝ) / Fintype.card G.SpanningTree *
        (∑ v ∈ (G.componentSpan t S hSC).toFinset, (G.crossingAt C v).card) := by
  have h := wilson_classical_event_law G hconn ι r order hnodup hspan
    {u : G.SpanningTree | G.descendants u r (G.ancestorOf u r S hS) = C ∧
      G.internalEdges C u.val = t.val}
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at h'
  have h2 := G.probability_ancestorPastTree_eq_sum r hr hS t hSC
  unfold Multigraph.uniformTreeProbability at h2
  exact h'.trans h2

end
end FiniteAvalanches.Wilson.CopiedNetwork
