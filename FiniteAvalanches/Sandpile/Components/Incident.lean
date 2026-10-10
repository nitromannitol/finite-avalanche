import FiniteAvalanches.Sandpile.Components.Degrees
import FiniteAvalanches.Model.WiredTrees

/-! Every original wired incident copy is exactly one direction copy. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Incidence remembers the original copy, including individual sink exits. -/
def incident {N : ℕ} (x : FiniteWired.Active N) (e : FiniteWired.Edge N) : Prop :=
  (FiniteWired.endpoints e).1 = some x ∨ (FiniteWired.endpoints e).2 = some x

theorem direction_edge_incident {N : ℕ} (x : FiniteWired.Active N)
    (d : FiniteWired.Direction) : incident x (FiniteWired.directionEdge x d) := by
  rcases d with ⟨i, b⟩
  cases b
  all_goals simp only [FiniteWired.directionEdge]
  all_goals split_ifs
  all_goals simp [incident, FiniteWired.endpoints]

/-- An incident interior or exit copy comes from an actual direction at x. -/
theorem exists_direction_of_incident {N : ℕ} (x : FiniteWired.Active N)
    (e : FiniteWired.Edge N) (he : incident x e) :
    ∃ d : FiniteWired.Direction, FiniteWired.directionEdge x d = e := by
  cases e with
  | inl e =>
    obtain ⟨i, hi⟩ := e.property
    rcases he with he | he
    · have hx : e.val.1 = x := Option.some.inj he
      have hb : FiniteWired.inBox N (FiniteWired.site x + unit i) := by
        rw [← hx, ← hi]
        exact fun j => (e.val.2 j).property
      refine ⟨(i, true), ?_⟩
      simp only [FiniteWired.directionEdge, dif_pos hb]
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · exact hx.symm
      · apply FiniteWired.site_injective N
        exact (hx ▸ hi).symm
    · have hx : e.val.2 = x := Option.some.inj he
      have hs : FiniteWired.site x - unit i = FiniteWired.site e.val.1 := by
        rw [← hx, hi]
        abel
      have hb : FiniteWired.inBox N (FiniteWired.site x - unit i) := by
        rw [hs]
        exact fun j => (e.val.1 j).property
      refine ⟨(i, false), ?_⟩
      simp only [FiniteWired.directionEdge, dif_pos hb]
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · exact FiniteWired.site_injective N hs
      · exact hx.symm
  | inr e =>
    have hx : e.val.1 = x := by
      rcases he with he | he
      · exact Option.some.inj he
      · have hn : (none : FiniteWired.Vertex N) = some x := he
        cases hn
    have hb : ¬FiniteWired.inBox N (FiniteWired.site x + FiniteWired.step e.val.2) := by
      simpa only [hx] using e.property
    refine ⟨e.val.2, ?_⟩
    rw [FiniteWired.direction_edge_exit x e.val.2 hb]
    apply congrArg Sum.inr
    apply Subtype.ext
    exact Prod.ext hx.symm rfl

/-- Uniqueness precedes any conversion from original copies to directions. -/
theorem existsUnique_direction_of_incident {N : ℕ} (x : FiniteWired.Active N)
    (e : FiniteWired.Edge N) (he : incident x e) :
    ∃! d : FiniteWired.Direction, FiniteWired.directionEdge x d = e := by
  obtain ⟨d, hd⟩ := exists_direction_of_incident x e he
  exact ⟨d, hd, fun d' hd' => direction_edge_injective x (hd'.trans hd.symm)⟩

/-- Retention in the inside component is exactly the neighbor-in-C test. -/
theorem inner_direction_endpoints_iff {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : FiniteWired.Active N // FiniteWired.site x ∈ C.val})
    (d : FiniteWired.Direction) :
    (insideVertex C.val (FiniteWired.endpoints (FiniteWired.directionEdge x.val d)).1 ∧
      insideVertex C.val (FiniteWired.endpoints (FiniteWired.directionEdge x.val d)).2) ↔
        FiniteWired.site x.val + FiniteWired.step d ∈ C.val := by
  constructor
  · intro he
    rcases d with ⟨i, b⟩
    cases b
    all_goals simp only [FiniteWired.directionEdge] at he
    all_goals split_ifs at he
    all_goals simp only [FiniteWired.endpoints, insideVertex, FiniteWired.site_activeOfSite] at he
    all_goals first
      | simpa only [FiniteWired.step, Bool.false_eq_true, if_false, ← sub_eq_add_neg] using he.1
      | simpa only [FiniteWired.step, if_true] using he.2
  · exact inner_direction_edge_endpoints C.property.1 x.property d

/-- Retention in the sink component is exactly the neighbor-outside-C test. -/
theorem outer_direction_endpoints_iff {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : FiniteWired.Active N // FiniteWired.site x ∉ C.val})
    (d : FiniteWired.Direction) :
    (outsideVertex C.val (FiniteWired.endpoints (FiniteWired.directionEdge x.val d)).1 ∧
      outsideVertex C.val (FiniteWired.endpoints (FiniteWired.directionEdge x.val d)).2) ↔
        FiniteWired.site x.val + FiniteWired.step d ∉ C.val := by
  constructor
  · intro he
    rcases d with ⟨i, b⟩
    cases b
    all_goals simp only [FiniteWired.directionEdge] at he
    all_goals split_ifs at he
    all_goals simp only [FiniteWired.endpoints, outsideVertex, FiniteWired.site_activeOfSite] at he
    all_goals first
      | simpa only [FiniteWired.step, Bool.false_eq_true, if_false, ← sub_eq_add_neg] using he.1
      | simpa only [FiniteWired.step, if_true] using he.2
      | rename_i hb
        intro hm
        apply hb
        simpa only [FiniteWired.step, Bool.false_eq_true, if_false, if_true,
          ← sub_eq_add_neg] using (mem_box_sites N _).mp (C.property.1 hm)
  · exact outer_direction_edge_endpoints x.property d

/-- Literal induced-graph incident copies: incidence and both endpoints in the support. -/
def inducedIncidentCopies {N : ℕ} (V : Set (FiniteWired.Vertex N))
    (x : FiniteWired.Active N) : Finset (FiniteWired.Edge N) :=
  Finset.univ.filter (fun e => incident x e ∧
    (FiniteWired.endpoints e).1 ∈ V ∧ (FiniteWired.endpoints e).2 ∈ V)

theorem inner_incident_copies_eq {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : FiniteWired.Active N // FiniteWired.site x ∈ C.val}) :
    innerIncidentCopies C x = inducedIncidentCopies {v | insideVertex C.val v} x.val := by
  ext e
  simp only [innerIncidentCopies, inducedIncidentCopies, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨direction_edge_incident x.val d,
      (inner_direction_endpoints_iff C x d).mpr ((Finset.mem_filter.mp hd).2)⟩
  · rintro ⟨hi, he⟩
    obtain ⟨d, hd⟩ := exists_direction_of_incident x.val e hi
    refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hd⟩
    apply (inner_direction_endpoints_iff C x d).mp
    simpa only [hd] using he

theorem outer_incident_copies_eq {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : FiniteWired.Active N // FiniteWired.site x ∉ C.val}) :
    outerIncidentCopies C x = inducedIncidentCopies {v | outsideVertex C.val v} x.val := by
  ext e
  simp only [outerIncidentCopies, inducedIncidentCopies, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨direction_edge_incident x.val d,
      (outer_direction_endpoints_iff C x d).mpr ((Finset.mem_filter.mp hd).2)⟩
  · rintro ⟨hi, he⟩
    obtain ⟨d, hd⟩ := exists_direction_of_incident x.val e hi
    refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hd⟩
    apply (outer_direction_endpoints_iff C x d).mp
    simpa only [hd] using he

end
end FiniteAvalanches.Sandpile.Components
