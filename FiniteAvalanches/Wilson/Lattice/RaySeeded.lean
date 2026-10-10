import FiniteAvalanches.Trees.Lattice.TreeContinuityMeasurability
import FiniteAvalanches.Wilson.Lattice.Sampler

set_option autoImplicit false
open LatticeProb MeasureTheory
open scoped Classical

namespace FiniteAvalanches.Wilson.Lattice.RaySeeded
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice TreeMeasurability11
noncomputable section

/-- The coordinate sigma algebra of genuine infinite injective lattice rays. -/
abbrev rayMeasurableSpace : MeasurableSpace SimpleRay :=
  MeasurableSpace.comap (fun r : SimpleRay => r.vertex) inferInstance

local instance : MeasurableSpace SimpleRay := rayMeasurableSpace

abbrev Rows := ℕ → WalkDriver

def seed (o : Site 2) (T : EndedTree) : SimpleRay :=
  orientedRay T.val T.property.1 T.property.2 o

theorem measurable_seed (o : Site 2) : Measurable (seed o) := by
  apply measurable_iff_comap_le.mpr
  change MeasurableSpace.comap (seed o) (MeasurableSpace.comap (fun r : SimpleRay => r.vertex) _) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact (measurable_pi_iff.mpr (fun n => measurable_rayVertex o n)).comap_le

theorem measurable_seed_tree (o : Site 2) :
    Measurable (fun T : EndedTree => (seed o T, T.val)) :=
  (measurable_seed o).prodMk measurable_subtype_coe

def rayLaw (o : Site 2) : Measure SimpleRay := endedUST.map (seed o)

instance rayLaw_probability (o : Site 2) : IsProbabilityMeasure (rayLaw o) :=
  Measure.isProbabilityMeasure_map (measurable_seed o).aemeasurable

/-- A genuine ray admits both existing root colors, without any finite-root claim.
The color split is bookkeeping; every seed vertex is a separate absorbing root. -/
def seedRoots (γ : SimpleRay) : RootPair where
  zero := {γ.vertex 0}
  one := γ.tailVertices
  disjoint := Set.disjoint_singleton_left.mpr γ.start_not_mem_tail
  zero_nonempty := Set.singleton_nonempty _
  one_nonempty := γ.tail_nonempty

theorem seedRoots_union (γ : SimpleRay) :
    (seedRoots γ).zero ∪ (seedRoots γ).one = γ.vertices := by
  ext x
  constructor
  · rintro (hx | ⟨n, hn⟩)
    · exact ⟨0, Set.mem_singleton_iff.mp hx |>.symm⟩
    · exact ⟨n + 1, hn⟩
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, rfl⟩

theorem initial_covered (γ : SimpleRay) :
    (initialSampler (seedRoots γ)).covered = γ.vertices := by
  rw [← seedRoots_union]
  ext x
  simp only [SamplerState.covered, Set.mem_setOf_eq, initialSampler, Set.mem_union]
  split_ifs <;> simp_all

/-- Actual sampler prefixes, including skipped/duplicate slots and their consumed rows. -/
def prefixRun (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows) (n : ℕ) :
    Option SamplerState :=
  samplerRun (initialSampler (seedRoots γ)) ((List.range n).map order) ξ

/-- No failed walk is replaced by a finite trace or an artificial tree. -/
def Successful (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows) : Prop :=
  ∀ n, ∃ st, prefixRun γ order ξ n = some st

/-- Each original lattice edge occurs individually; the infinite seed is retained. -/
def EdgePresent (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows) (e : LatticeEdge) : Prop :=
  (∃ k, e.val = s(γ.vertex k, γ.vertex (k + 1))) ∨
    ∃ n st, prefixRun γ order ξ n = some st ∧ e.val ∈ st.edges

/-- Literal graph of the complete successful algorithm. -/
def Completes (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows) (ω : EdgeField) : Prop :=
  Successful γ order ξ ∧ ∀ e, ω e = true ↔ EdgePresent γ order ξ e

theorem completion_existsUnique (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows)
    (h : Successful γ order ξ) : ∃! ω : EdgeField, Completes γ order ξ ω := by
  refine ⟨fun e => decide (EdgePresent γ order ξ e), ⟨h, fun e => by simp⟩, ?_⟩
  intro ω hω
  funext e
  have he := hω.2 e
  apply Bool.eq_iff_iff.mpr
  simpa using he

/-- Defined only on the genuine successful domain, after its unique completion proof. -/
def completedEdges (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows)
    (_h : Successful γ order ξ) : EdgeField :=
  fun e => decide (EdgePresent γ order ξ e)

theorem completedEdges_characterization (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows)
    (h : Successful γ order ξ) (ω : EdgeField) :
    ω = completedEdges γ order ξ h ↔ Completes γ order ξ ω := by
  constructor
  · rintro rfl
    exact ⟨h, fun e => by simp [completedEdges]⟩
  · intro hω
    exact (completion_existsUnique γ order ξ h).unique hω
      ⟨h, fun e => by simp [completedEdges]⟩

theorem retains_seed (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows)
    (h : Successful γ order ξ) (n : ℕ) :
    completedEdges γ order ξ h ⟨s(γ.vertex n, γ.vertex (n + 1)), γ.adjacent n⟩ = true :=
  decide_eq_true (Or.inl ⟨n, rfl⟩)

theorem retains_original_branch (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows)
    (h : Successful γ order ξ) (n : ℕ) (st : SamplerState)
    (hn : prefixRun γ order ξ n = some st) (e : LatticeEdge) (he : e.val ∈ st.edges) :
    completedEdges γ order ξ h e = true := decide_eq_true (Or.inr ⟨n, st, hn, he⟩)

theorem seed_only_prefix (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows) :
    prefixRun γ order ξ 0 = some (initialSampler (seedRoots γ)) := rfl

theorem repeated_seed_queries (γ : SimpleRay) (L : List (Site 2))
    (hL : ∀ x ∈ L, x ∈ γ.vertices) (ξ : Rows) :
    samplerRun (initialSampler (seedRoots γ)) L ξ = some (initialSampler (seedRoots γ)) := by
  exact samplerRun_of_covered _ L (fun x hx => initial_covered γ ▸ hL x hx) ξ

end
end FiniteAvalanches.Wilson.Lattice.RaySeeded
