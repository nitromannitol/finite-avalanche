import FiniteAvalanches.Wilson.Lattice.FirstBranch
import FiniteAvalanches.Wilson.Lattice.RaySeeded
import FiniteAvalanches.Trees.Lattice.RayPathAgreement

/-! Wilson's algorithm rooted at a distant site, in the limit.

Root the sampler at the site `z n` at distance `n + 1` from `o` and run the walk from `o`
first. Its first branch is the tree path from `o` to `z n`, and the later walks are
stopped on it. In the one-ended uniform spanning tree the tree path from `o` to `z n`
agrees with the ray from `o` on every fixed ball once `z n` leaves the finite pasts of
the ball, so with the same rows the later walks stopped on the path eventually reveal the
same finite edge pattern as the walks stopped on the ray. This is the limit `z n → ∞` of
van Engelenburg–Hutchcroft, Lemma 10, taken inside the tree. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.RaySeeded

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice
open TreeMeasurability11 FiniteAvalanches.Trees.Lattice.BarlowMasson
open scoped Classical ENNReal Topology

attribute [local instance] rayMeasurableSpace

noncomputable section

/-- The site at distance `n + 1` from `o` along the first coordinate. -/
def distantSite (o : Site 2) (n : ℕ) : Site 2 := fun i => if i = 0 then o 0 + n + 1 else o i

theorem distantSite_ne (o : Site 2) (n : ℕ) : o ≠ distantSite o n := by
  intro h
  have h0 := congrFun h 0
  simp only [distantSite, if_true] at h0
  omega

theorem eventually_distantSite_not_mem (o : Site 2) {S : Set (Site 2)} (hS : S.Finite) :
    ∀ᶠ n in atTop, distantSite o n ∉ S := by
  obtain ⟨K, hK⟩ := SiteRoots.exists_inBox_finset (insert o hS.toFinset)
  have ho := hK o (Finset.mem_insert_self _ _)
  refine eventually_atTop.mpr ⟨2 * K, fun n hn hs => ?_⟩
  have h := (hK _ (Finset.mem_insert_of_mem (hS.mem_toFinset.mpr hs)) 0).2
  have h' := (ho 0).1
  simp only [distantSite, if_true] at h
  have : ((2 * K : ℕ) : ℤ) ≤ n := by exact_mod_cast hn
  push_cast at this
  omega

/-- The tree path from `o` to the distant site. -/
def branchPath (o : Site 2) (n : ℕ) (T : EndedTree) : List (Site 2) :=
  (treePath T.val T.property.1 o (distantSite o n)).support

/-- The tree path as a lattice path. -/
def branchLPath (o : Site 2) (n : ℕ) (T : EndedTree) : LPath o (distantSite o n) :=
  ⟨(treePath T.val T.property.1 o (distantSite o n)).mapLe (toGraph_le_lattice T.val),
    (FiniteAvalanches.Trees.RootedPaths.path_isPath T.property.1 _ _).mapLe _⟩

theorem branchLPath_support (o : Site 2) (n : ℕ) (T : EndedTree) :
    (branchLPath o n T).val.support = branchPath o n T :=
  SimpleGraph.Walk.support_mapLe_eq_support _ _

theorem branchLPath_present (o : Site 2) (n : ℕ) (T : EndedTree) :
    T.val ∈ Present (branchLPath o n T).val := by
  apply (present_iff_toGraph _ T.val).mpr
  intro e he
  rw [branchLPath, SimpleGraph.Walk.edges_mapLe_eq_edges] at he
  exact SimpleGraph.Walk.edges_subset_edgeSet _ he

theorem present_iff_eq (o : Site 2) (n : ℕ) (T : EndedTree) (p : LPath o (distantSite o n)) :
    T.val ∈ Present p.val ↔ p = branchLPath o n T :=
  ⟨fun h => (existsUnique_present T.property.1 o (distantSite o n)).unique h
      (branchLPath_present o n T),
    fun h => h ▸ branchLPath_present o n T⟩

theorem measurableSet_branchPath_pred (o : Site 2) (n : ℕ) (P : List (Site 2) → Prop) :
    MeasurableSet {T : EndedTree | P (branchPath o n T)} := by
  have he : {T : EndedTree | P (branchPath o n T)} =
      ⋃ p : LPath o (distantSite o n), ⋃ (_ : P p.val.support),
        (Subtype.val : EndedTree → EdgeField) ⁻¹' Present p.val := by
    ext T
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, exists_prop]
    constructor
    · intro h
      exact ⟨branchLPath o n T, by rwa [branchLPath_support], branchLPath_present o n T⟩
    · rintro ⟨p, hp, hpres⟩
      rw [(present_iff_eq o n T p).mp hpres, branchLPath_support] at hp
      exact hp
  rw [he]
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ =>
    measurable_subtype_coe (measurableSet_present p.val)

theorem measurable_branchPath_comp (o : Site 2) (n : ℕ) (g : List (Site 2) → ℝ≥0∞) :
    Measurable (fun T : EndedTree => g (branchPath o n T)) :=
  fun B _ => measurableSet_branchPath_pred o n (fun l => g l ∈ B)

theorem endedUST_preimage (S : Set EdgeField) (hS : MeasurableSet S) :
    endedUST ((Subtype.val : EndedTree → EdgeField) ⁻¹' S) =
      (squareLatticeUST : Measure EdgeField) S := by
  rw [← endedUST_map, Measure.map_apply measurable_subtype_coe hS]

/-- The first `k + 1` entries of a list. -/
def prefixOf (k : ℕ) (l : List (Site 2)) : Fin (k + 1) → Site 2 := fun i => l.getD i 0

/-- The first `k + 1` vertices of a ray. -/
def rayPrefix (k : ℕ) (γ : SimpleRay) : Fin (k + 1) → Site 2 := fun i => γ.vertex i

/-- The edges of a ray. -/
def seedEdges (γ : SimpleRay) : Set (Sym2 (Site 2)) := {s | ∃ i, s = s(γ.vertex i, γ.vertex (i + 1))}

section Values

variable (L : List (Site 2)) (E : Finset LatticeEdge) (pE : LatticeEdge → Bool)

/-- Later walks stopped on the finite path `l` reveal the pattern `pE` on `E`. -/
def pathTail (l : List (Site 2)) : ℝ≥0∞ :=
  wilsonRows {ξ | ∃ out, samplerRun (coverState {v | v ∈ l}) L ξ = some out ∧
    ∀ e ∈ E, decide (e.val ∈ out.edges ∨ e.val ∈ branchEdges l) = pE e}

/-- Walks stopped on the ray `γ` reveal the pattern `pE` on `E`, the ray edges included. -/
def seedTail (γ : SimpleRay) : ℝ≥0∞ :=
  wilsonRows {ξ | ∃ out, samplerRun (coverState γ.vertices) L ξ = some out ∧
    ∀ e ∈ E, decide (e.val ∈ out.edges ∨ e.val ∈ seedEdges γ) = pE e}

end Values

/-- The finite-distance identity: the uniform spanning tree path from `o` to the distant
site and the later walks stopped on it. -/
theorem branch_identity (o : Site 2) (L : List (Site 2)) (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ∀ x ∈ e.val, x ∈ L) (pE : LatticeEdge → Bool) (k : ℕ)
    (R : Set (Fin (k + 1) → Site 2)) (n : ℕ) :
    endedUST {T | prefixOf k (branchPath o n T) ∈ R ∧ T.val ∈ {ω | ∀ e ∈ E, ω e = pE e}} =
      ∫⁻ T, {T : EndedTree | prefixOf k (branchPath o n T) ∈ R}.indicator
        (fun T => pathTail L E pE (branchPath o n T)) T ∂endedUST := by
  let z := distantSite o n
  let A := {ω : EdgeField | ∀ e ∈ E, ω e = pE e}
  let piece : LPath o z → Set EndedTree := fun p => (Subtype.val : EndedTree → EdgeField) ⁻¹' Present p.val
  have hpiece : ∀ p, MeasurableSet (piece p) := fun p =>
    measurable_subtype_coe (measurableSet_present p.val)
  have hdisj : Pairwise (Function.onFun Disjoint piece) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    intro T hp hq
    exact hpq (((present_iff_eq o n T p).mp hp).trans ((present_iff_eq o n T q).mp hq).symm)
  have hcover : (⋃ p, piece p) = Set.univ := by
    ext T
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨branchLPath o n T, branchLPath_present o n T⟩
  have hpath : ∀ p : LPath o z, ∀ T ∈ piece p, branchPath o n T = p.val.support := by
    intro p T hT
    rw [(present_iff_eq o n T p).mp hT, branchLPath_support]
  have hA : MeasurableSet A := measurableSet_edgePattern E pE
  have hpresent : ∀ p : LPath o z, (squareLatticeUST : Measure EdgeField) (Present p.val) =
      walkLaw (FirstIs p.val) := by
    intro p
    have h := ust_present_inter_eq (distantSite_ne o n) [] ∅ (by simp) pE p
    have h1 : Present p.val ∩ {ω : EdgeField | ∀ e ∈ (∅ : Finset LatticeEdge), ω e = pE e} =
        Present p.val := by ext ω; simp
    have h2 : tailEvent o z [] ∅ pE p.val = Set.univ := by
      ext ξ
      simp [tailEvent, samplerRun]
    rw [h1, h2, measure_univ, mul_one] at h
    exact h
  have hmulti : ∀ p : LPath o z, (squareLatticeUST : Measure EdgeField) (Present p.val ∩ A) =
      pathTail L E pE p.val.support * (squareLatticeUST : Measure EdgeField) (Present p.val) := by
    intro p
    rw [ust_present_inter_eq (distantSite_ne o n) L E hE pE p, hpresent p, mul_comm]
    rfl
  have hS : MeasurableSet {T : EndedTree | prefixOf k (branchPath o n T) ∈ R ∧ T.val ∈ A} :=
    (measurableSet_branchPath_pred o n (fun l => prefixOf k l ∈ R)).inter
      (measurable_subtype_coe hA)
  calc endedUST {T | prefixOf k (branchPath o n T) ∈ R ∧ T.val ∈ A}
      = ∑' p, endedUST (piece p ∩ {T | prefixOf k (branchPath o n T) ∈ R ∧ T.val ∈ A}) := by
        rw [← measure_iUnion (fun p q hpq => (hdisj hpq).mono Set.inter_subset_left
          Set.inter_subset_left) (fun p => (hpiece p).inter hS), ← Set.iUnion_inter, hcover,
          Set.univ_inter]
    _ = ∑' p : LPath o z, {p : LPath o z | prefixOf k p.val.support ∈ R}.indicator
          (fun p => pathTail L E pE p.val.support * endedUST (piece p)) p := by
        congr 1
        funext p
        by_cases hR : prefixOf k p.val.support ∈ R
        · rw [Set.indicator_of_mem (show p ∈ {p : LPath o z | prefixOf k p.val.support ∈ R} from hR)]
          have hset : piece p ∩ {T | prefixOf k (branchPath o n T) ∈ R ∧ T.val ∈ A} =
              (Subtype.val : EndedTree → EdgeField) ⁻¹' (Present p.val ∩ A) := by
            ext T
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
            constructor
            · rintro ⟨hT, -, hTA⟩
              exact ⟨hT, hTA⟩
            · rintro ⟨hT, hTA⟩
              exact ⟨hT, by rw [hpath p T hT]; exact hR, hTA⟩
          rw [hset, endedUST_preimage _ ((measurableSet_present p.val).inter hA), hmulti p,
            endedUST_preimage _ (measurableSet_present p.val)]
        · rw [Set.indicator_of_notMem (show p ∉ {p : LPath o z | prefixOf k p.val.support ∈ R} from hR)]
          have hset : piece p ∩ {T | prefixOf k (branchPath o n T) ∈ R ∧ T.val ∈ A} = ∅ := by
            ext T
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            rintro ⟨hT, hTR, -⟩
            rw [hpath p T hT] at hTR
            exact hR hTR
          rw [hset, measure_empty]
    _ = ∑' p, ∫⁻ T in piece p, {T : EndedTree | prefixOf k (branchPath o n T) ∈ R}.indicator
          (fun T => pathTail L E pE (branchPath o n T)) T ∂endedUST := by
        congr 1
        funext p
        rw [setLIntegral_congr_fun (hpiece p) (g := fun _ =>
          {p : LPath o z | prefixOf k p.val.support ∈ R}.indicator
            (fun p => pathTail L E pE p.val.support) p) (fun T hT => ?_), setLIntegral_const]
        · by_cases hR : prefixOf k p.val.support ∈ R
          · rw [Set.indicator_of_mem (show p ∈ {p : LPath o z | prefixOf k p.val.support ∈ R} from hR),
              Set.indicator_of_mem (show p ∈ {p : LPath o z | prefixOf k p.val.support ∈ R} from hR)]
          · rw [Set.indicator_of_notMem (show p ∉ {p : LPath o z | prefixOf k p.val.support ∈ R} from hR),
              Set.indicator_of_notMem (show p ∉ {p : LPath o z | prefixOf k p.val.support ∈ R} from hR),
              zero_mul]
        · simp only [Set.indicator, Set.mem_setOf_eq, hpath p T hT]
    _ = ∫⁻ T, {T : EndedTree | prefixOf k (branchPath o n T) ∈ R}.indicator
          (fun T => pathTail L E pE (branchPath o n T)) T ∂endedUST := by
        rw [← lintegral_iUnion hpiece hdisj, hcover, Measure.restrict_univ]

end

end FiniteAvalanches.Wilson.Lattice.RaySeeded
