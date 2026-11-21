import FiniteAvalanches.Wilson.Lattice.SiteRootLimit

/-! Translation invariance of the wired uniform spanning tree of `ℤ²`.

A copy of a wired box that survives the contraction of the roots outside `Γ` is
determined by its lattice edge, and these lattice edges are exactly those meeting `Γ`.
Translating lattice edges therefore identifies the contracted graphs for `Γ` and for its
translate, and with them the rooted forest carriers. The rooted forest laws of a set and
of its translate thus differ by the translation of edge fields. Shifted boxes form an
exhaustion, so the wired uniform spanning tree is translation invariant. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.SiteRoots

open LatticeProb MeasureTheory Filter Topology FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open CopiedNetwork.NonemptyQuotient
open scoped Classical ENNReal

noncomputable section

theorem lattice_adj_add (x y z : Site 2) :
    (lattice 2).Adj (x + z) (y + z) ↔ (lattice 2).Adj x y := by
  have h (a b : Site 2) (i : Fin 2) : a + z = b + z + unit i ↔ a = b + unit i := by
    rw [add_right_comm b z, add_left_inj]
  change (∃ i, y + z = x + z + unit i ∨ x + z = y + z + unit i) ↔
    ∃ i, y = x + unit i ∨ x = y + unit i
  simp only [h]

theorem map_add_mem_edgeSet (z : Site 2) (v : Sym2 (Site 2)) (hv : v ∈ (lattice 2).edgeSet) :
    v.map (· + z) ∈ (lattice 2).edgeSet := by
  induction v using Sym2.ind with
  | h x y =>
    rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, lattice_adj_add]
    exact hv

/-- The translate of a lattice edge. -/
def shiftEdge (z : Site 2) (e : LatticeEdge) : LatticeEdge :=
  ⟨e.val.map (· + z), map_add_mem_edgeSet z e.val e.property⟩

theorem mem_shiftEdge (z : Site 2) (e : LatticeEdge) (x : Site 2) :
    x ∈ (shiftEdge z e).val ↔ x - z ∈ e.val := by
  change x ∈ e.val.map (· + z) ↔ _
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [add_sub_cancel_right] using ha
  · intro h
    exact ⟨x - z, h, sub_add_cancel x z⟩

theorem shiftEdge_neg_shiftEdge (z : Site 2) (e : LatticeEdge) :
    shiftEdge (-z) (shiftEdge z e) = e := by
  apply Subtype.ext
  change Sym2.map (· + -z) (Sym2.map (· + z) e.val) = e.val
  rw [Sym2.map_map]
  simp only [Function.comp_def, add_neg_cancel_right, Sym2.map_id', id_eq]

theorem shiftEdge_shiftEdge_neg (z : Site 2) (e : LatticeEdge) :
    shiftEdge z (shiftEdge (-z) e) = e := by
  simpa only [neg_neg] using shiftEdge_neg_shiftEdge (-z) e

/-- Translation of edge fields: the translated field has the edge `e` exactly when the
original field has `e - z`. -/
def shiftField (z : Site 2) (ω : EdgeField) : EdgeField := fun e => ω (shiftEdge (-z) e)

theorem continuous_shiftField (z : Site 2) : Continuous (shiftField z) :=
  continuous_pi fun _ => continuous_apply _

theorem measurable_shiftField (z : Site 2) : Measurable (shiftField z) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- The translate of a set of sites. -/
def shiftSet (z : Site 2) (Γ : Set (Site 2)) : Set (Site 2) := {x | x - z ∈ Γ}

theorem add_mem_shiftSet (z : Site 2) (Γ : Set (Site 2)) (x : Site 2) :
    x + z ∈ shiftSet z Γ ↔ x ∈ Γ := by
  change x + z - z ∈ Γ ↔ x ∈ Γ
  rw [add_sub_cancel_right]

/-- The sites of `Γ`, every other site being sent to `none`. -/
def siteOption (Γ : Set (Site 2)) (x : Site 2) : Option Γ :=
  if h : x ∈ Γ then some ⟨x, h⟩ else none

/-- Translation of optional sites of `Γ`. -/
def shiftOption (z : Site 2) (Γ : Set (Site 2)) : Option Γ ≃ Option (shiftSet z Γ) :=
  Equiv.optionCongr
    { toFun := fun x => ⟨x.val + z, (add_mem_shiftSet z Γ x.val).mpr x.property⟩
      invFun := fun y => ⟨y.val - z, y.property⟩
      left_inv := fun _ => Subtype.ext (add_sub_cancel_right _ _)
      right_inv := fun _ => Subtype.ext (sub_add_cancel _ _) }

theorem siteOption_add (z : Site 2) (Γ : Set (Site 2)) (x : Site 2) :
    siteOption (shiftSet z Γ) (x + z) = shiftOption z Γ (siteOption Γ x) := by
  by_cases hx : x ∈ Γ
  · have hx' : x + z ∈ shiftSet z Γ := (add_mem_shiftSet z Γ x).mpr hx
    rw [siteOption, dif_pos hx', siteOption, dif_pos hx]
    rfl
  · have hx' : x + z ∉ shiftSet z Γ := fun h => hx ((add_mem_shiftSet z Γ x).mp h)
    rw [siteOption, dif_neg hx', siteOption, dif_neg hx]
    rfl

theorem map_siteOption_of_not_mem (Γ : Set (Site 2)) (s : Sym2 (Site 2))
    (h : ∀ x ∈ s, x ∉ Γ) : s.map (siteOption Γ) = s(none, none) := by
  induction s using Sym2.ind with
  | h a b =>
    rw [Sym2.map_mk, siteOption, siteOption, dif_neg (h a (Sym2.mem_mk_left a b)),
      dif_neg (h b (Sym2.mem_mk_right a b))]

section Contraction

variable (Γ : Set (Site 2)) (N : ℕ) (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x)
include hΓ

/-- Contracted vertices are the sites of `Γ` and the contracted root. -/
def quotientSiteEquiv : Vertex (roots Γ N) ≃ Option Γ :=
  Equiv.optionCongr ((nonrootEquiv Γ N).trans
    { toFun := fun a => ⟨FiniteWired.site a.val, a.property⟩
      invFun := fun x => ⟨FiniteWired.activeOfSite N x.val (hΓ x.val x.property), x.property⟩
      left_inv := fun _ => Subtype.ext (FiniteWired.site_injective N rfl)
      right_inv := fun _ => rfl })

theorem quotientSiteEquiv_project_some (a : FiniteWired.Active N) :
    quotientSiteEquiv Γ N hΓ (project (roots Γ N) (some a)) =
      siteOption Γ (FiniteWired.site a) := by
  by_cases h : FiniteWired.site a ∈ Γ
  · have hna : (some a : FiniteWired.Vertex N) ∉ (roots Γ N).val := fun hr => hr h
    rw [project, dif_neg hna, siteOption, dif_pos h]
    rfl
  · have hr : (some a : FiniteWired.Vertex N) ∈ (roots Γ N).val := h
    rw [project, dif_pos hr, siteOption, dif_neg h]
    rfl

/-- The contracted endpoints of a copy are the optional `Γ`-sites of its lattice edge. -/
theorem endpoints_siteOption (e : FiniteWired.Edge N) :
    s(quotientSiteEquiv Γ N hΓ (project (roots Γ N) (FiniteWired.endpoints e).1),
      quotientSiteEquiv Γ N hΓ (project (roots Γ N) (FiniteWired.endpoints e).2)) =
      (TreeMeasurability11.originalCopyEdge e).val.map (siteOption Γ) := by
  cases e with
  | inl e =>
    change s(quotientSiteEquiv Γ N hΓ (project (roots Γ N) (some e.val.1)),
      quotientSiteEquiv Γ N hΓ (project (roots Γ N) (some e.val.2))) =
      Sym2.map (siteOption Γ) s(FiniteWired.site e.val.1, FiniteWired.site e.val.2)
    rw [Sym2.map_mk, quotientSiteEquiv_project_some, quotientSiteEquiv_project_some]
  | inr e =>
    have hout : siteOption Γ (FiniteWired.site e.val.1 + FiniteWired.step e.val.2) = none :=
      dif_neg (fun h => e.property (hΓ _ h))
    change s(quotientSiteEquiv Γ N hΓ (project (roots Γ N) (some e.val.1)),
      quotientSiteEquiv Γ N hΓ (project (roots Γ N) none)) =
      Sym2.map (siteOption Γ) s(FiniteWired.site e.val.1,
        FiniteWired.site e.val.1 + FiniteWired.step e.val.2)
    rw [Sym2.map_mk, quotientSiteEquiv_project_some, hout, project_sink]
    rfl

/-- Lattice edges with an endpoint in `Γ`. -/
abbrev MeetEdge (Γ : Set (Site 2)) := {e : LatticeEdge // ∃ x ∈ e.val, x ∈ Γ}

theorem copy_meets (c : Copy (WiredTrees.graph N) (roots Γ N)) :
    ∃ x ∈ (TreeMeasurability11.originalCopyEdge c.val).val, x ∈ Γ := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have he := (endpoints_siteOption Γ N hΓ c.val).trans (map_siteOption_of_not_mem Γ _ hno)
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact c.property ((quotientSiteEquiv Γ N hΓ).injective (h1.trans h2.symm))
  · exact c.property ((quotientSiteEquiv Γ N hΓ).injective (h1.trans h2.symm))

/-- A surviving copy is recorded by its lattice edge. -/
def copyMeet (c : Copy (WiredTrees.graph N) (roots Γ N)) : MeetEdge Γ :=
  ⟨TreeMeasurability11.originalCopyEdge c.val, copy_meets Γ N hΓ c⟩

theorem copyMeet_bijective : Function.Bijective (copyMeet Γ N hΓ) := by
  constructor
  · intro a b h
    exact Subtype.ext (originalCopyEdge_injective N (congrArg Subtype.val h))
  · rintro ⟨e, x, hxe, hxΓ⟩
    obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hxe
    have hadj : (lattice 2).Adj x y := by
      rw [← SimpleGraph.mem_edgeSet, ← hy]
      exact e.property
    obtain ⟨d, hd⟩ : ∃ d : FiniteWired.Direction, y = x + FiniteWired.step d := by
      obtain ⟨i, h | h⟩ := hadj
      · exact ⟨(i, true), by simp [FiniteWired.step, h]⟩
      · exact ⟨(i, false), by simp [FiniteWired.step, h]⟩
    let f := FiniteWired.directionEdge (FiniteWired.activeOfSite N x (hΓ x hxΓ)) d
    have hf : (TreeMeasurability11.originalCopyEdge f).val = e.val := by
      rw [originalCopyEdge_direction, hy, hd]
      rfl
    have hs : project (roots Γ N) ((WiredTrees.graph N).left f) ≠
        project (roots Γ N) ((WiredTrees.graph N).right f) := by
      intro heq
      have he := endpoints_siteOption Γ N hΓ f
      change project (roots Γ N) (FiniteWired.endpoints f).1 =
        project (roots Γ N) (FiniteWired.endpoints f).2 at heq
      rw [hf, hy, Sym2.map_mk, heq] at he
      have hρ : siteOption Γ x = siteOption Γ y := by
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h1.symm.trans h2
        · exact h2.symm.trans h1
      rw [siteOption, dif_pos hxΓ] at hρ
      unfold siteOption at hρ
      split_ifs at hρ with hyΓ
      exact hadj.ne (congrArg Subtype.val (Option.some.inj hρ))
    exact ⟨⟨f, hs⟩, Subtype.ext (Subtype.ext hf)⟩

/-- Surviving copies are in bijection with the lattice edges meeting `Γ`. -/
def copyMeetEquiv : Copy (WiredTrees.graph N) (roots Γ N) ≃ MeetEdge Γ :=
  Equiv.ofBijective _ (copyMeet_bijective Γ N hΓ)

end Contraction

/-- Translation of lattice edges meeting `Γ`. -/
def shiftMeet (z : Site 2) (Γ : Set (Site 2)) : MeetEdge Γ ≃ MeetEdge (shiftSet z Γ) where
  toFun e := ⟨shiftEdge z e.val, by
    obtain ⟨x, hx, hxΓ⟩ := e.property
    refine ⟨x + z, (mem_shiftEdge z e.val (x + z)).mpr ?_, (add_mem_shiftSet z Γ x).mpr hxΓ⟩
    simpa only [add_sub_cancel_right] using hx⟩
  invFun e := ⟨shiftEdge (-z) e.val, by
    obtain ⟨x, hx, hxΓ⟩ := e.property
    refine ⟨x - z, (mem_shiftEdge (-z) e.val (x - z)).mpr ?_, hxΓ⟩
    simpa only [sub_neg_eq_add, sub_add_cancel] using hx⟩
  left_inv e := Subtype.ext (shiftEdge_neg_shiftEdge z e.val)
  right_inv e := Subtype.ext (shiftEdge_shiftEdge_neg z e.val)

section Shift

variable (z : Site 2) (Γ : Set (Site 2)) {N M : ℕ} (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x)
  (hΓ' : ∀ x ∈ shiftSet z Γ, FiniteWired.inBox M x)
include hΓ hΓ'

/-- Translation of contracted vertices. -/
def vertexShift : Vertex (roots Γ N) ≃ Vertex (roots (shiftSet z Γ) M) :=
  (quotientSiteEquiv Γ N hΓ).trans
    ((shiftOption z Γ).trans (quotientSiteEquiv (shiftSet z Γ) M hΓ').symm)

/-- Translation of surviving copies. -/
def copyShift : Copy (WiredTrees.graph N) (roots Γ N) ≃
    Copy (WiredTrees.graph M) (roots (shiftSet z Γ) M) :=
  (copyMeetEquiv Γ N hΓ).trans ((shiftMeet z Γ).trans (copyMeetEquiv (shiftSet z Γ) M hΓ').symm)

theorem copyShift_edge (c : Copy (WiredTrees.graph N) (roots Γ N)) :
    TreeMeasurability11.originalCopyEdge (copyShift z Γ hΓ hΓ' c).val =
      shiftEdge z (TreeMeasurability11.originalCopyEdge c.val) :=
  congrArg Subtype.val ((copyMeetEquiv (shiftSet z Γ) M hΓ').apply_symm_apply
    (shiftMeet z Γ (copyMeetEquiv Γ N hΓ c)))

theorem copyShift_endpoints (c : Copy (WiredTrees.graph N) (roots Γ N)) :
    ((graph (WiredTrees.graph M) (roots (shiftSet z Γ) M)).left (copyShift z Γ hΓ hΓ' c) =
        vertexShift z Γ hΓ hΓ' ((graph (WiredTrees.graph N) (roots Γ N)).left c) ∧
      (graph (WiredTrees.graph M) (roots (shiftSet z Γ) M)).right (copyShift z Γ hΓ hΓ' c) =
        vertexShift z Γ hΓ hΓ' ((graph (WiredTrees.graph N) (roots Γ N)).right c)) ∨
    ((graph (WiredTrees.graph M) (roots (shiftSet z Γ) M)).left (copyShift z Γ hΓ hΓ' c) =
        vertexShift z Γ hΓ hΓ' ((graph (WiredTrees.graph N) (roots Γ N)).right c) ∧
      (graph (WiredTrees.graph M) (roots (shiftSet z Γ) M)).right (copyShift z Γ hΓ hΓ' c) =
        vertexShift z Γ hΓ hΓ' ((graph (WiredTrees.graph N) (roots Γ N)).left c)) := by
  let q := quotientSiteEquiv Γ N hΓ
  let q' := quotientSiteEquiv (shiftSet z Γ) M hΓ'
  let c' := copyShift z Γ hΓ hΓ' c
  have hc := endpoints_siteOption (shiftSet z Γ) M hΓ' c'.val
  rw [copyShift_edge] at hc
  change _ = Sym2.map (siteOption (shiftSet z Γ))
    (Sym2.map (· + z) (TreeMeasurability11.originalCopyEdge c.val).val) at hc
  rw [Sym2.map_map] at hc
  have hfun : siteOption (shiftSet z Γ) ∘ (· + z) = shiftOption z Γ ∘ siteOption Γ := by
    funext x
    exact siteOption_add z Γ x
  rw [hfun, ← Sym2.map_map, ← endpoints_siteOption Γ N hΓ c.val, Sym2.map_mk] at hc
  change s(q' ((graph (WiredTrees.graph M) (roots (shiftSet z Γ) M)).left c'),
    q' ((graph (WiredTrees.graph M) (roots (shiftSet z Γ) M)).right c')) =
    s(shiftOption z Γ (q ((graph (WiredTrees.graph N) (roots Γ N)).left c)),
      shiftOption z Γ (q ((graph (WiredTrees.graph N) (roots Γ N)).right c))) at hc
  rcases Sym2.eq_iff.mp hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨q'.eq_symm_apply.mpr h1, q'.eq_symm_apply.mpr h2⟩
  · exact Or.inr ⟨q'.eq_symm_apply.mpr h1, q'.eq_symm_apply.mpr h2⟩

/-- Translation of spanning trees of the contracted graphs. -/
def shiftTreeEquiv :
    (graph (WiredTrees.graph N) (roots Γ N)).ComponentTree Set.univ ≃
      (graph (WiredTrees.graph M) (roots (shiftSet z Γ) M)).ComponentTree Set.univ where
  toFun t := ⟨t.val.image (copyShift z Γ hΓ hΓ'),
    (Multigraph.copiedEquiv_tree_iff _ _ (vertexShift z Γ hΓ hΓ')
      (copyShift z Γ hΓ hΓ') (copyShift_endpoints z Γ hΓ hΓ') t.val).mpr t.property⟩
  invFun t := ⟨t.val.image (copyShift z Γ hΓ hΓ').symm, by
    apply (Multigraph.copiedEquiv_tree_iff _ _ (vertexShift z Γ hΓ hΓ')
      (copyShift z Γ hΓ hΓ') (copyShift_endpoints z Γ hΓ hΓ') _).mp
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
      Finset.image_id'] using t.property⟩
  left_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply,
      Finset.image_id']
  right_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
      Finset.image_id']

/-- Translation of rooted forest carriers. -/
def forestShift : Forest Γ N ≃ Forest (shiftSet z Γ) M :=
  (rootContractionEquiv (WiredTrees.graph N) (roots Γ N)).trans
    ((shiftTreeEquiv z Γ hΓ hΓ').trans
      (rootContractionEquiv (WiredTrees.graph M) (roots (shiftSet z Γ) M)).symm)

theorem forestField_forestShift (F : Forest Γ N) :
    forestField (shiftSet z Γ) (forestShift z Γ hΓ hΓ' F).val =
      shiftField z (forestField Γ F.val) := by
  funext e
  apply Bool.eq_iff_iff.mpr
  change _ ↔ forestField Γ F.val (shiftEdge (-z) e) = true
  rw [forestField_eq_true, forestField_eq_true]
  change (∃ c ∈ liftCopies (WiredTrees.graph M) (roots (shiftSet z Γ) M)
    ((projectCopies (WiredTrees.graph N) (roots Γ N) F.val).image (copyShift z Γ hΓ hΓ')), _) ↔ _
  constructor
  · rintro ⟨c, hc, hce, hcΓ⟩
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hc'
    refine ⟨c₀.val, (mem_projectCopies _ _ _ _).mp hc₀, ?_, ?_⟩
    · rw [← hce, copyShift_edge, shiftEdge_neg_shiftEdge]
    · intro x hx
      have h := hcΓ (x - -z) ((mem_shiftEdge (-z) e x).mp hx)
      change x - -z - z ∈ Γ at h
      simpa only [sub_neg_eq_add, add_sub_cancel_right] using h
  · rintro ⟨c, hc, hce, hcΓ⟩
    have hc' : c ∈ liftCopies (WiredTrees.graph N) (roots Γ N)
        (projectCopies (WiredTrees.graph N) (roots Γ N) F.val) := by
      rw [lift_project_forest _ _ F.property]
      exact hc
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hc'
    refine ⟨(copyShift z Γ hΓ hΓ' c₀).val,
      Finset.mem_image.mpr ⟨copyShift z Γ hΓ hΓ' c₀, Finset.mem_image_of_mem _ hc₀, rfl⟩, ?_, ?_⟩
    · rw [copyShift_edge, hce, shiftEdge_shiftEdge_neg]
    · intro x hx
      exact hcΓ (x - z) ((mem_shiftEdge (-z) e (x - z)).mpr (by
        simpa only [sub_neg_eq_add, sub_add_cancel] using hx))

/-- The rooted forest law of a translate is the translate of the rooted forest law. -/
theorem forestLaw_shiftSet :
    forestLaw (shiftSet z Γ) M = (forestLaw Γ N).map (shiftField z) := by
  have hmap : (fun F : Forest (shiftSet z Γ) M => forestField (shiftSet z Γ) F.val) ∘
      forestShift z Γ hΓ hΓ' = shiftField z ∘ fun F : Forest Γ N => forestField Γ F.val := by
    funext F
    rw [Function.comp_apply, Function.comp_apply]
    exact forestField_forestShift z Γ hΓ hΓ' F
  rw [forestLaw, forestLaw, Measure.map_map (measurable_shiftField z) (measurable_of_countable _),
    ← hmap, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    FiniteAvalanches.uniform_measure_map_equiv]

end Shift

/-- The wired uniform spanning tree of `ℤ²` is invariant under every translation. -/
theorem squareLatticeUST_map_shiftField (z : Site 2) :
    (squareLatticeUST : Measure EdgeField).map (shiftField z) = squareLatticeUST := by
  obtain ⟨K, hK⟩ := exists_inBox_finset {z}
  have hz := hK z (Finset.mem_singleton_self z)
  have h1 := forestProbability_tendsto (fun n => boxSet n) (fun n => n) (fun _ _ hx => hx)
    (fun m => eventually_atTop.mpr ⟨m, fun _ hn => boxSet_mono hn⟩)
  have h2 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h1
    (continuous_shiftField z)
  have hM : ∀ n, ∀ x ∈ shiftSet z (boxSet n), FiniteWired.inBox (n + K) x := by
    intro n x hx i
    have h1 := hx i
    have h2 := hz i
    simp only [Pi.sub_apply] at h1
    push_cast
    constructor <;> omega
  have hΓ : ∀ m, ∀ᶠ n in atTop, boxSet m ⊆ shiftSet z (boxSet n) := by
    intro m
    refine eventually_atTop.mpr ⟨m + K, fun n hn x hx i => ?_⟩
    have h1 := hx i
    have h2 := hz i
    have hn' : ((m + K : ℕ) : ℤ) ≤ n := by exact_mod_cast hn
    push_cast at hn'
    simp only [Pi.sub_apply]
    constructor <;> omega
  have h3 := forestProbability_tendsto (fun n => shiftSet z (boxSet n)) (fun n => n + K) hM hΓ
  have he : (fun n => (forestProbability (boxSet n) n).map
      (continuous_shiftField z).measurable.aemeasurable) =
      fun n => forestProbability (shiftSet z (boxSet n)) (n + K) := by
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, forestProbability_toMeasure, forestProbability_toMeasure,
      forestLaw_shiftSet z (boxSet n) (fun _ hx => hx) (hM n)]
  rw [he] at h2
  exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique h2 h3)

end

end FiniteAvalanches.Wilson.Lattice.SiteRoots
