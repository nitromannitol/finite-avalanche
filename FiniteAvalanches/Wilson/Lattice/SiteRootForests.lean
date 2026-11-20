import FiniteAvalanches.Wilson.Lattice.FiniteBoxForestEquiv

/-! Rooted forests of wired boxes whose roots are the sink and every site outside a
fixed set `Γ`. When `Γ` lies in the smaller of two boxes, the two forest carriers are
in bijection by the lattice copy embedding `copyInLarger`. This is the cross-volume
equivalence of `WiredBoxCopies.finiteForestEquiv` for an arbitrary site-determined root
set, which may have no root inside the smaller box. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.SiteRoots

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open CopiedNetwork.NonemptyQuotient
open scoped Classical

noncomputable section

/-- The roots of a wired box relative to `Γ`: the sink and every site outside `Γ`. -/
def rootSet (Γ : Set (Site 2)) (N : ℕ) : Set (FiniteWired.Vertex N)
  | none => True
  | some x => FiniteWired.site x ∉ Γ

theorem none_mem_rootSet (Γ : Set (Site 2)) (N : ℕ) : (none : FiniteWired.Vertex N) ∈ rootSet Γ N :=
  trivial

theorem some_mem_rootSet (Γ : Set (Site 2)) (N : ℕ) (x : FiniteWired.Active N) :
    (some x : FiniteWired.Vertex N) ∈ rootSet Γ N ↔ FiniteWired.site x ∉ Γ := Iff.rfl

/-- The root set as a nonempty root family. -/
def roots (Γ : Set (Site 2)) (N : ℕ) : CopiedNetwork.Roots (V := FiniteWired.Vertex N) :=
  ⟨rootSet Γ N, ⟨none, trivial⟩⟩

/-- Rooted spanning forests of the wired box with roots the sink and the sites outside `Γ`. -/
abbrev Forest (Γ : Set (Site 2)) (N : ℕ) :=
  (WiredTrees.graph N).RootedForest (roots Γ N).val

/-- Nonroot vertices are the box sites of `Γ`. -/
def nonrootEquiv (Γ : Set (Site 2)) (N : ℕ) :
    {v : FiniteWired.Vertex N // v ∉ (roots Γ N).val} ≃
      {x : FiniteWired.Active N // FiniteWired.site x ∈ Γ} where
  toFun v := match hv : v.val with
    | none => False.elim (v.property (hv.symm ▸ trivial))
    | some x => ⟨x, by
        by_contra hx
        exact v.property (hv.symm ▸ hx)⟩
  invFun x := ⟨some x.val, fun h => h x.property⟩
  left_inv v := by
    rcases v with ⟨v, hv⟩
    cases v with
    | none => exact (hv trivial).elim
    | some x => rfl
  right_inv x := rfl

/-- The sites of `Γ` are the same in both boxes when `Γ` lies in the smaller one. -/
def activeEquiv {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) :
    {x : FiniteWired.Active N // FiniteWired.site x ∈ Γ} ≃
      {x : FiniteWired.Active M // FiniteWired.site x ∈ Γ} where
  toFun x := ⟨activeEmbedding hNM x.val, x.property⟩
  invFun x := ⟨FiniteWired.activeOfSite N (FiniteWired.site x.val) (hΓ _ x.property),
    x.property⟩
  left_inv _ := Subtype.ext (FiniteWired.site_injective N rfl)
  right_inv _ := Subtype.ext (FiniteWired.site_injective M rfl)

/-- The quotient vertex carriers of the two boxes agree. -/
def quotientVertexEquiv {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) :
    Vertex (roots Γ N) ≃ Vertex (roots Γ M) :=
  Equiv.optionCongr ((nonrootEquiv Γ N).trans
    ((activeEquiv hNM Γ hΓ).trans (nonrootEquiv Γ M).symm))

@[simp] theorem quotientVertexEquiv_none {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) :
    quotientVertexEquiv hNM Γ hΓ none = none := rfl

theorem quotientVertexEquiv_project_active {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) (x : FiniteWired.Active N) :
    quotientVertexEquiv hNM Γ hΓ (project (roots Γ N) (some x)) =
      project (roots Γ M) (some (activeEmbedding hNM x)) := by
  by_cases hx : (some x : FiniteWired.Vertex N) ∈ (roots Γ N).val
  · have hx' : (some (activeEmbedding hNM x) : FiniteWired.Vertex M) ∈ (roots Γ M).val := hx
    rw [project, dif_pos hx, project, dif_pos hx']
    rfl
  · have hx' : (some (activeEmbedding hNM x) : FiniteWired.Vertex M) ∉ (roots Γ M).val := hx
    rw [project, dif_neg hx, project, dif_neg hx']
    rfl

theorem project_sink (Γ : Set (Site 2)) (N : ℕ) :
    project (roots Γ N) (none : FiniteWired.Vertex N) = none :=
  (project_eq_none _ _).mpr trivial

theorem project_exterior_active {N M : ℕ} (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x)
    (x : FiniteWired.Active M) (hx : ¬FiniteWired.inBox N (FiniteWired.site x)) :
    project (roots Γ M) (some x) = none :=
  (project_eq_none _ _).mpr (fun h => hx (hΓ _ h))

/-- The contracted endpoints of every small copy match those of its large
representative, up to an orientation reversal. -/
theorem copyInLarger_quotient_endpoints {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) (e : FiniteWired.Edge N) :
    (project (roots Γ M) ((FiniteWired.endpoints (copyInLarger hNM e)).1) =
        quotientVertexEquiv hNM Γ hΓ (project (roots Γ N) ((FiniteWired.endpoints e).1)) ∧
      project (roots Γ M) ((FiniteWired.endpoints (copyInLarger hNM e)).2) =
        quotientVertexEquiv hNM Γ hΓ (project (roots Γ N) ((FiniteWired.endpoints e).2))) ∨
    (project (roots Γ M) ((FiniteWired.endpoints (copyInLarger hNM e)).1) =
        quotientVertexEquiv hNM Γ hΓ (project (roots Γ N) ((FiniteWired.endpoints e).2)) ∧
      project (roots Γ M) ((FiniteWired.endpoints (copyInLarger hNM e)).2) =
        quotientVertexEquiv hNM Γ hΓ (project (roots Γ N) ((FiniteWired.endpoints e).1))) := by
  cases e with
  | inl e =>
    exact Or.inl ⟨(quotientVertexEquiv_project_active hNM Γ hΓ e.val.1).symm,
      (quotientVertexEquiv_project_active hNM Γ hΓ e.val.2).symm⟩
  | inr e =>
    rcases e with ⟨⟨x, ⟨i, b⟩⟩, he⟩
    cases b
    · change ¬FiniteWired.inBox N (FiniteWired.site x + -unit i) at he
      simp only [copyInLarger, FiniteWired.directionEdge]
      split_ifs with hm
      · have ho := project_exterior_active Γ hΓ
          (FiniteWired.activeOfSite M (FiniteWired.site (activeEmbedding hNM x) - unit i) hm)
          (by simpa only [FiniteWired.site_activeOfSite, site_activeEmbedding,
            sub_eq_add_neg] using he)
        exact Or.inr ⟨by simpa only [FiniteWired.endpoints, project_sink,
          quotientVertexEquiv_none] using ho,
          (quotientVertexEquiv_project_active hNM Γ hΓ x).symm⟩
      · exact Or.inl ⟨(quotientVertexEquiv_project_active hNM Γ hΓ x).symm, by
          change project (roots Γ M) (none : FiniteWired.Vertex M) =
            quotientVertexEquiv hNM Γ hΓ (project (roots Γ N) (none : FiniteWired.Vertex N))
          rw [project_sink, project_sink, quotientVertexEquiv_none]⟩
    · change ¬FiniteWired.inBox N (FiniteWired.site x + unit i) at he
      simp only [copyInLarger, FiniteWired.directionEdge]
      split_ifs with hm
      · have ho := project_exterior_active Γ hΓ
          (FiniteWired.activeOfSite M (FiniteWired.site (activeEmbedding hNM x) + unit i) hm)
          (by simpa only [FiniteWired.site_activeOfSite, site_activeEmbedding] using he)
        exact Or.inl ⟨(quotientVertexEquiv_project_active hNM Γ hΓ x).symm,
          by simpa only [FiniteWired.endpoints, project_sink,
            quotientVertexEquiv_none] using ho⟩
      · exact Or.inl ⟨(quotientVertexEquiv_project_active hNM Γ hΓ x).symm, by
          change project (roots Γ M) (none : FiniteWired.Vertex M) =
            quotientVertexEquiv hNM Γ hΓ (project (roots Γ N) (none : FiniteWired.Vertex N))
          rw [project_sink, project_sink, quotientVertexEquiv_none]⟩

theorem copyInLarger_survives_iff {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) (e : FiniteWired.Edge N) :
    project (roots Γ M) ((WiredTrees.graph M).left (copyInLarger hNM e)) ≠
        project (roots Γ M) ((WiredTrees.graph M).right (copyInLarger hNM e)) ↔
      project (roots Γ N) ((WiredTrees.graph N).left e) ≠
        project (roots Γ N) ((WiredTrees.graph N).right e) := by
  change (project (roots Γ M) (FiniteWired.endpoints (copyInLarger hNM e)).1 ≠
      project (roots Γ M) (FiniteWired.endpoints (copyInLarger hNM e)).2) ↔
    (project (roots Γ N) (FiniteWired.endpoints e).1 ≠
      project (roots Γ N) (FiniteWired.endpoints e).2)
  rcases copyInLarger_quotient_endpoints hNM Γ hΓ e with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [hl, hr]
    exact not_congr (quotientVertexEquiv hNM Γ hΓ).injective.eq_iff
  · rw [hl, hr]
    exact (not_congr (quotientVertexEquiv hNM Γ hΓ).injective.eq_iff).trans ne_comm

theorem nonroot_inside {N M : ℕ} (Γ : Set (Site 2)) (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x)
    (v : FiniteWired.Vertex M) (hv : v ∉ (roots Γ M).val) :
    ∃ x : FiniteWired.Active M, v = some x ∧ FiniteWired.inBox N (FiniteWired.site x) := by
  cases v with
  | none => exact (hv trivial).elim
  | some x =>
    refine ⟨x, rfl, ?_⟩
    by_contra hx
    exact hv (fun h => hx (hΓ _ h))

theorem surviving_large_copy_in_range {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) (e : Copy (WiredTrees.graph M) (roots Γ M)) :
    ∃ f : FiniteWired.Edge N, copyInLarger hNM f = e.val := by
  have hn : (WiredTrees.graph M).left e.val ∉ (roots Γ M).val ∨
      (WiredTrees.graph M).right e.val ∉ (roots Γ M).val := by
    by_cases hl : (WiredTrees.graph M).left e.val ∈ (roots Γ M).val
    · exact Or.inr (fun hr => e.property
        ((contracted_loop_iff (WiredTrees.graph M) (roots Γ M) e.val).mpr ⟨hl, hr⟩))
    · exact Or.inl hl
  rcases hn with hn | hn
  · obtain ⟨x, hx, hxin⟩ := nonroot_inside Γ hΓ _ hn
    let a := FiniteWired.activeOfSite N (FiniteWired.site x) hxin
    have ha : activeEmbedding hNM a = x := FiniteWired.site_injective M rfl
    exact copyInLarger_covers_incident hNM a e.val (Or.inl (hx.trans (congrArg some ha).symm))
  · obtain ⟨x, hx, hxin⟩ := nonroot_inside Γ hΓ _ hn
    let a := FiniteWired.activeOfSite N (FiniteWired.site x) hxin
    have ha : activeEmbedding hNM a = x := FiniteWired.site_injective M rfl
    exact copyInLarger_covers_incident hNM a e.val (Or.inr (hx.trans (congrArg some ha).symm))

/-- Surviving copies keep their lattice identities. -/
def quotientCopyMap {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) (e : Copy (WiredTrees.graph N) (roots Γ N)) :
    Copy (WiredTrees.graph M) (roots Γ M) :=
  ⟨copyInLarger hNM e.val, (copyInLarger_survives_iff hNM Γ hΓ e.val).mpr e.property⟩

theorem quotientCopyMap_bijective {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) :
    Function.Bijective (quotientCopyMap hNM Γ hΓ) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact copyInLarger_injective hNM (congrArg Subtype.val hab)
  · intro e
    obtain ⟨f, hf⟩ := surviving_large_copy_in_range hNM Γ hΓ e
    have hs : project (roots Γ N) ((WiredTrees.graph N).left f) ≠
        project (roots Γ N) ((WiredTrees.graph N).right f) :=
      (copyInLarger_survives_iff hNM Γ hΓ f).mp (hf.symm ▸ e.property)
    exact ⟨⟨f, hs⟩, Subtype.ext hf⟩

def quotientCopyEquiv {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) :
    Copy (WiredTrees.graph N) (roots Γ N) ≃ Copy (WiredTrees.graph M) (roots Γ M) :=
  Equiv.ofBijective (quotientCopyMap hNM Γ hΓ) (quotientCopyMap_bijective hNM Γ hΓ)

theorem quotientCopyEquiv_endpoints {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) (e : Copy (WiredTrees.graph N) (roots Γ N)) :
    ((graph (WiredTrees.graph M) (roots Γ M)).left (quotientCopyEquiv hNM Γ hΓ e) =
        quotientVertexEquiv hNM Γ hΓ ((graph (WiredTrees.graph N) (roots Γ N)).left e) ∧
      (graph (WiredTrees.graph M) (roots Γ M)).right (quotientCopyEquiv hNM Γ hΓ e) =
        quotientVertexEquiv hNM Γ hΓ ((graph (WiredTrees.graph N) (roots Γ N)).right e)) ∨
    ((graph (WiredTrees.graph M) (roots Γ M)).left (quotientCopyEquiv hNM Γ hΓ e) =
        quotientVertexEquiv hNM Γ hΓ ((graph (WiredTrees.graph N) (roots Γ N)).right e) ∧
      (graph (WiredTrees.graph M) (roots Γ M)).right (quotientCopyEquiv hNM Γ hΓ e) =
        quotientVertexEquiv hNM Γ hΓ ((graph (WiredTrees.graph N) (roots Γ N)).left e)) :=
  copyInLarger_quotient_endpoints hNM Γ hΓ e.val

def quotientTreeEquiv {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) :
    (graph (WiredTrees.graph N) (roots Γ N)).ComponentTree Set.univ ≃
      (graph (WiredTrees.graph M) (roots Γ M)).ComponentTree Set.univ where
  toFun t := ⟨t.val.image (quotientCopyEquiv hNM Γ hΓ),
    (Multigraph.copiedEquiv_tree_iff _ _ (quotientVertexEquiv hNM Γ hΓ)
      (quotientCopyEquiv hNM Γ hΓ) (quotientCopyEquiv_endpoints hNM Γ hΓ)
      t.val).mpr t.property⟩
  invFun t := ⟨t.val.image (quotientCopyEquiv hNM Γ hΓ).symm, by
    apply (Multigraph.copiedEquiv_tree_iff _ _ (quotientVertexEquiv hNM Γ hΓ)
      (quotientCopyEquiv hNM Γ hΓ) (quotientCopyEquiv_endpoints hNM Γ hΓ) _).mp
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

theorem liftCopies_image_quotientCopyEquiv {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x)
    (t : Finset (Copy (WiredTrees.graph N) (roots Γ N))) :
    liftCopies (WiredTrees.graph M) (roots Γ M) (t.image (quotientCopyEquiv hNM Γ hΓ)) =
      (liftCopies (WiredTrees.graph N) (roots Γ N) t).image (copyInLarger hNM) := by
  change (t.image (quotientCopyEquiv hNM Γ hΓ)).image Subtype.val =
    (t.image Subtype.val).image (copyInLarger hNM)
  rw [Finset.image_image, Finset.image_image]
  rfl

/-- Cross-volume bijection of the rooted forest carriers. -/
def forestEquiv {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) : Forest Γ N ≃ Forest Γ M :=
  (rootContractionEquiv (WiredTrees.graph N) (roots Γ N)).trans
    ((quotientTreeEquiv hNM Γ hΓ).trans
      (rootContractionEquiv (WiredTrees.graph M) (roots Γ M)).symm)

@[simp] theorem forestEquiv_copies {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) (F : Forest Γ N) :
    (forestEquiv hNM Γ hΓ F).val = F.val.image (copyInLarger hNM) := by
  change liftCopies (WiredTrees.graph M) (roots Γ M)
      ((projectCopies (WiredTrees.graph N) (roots Γ N) F.val).image
        (quotientCopyEquiv hNM Γ hΓ)) = _
  rw [liftCopies_image_quotientCopyEquiv, lift_project_forest _ _ F.property]

theorem forest_count_eq {N M : ℕ} (hNM : N ≤ M) (Γ : Set (Site 2))
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox N x) :
    Nat.card (Forest Γ N) = Nat.card (Forest Γ M) :=
  Nat.card_congr (forestEquiv hNM Γ hΓ)

end

end FiniteAvalanches.Wilson.Lattice.SiteRoots
