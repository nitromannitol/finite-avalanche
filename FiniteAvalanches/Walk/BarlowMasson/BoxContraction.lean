import FiniteAvalanches.Wilson.Lattice.FiniteBoxForestEquiv

/-!
# Wired boxes whose exterior consists of roots of either color

The cross-volume forest equivalence `WiredBoxCopies.finiteForestEquiv` identifies the rooted
forests of two wired boxes `N ≤ M` when every site outside the box of size `N` is a one root.
The construction only uses that every such site is a root. This file carries out the same
construction when every site outside the box of size `N` is a root of either color. This allows
a root pair with no root at all inside the box of size `N`, whose forests in that box are the
spanning trees of the wired box rooted at its sink.

## Main statements

* `finiteForestEquiv`: the rooted forests of the boxes `N ≤ M` correspond, and
  `finiteForestEquiv_copies`: the correspondence keeps every original copied edge.
* `finiteForestCount_eq`: the two boxes have the same number of rooted forests.
-/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.WiredBoxCopies.ExteriorRoots

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open CopiedNetwork.NonemptyQuotient
open scoped Classical

noncomputable section

/-- The nonroot active sites of the two boxes agree. -/
def nonrootActiveEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) :
    {x : FiniteWired.Active N // FiniteWired.site x ∉ R.zero ∪ R.one} ≃
      {x : FiniteWired.Active M // FiniteWired.site x ∉ R.zero ∪ R.one} where
  toFun x := ⟨activeEmbedding hNM x.val, x.property⟩
  invFun x := ⟨FiniteWired.activeOfSite N (FiniteWired.site x.val) (by
    by_contra hx
    exact x.property (hext _ hx)), x.property⟩
  left_inv x := Subtype.ext (FiniteWired.site_injective N rfl)
  right_inv x := Subtype.ext (FiniteWired.site_injective M rfl)

/-- The vertices of the root-contracted quotients of the two boxes agree. -/
def quotientVertexEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) :
    CopiedNetwork.NonemptyQuotient.Vertex (wiredRoots R N) ≃
      CopiedNetwork.NonemptyQuotient.Vertex (wiredRoots R M) :=
  Equiv.optionCongr ((nonrootWiredEquiv R N).trans
    ((nonrootActiveEquiv hNM R hext).trans (nonrootWiredEquiv R M).symm))

@[simp] theorem quotientVertexEquiv_none {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) :
    quotientVertexEquiv hNM R hext none = none := rfl

/-- Every nonroot vertex of the larger box is a site of the smaller box. -/
theorem nonroot_inside {N M : ℕ} (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one)
    (v : FiniteWired.Vertex M) (hv : v ∉ (wiredRoots R M).val) :
    ∃ x : FiniteWired.Active M, v = some x ∧ FiniteWired.inBox N (FiniteWired.site x) := by
  cases v with
  | none => exact (hv (Or.inr trivial)).elim
  | some x =>
    refine ⟨x, rfl, ?_⟩
    by_contra hx
    exact hv (hext _ hx)

theorem quotientVertexEquiv_project_active {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one)
    (x : FiniteWired.Active N) :
    quotientVertexEquiv hNM R hext (project (wiredRoots R N) (some x)) =
      project (wiredRoots R M) (some (activeEmbedding hNM x)) := by
  by_cases hx : (some x : FiniteWired.Vertex N) ∈ (wiredRoots R N).val
  · have hx' : (some (activeEmbedding hNM x) : FiniteWired.Vertex M) ∈
        (wiredRoots R M).val := hx
    rw [project, dif_pos hx, project, dif_pos hx']
    rfl
  · have hx' : (some (activeEmbedding hNM x) : FiniteWired.Vertex M) ∉
        (wiredRoots R M).val := hx
    rw [project, dif_neg hx, project, dif_neg hx']
    rfl

theorem project_exterior_active {N M : ℕ} (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one)
    (x : FiniteWired.Active M) (hx : ¬FiniteWired.inBox N (FiniteWired.site x)) :
    project (wiredRoots R M) (some x) = none :=
  (project_eq_none _ _).mpr (hext _ hx)

/-- The contracted endpoints of every copied edge of the smaller box match those of its copy in
the larger box, up to orientation. -/
theorem copyInLarger_quotient_endpoints {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) (e : FiniteWired.Edge N) :
    (project (wiredRoots R M) ((FiniteWired.endpoints (copyInLarger hNM e)).1) =
        quotientVertexEquiv hNM R hext
          (project (wiredRoots R N) ((FiniteWired.endpoints e).1)) ∧
      project (wiredRoots R M) ((FiniteWired.endpoints (copyInLarger hNM e)).2) =
        quotientVertexEquiv hNM R hext
          (project (wiredRoots R N) ((FiniteWired.endpoints e).2))) ∨
    (project (wiredRoots R M) ((FiniteWired.endpoints (copyInLarger hNM e)).1) =
        quotientVertexEquiv hNM R hext
          (project (wiredRoots R N) ((FiniteWired.endpoints e).2)) ∧
      project (wiredRoots R M) ((FiniteWired.endpoints (copyInLarger hNM e)).2) =
        quotientVertexEquiv hNM R hext
          (project (wiredRoots R N) ((FiniteWired.endpoints e).1))) := by
  cases e with
  | inl e =>
    exact Or.inl ⟨(quotientVertexEquiv_project_active hNM R hext e.val.1).symm,
      (quotientVertexEquiv_project_active hNM R hext e.val.2).symm⟩
  | inr e =>
    rcases e with ⟨⟨x, ⟨i, b⟩⟩, he⟩
    cases b
    · change ¬FiniteWired.inBox N (FiniteWired.site x + -unit i) at he
      simp only [copyInLarger, FiniteWired.directionEdge]
      split_ifs with hm
      · have ho := project_exterior_active R hext
          (FiniteWired.activeOfSite M (FiniteWired.site (activeEmbedding hNM x) - unit i) hm)
          (by simpa only [FiniteWired.site_activeOfSite, site_activeEmbedding,
            sub_eq_add_neg] using he)
        exact Or.inr ⟨by simpa only [FiniteWired.endpoints, project_wired_sink,
          quotientVertexEquiv_none] using ho,
          (quotientVertexEquiv_project_active hNM R hext x).symm⟩
      · exact Or.inl ⟨(quotientVertexEquiv_project_active hNM R hext x).symm,
          by
            change project (wiredRoots R M) (none : FiniteWired.Vertex M) =
              quotientVertexEquiv hNM R hext
                (project (wiredRoots R N) (none : FiniteWired.Vertex N))
            rw [project_wired_sink, project_wired_sink, quotientVertexEquiv_none]⟩
    · change ¬FiniteWired.inBox N (FiniteWired.site x + unit i) at he
      simp only [copyInLarger, FiniteWired.directionEdge]
      split_ifs with hm
      · have ho := project_exterior_active R hext
          (FiniteWired.activeOfSite M (FiniteWired.site (activeEmbedding hNM x) + unit i) hm)
          (by simpa only [FiniteWired.site_activeOfSite, site_activeEmbedding] using he)
        exact Or.inl ⟨(quotientVertexEquiv_project_active hNM R hext x).symm,
          by simpa only [FiniteWired.endpoints, project_wired_sink,
            quotientVertexEquiv_none] using ho⟩
      · exact Or.inl ⟨(quotientVertexEquiv_project_active hNM R hext x).symm,
          by
            change project (wiredRoots R M) (none : FiniteWired.Vertex M) =
              quotientVertexEquiv hNM R hext
                (project (wiredRoots R N) (none : FiniteWired.Vertex N))
            rw [project_wired_sink, project_wired_sink, quotientVertexEquiv_none]⟩

/-- A copied edge survives the contraction in the larger box exactly when it survives in the
smaller box. -/
theorem copyInLarger_survives_iff {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) (e : FiniteWired.Edge N) :
    project (wiredRoots R M) ((WiredTrees.graph M).left (copyInLarger hNM e)) ≠
        project (wiredRoots R M) ((WiredTrees.graph M).right (copyInLarger hNM e)) ↔
      project (wiredRoots R N) ((WiredTrees.graph N).left e) ≠
        project (wiredRoots R N) ((WiredTrees.graph N).right e) := by
  change (project (wiredRoots R M) (FiniteWired.endpoints (copyInLarger hNM e)).1 ≠
      project (wiredRoots R M) (FiniteWired.endpoints (copyInLarger hNM e)).2) ↔
    (project (wiredRoots R N) (FiniteWired.endpoints e).1 ≠
      project (wiredRoots R N) (FiniteWired.endpoints e).2)
  rcases copyInLarger_quotient_endpoints hNM R hext e with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [hl, hr]
    exact not_congr (quotientVertexEquiv hNM R hext).injective.eq_iff
  · rw [hl, hr]
    exact (not_congr (quotientVertexEquiv hNM R hext).injective.eq_iff).trans ne_comm

/-- Every copied edge surviving the contraction in the larger box comes from the smaller box. -/
theorem surviving_large_copy_in_range {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one)
    (e : Copy (WiredTrees.graph M) (wiredRoots R M)) :
    ∃ f : FiniteWired.Edge N, copyInLarger hNM f = e.val := by
  have hn : (WiredTrees.graph M).left e.val ∉ (wiredRoots R M).val ∨
      (WiredTrees.graph M).right e.val ∉ (wiredRoots R M).val := by
    by_cases hl : (WiredTrees.graph M).left e.val ∈ (wiredRoots R M).val
    · exact Or.inr (fun hr => e.property
        ((contracted_loop_iff (WiredTrees.graph M) (wiredRoots R M) e.val).mpr ⟨hl, hr⟩))
    · exact Or.inl hl
  rcases hn with hn | hn
  · obtain ⟨x, hx, hxin⟩ := nonroot_inside R hext _ hn
    let a := FiniteWired.activeOfSite N (FiniteWired.site x) hxin
    have ha : activeEmbedding hNM a = x := FiniteWired.site_injective M rfl
    exact copyInLarger_covers_incident hNM a e.val (Or.inl (hx.trans (congrArg some ha).symm))
  · obtain ⟨x, hx, hxin⟩ := nonroot_inside R hext _ hn
    let a := FiniteWired.activeOfSite N (FiniteWired.site x) hxin
    have ha : activeEmbedding hNM a = x := FiniteWired.site_injective M rfl
    exact copyInLarger_covers_incident hNM a e.val (Or.inr (hx.trans (congrArg some ha).symm))

/-- Surviving copied edges of the smaller box, as surviving copied edges of the larger box. -/
def quotientCopyMap {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one)
    (e : Copy (WiredTrees.graph N) (wiredRoots R N)) :
    Copy (WiredTrees.graph M) (wiredRoots R M) :=
  ⟨copyInLarger hNM e.val, (copyInLarger_survives_iff hNM R hext e.val).mpr e.property⟩

theorem quotientCopyMap_bijective {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) :
    Function.Bijective (quotientCopyMap hNM R hext) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact copyInLarger_injective hNM (congrArg Subtype.val hab)
  · intro e
    obtain ⟨f, hf⟩ := surviving_large_copy_in_range hNM R hext e
    have hs : project (wiredRoots R N) ((WiredTrees.graph N).left f) ≠
        project (wiredRoots R N) ((WiredTrees.graph N).right f) :=
      (copyInLarger_survives_iff hNM R hext f).mp (hf.symm ▸ e.property)
    exact ⟨⟨f, hs⟩, Subtype.ext hf⟩

/-- The surviving copied edges of the two boxes correspond. -/
def quotientCopyEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) :
    Copy (WiredTrees.graph N) (wiredRoots R N) ≃
      Copy (WiredTrees.graph M) (wiredRoots R M) :=
  Equiv.ofBijective (quotientCopyMap hNM R hext) (quotientCopyMap_bijective hNM R hext)

theorem quotientCopyEquiv_endpoints {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one)
    (e : Copy (WiredTrees.graph N) (wiredRoots R N)) :
    ((graph (WiredTrees.graph M) (wiredRoots R M)).left (quotientCopyEquiv hNM R hext e) =
        quotientVertexEquiv hNM R hext ((graph (WiredTrees.graph N) (wiredRoots R N)).left e) ∧
      (graph (WiredTrees.graph M) (wiredRoots R M)).right (quotientCopyEquiv hNM R hext e) =
        quotientVertexEquiv hNM R hext ((graph (WiredTrees.graph N) (wiredRoots R N)).right e)) ∨
    ((graph (WiredTrees.graph M) (wiredRoots R M)).left (quotientCopyEquiv hNM R hext e) =
        quotientVertexEquiv hNM R hext ((graph (WiredTrees.graph N) (wiredRoots R N)).right e) ∧
      (graph (WiredTrees.graph M) (wiredRoots R M)).right (quotientCopyEquiv hNM R hext e) =
        quotientVertexEquiv hNM R hext ((graph (WiredTrees.graph N) (wiredRoots R N)).left e)) :=
  copyInLarger_quotient_endpoints hNM R hext e.val

/-- The spanning trees of the root-contracted quotients of the two boxes correspond. -/
def quotientTreeEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) :
    (graph (WiredTrees.graph N) (wiredRoots R N)).ComponentTree Set.univ ≃
      (graph (WiredTrees.graph M) (wiredRoots R M)).ComponentTree Set.univ where
  toFun t := ⟨t.val.image (quotientCopyEquiv hNM R hext),
    (Multigraph.copiedEquiv_tree_iff _ _ (quotientVertexEquiv hNM R hext)
      (quotientCopyEquiv hNM R hext) (quotientCopyEquiv_endpoints hNM R hext)
      t.val).mpr t.property⟩
  invFun t := ⟨t.val.image (quotientCopyEquiv hNM R hext).symm, by
    apply (Multigraph.copiedEquiv_tree_iff _ _ (quotientVertexEquiv hNM R hext)
      (quotientCopyEquiv hNM R hext) (quotientCopyEquiv_endpoints hNM R hext) _).mp
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
      Finset.image_id'] using t.property⟩
  left_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply, Finset.image_id']
  right_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id']

theorem liftCopies_image_quotientCopyEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one)
    (t : Finset (Copy (WiredTrees.graph N) (wiredRoots R N))) :
    liftCopies (WiredTrees.graph M) (wiredRoots R M) (t.image (quotientCopyEquiv hNM R hext)) =
      (liftCopies (WiredTrees.graph N) (wiredRoots R N) t).image (copyInLarger hNM) := by
  change (t.image (quotientCopyEquiv hNM R hext)).image Subtype.val =
    (t.image Subtype.val).image (copyInLarger hNM)
  rw [Finset.image_image, Finset.image_image]
  rfl

/-- The rooted forests of the two boxes correspond. -/
def finiteForestEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) :
    FiniteForest R N ≃ FiniteForest R M :=
  (rootContractionEquiv (WiredTrees.graph N) (wiredRoots R N)).trans
    ((quotientTreeEquiv hNM R hext).trans
      (rootContractionEquiv (WiredTrees.graph M) (wiredRoots R M)).symm)

@[simp] theorem finiteForestEquiv_copies {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) (F : FiniteForest R N) :
    (finiteForestEquiv hNM R hext F).val = F.val.image (copyInLarger hNM) := by
  change liftCopies (WiredTrees.graph M) (wiredRoots R M)
      ((projectCopies (WiredTrees.graph N) (wiredRoots R N) F.val).image
        (quotientCopyEquiv hNM R hext)) = _
  rw [liftCopies_image_quotientCopyEquiv, lift_project_forest _ _ F.property]

theorem finiteForestCount_eq {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) :
    finiteForestCount R N = finiteForestCount R M :=
  Nat.card_congr (finiteForestEquiv hNM R hext)

end

end FiniteAvalanches.Wilson.Lattice.WiredBoxCopies.ExteriorRoots
