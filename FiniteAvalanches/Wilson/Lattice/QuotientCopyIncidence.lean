import FiniteAvalanches.Wilson.Lattice.ForestCopyRestriction

/-! Incidence transport on the existing nonempty-root quotients. Original
copies remain individual IDs; negative exits may reverse ordered endpoints. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open LatticeProb FiniteAvalanches.Sandpile
open CopiedNetwork.NonemptyQuotient
open scoped Classical
noncomputable section

theorem quotientVertexEquiv_project_active {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (x : FiniteWired.Active N) :
    quotientVertexEquiv hNM R houtside (project (wiredRoots R N) (some x)) =
      project (wiredRoots R M) (some (activeEmbedding hNM x)) := by
  by_cases hx : (some x : FiniteWired.Vertex N) ∈ (wiredRoots R N).val
  · have hx' : (some (activeEmbedding hNM x) : FiniteWired.Vertex M) ∈
        (wiredRoots R M).val := hx
    rw [project,dif_pos hx,project,dif_pos hx']
    rfl
  · have hx' : (some (activeEmbedding hNM x) : FiniteWired.Vertex M) ∉
        (wiredRoots R M).val := hx
    rw [project,dif_neg hx,project,dif_neg hx']
    rfl

theorem project_wired_sink (R : RootPair) (N : ℕ) :
    project (wiredRoots R N) (none : FiniteWired.Vertex N) = none :=
  (project_eq_none _ _).mpr (Or.inr trivial)

theorem project_exterior_active {N M : ℕ} (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (x : FiniteWired.Active M) (hx : ¬FiniteWired.inBox N (FiniteWired.site x)) :
    project (wiredRoots R M) (some x) = none :=
  (project_eq_none _ _).mpr (Or.inr (houtside _ hx))

/-- The actual contracted endpoints of every copied small edge match those
of its actual large representative, allowing an orientation reversal. -/
theorem copyInLarger_quotient_endpoints {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) (e : FiniteWired.Edge N) :
    (project (wiredRoots R M) ((FiniteWired.endpoints (copyInLarger hNM e)).1) =
        quotientVertexEquiv hNM R houtside
          (project (wiredRoots R N) ((FiniteWired.endpoints e).1)) ∧
      project (wiredRoots R M) ((FiniteWired.endpoints (copyInLarger hNM e)).2) =
        quotientVertexEquiv hNM R houtside
          (project (wiredRoots R N) ((FiniteWired.endpoints e).2))) ∨
    (project (wiredRoots R M) ((FiniteWired.endpoints (copyInLarger hNM e)).1) =
        quotientVertexEquiv hNM R houtside
          (project (wiredRoots R N) ((FiniteWired.endpoints e).2)) ∧
      project (wiredRoots R M) ((FiniteWired.endpoints (copyInLarger hNM e)).2) =
        quotientVertexEquiv hNM R houtside
          (project (wiredRoots R N) ((FiniteWired.endpoints e).1))) := by
  cases e with
  | inl e =>
    exact Or.inl ⟨(quotientVertexEquiv_project_active hNM R houtside e.val.1).symm,
      (quotientVertexEquiv_project_active hNM R houtside e.val.2).symm⟩
  | inr e =>
    rcases e with ⟨⟨x,⟨i,b⟩⟩,he⟩
    cases b
    · change ¬FiniteWired.inBox N (FiniteWired.site x + -unit i) at he
      simp only [copyInLarger,FiniteWired.directionEdge]
      split_ifs with hm
      · have ho := project_exterior_active R houtside
          (FiniteWired.activeOfSite M (FiniteWired.site (activeEmbedding hNM x) - unit i) hm)
          (by simpa only [FiniteWired.site_activeOfSite,site_activeEmbedding,
            sub_eq_add_neg] using he)
        exact Or.inr ⟨by simpa only [FiniteWired.endpoints,project_wired_sink,
          quotientVertexEquiv_none] using ho,
          (quotientVertexEquiv_project_active hNM R houtside x).symm⟩
      · exact Or.inl ⟨(quotientVertexEquiv_project_active hNM R houtside x).symm,
          by
            change project (wiredRoots R M) (none : FiniteWired.Vertex M) =
              quotientVertexEquiv hNM R houtside
                (project (wiredRoots R N) (none : FiniteWired.Vertex N))
            rw [project_wired_sink,project_wired_sink,quotientVertexEquiv_none]⟩
    · change ¬FiniteWired.inBox N (FiniteWired.site x + unit i) at he
      simp only [copyInLarger,FiniteWired.directionEdge]
      split_ifs with hm
      · have ho := project_exterior_active R houtside
          (FiniteWired.activeOfSite M (FiniteWired.site (activeEmbedding hNM x) + unit i) hm)
          (by simpa only [FiniteWired.site_activeOfSite,site_activeEmbedding] using he)
        exact Or.inl ⟨(quotientVertexEquiv_project_active hNM R houtside x).symm,
          by simpa only [FiniteWired.endpoints,project_wired_sink,
            quotientVertexEquiv_none] using ho⟩
      · exact Or.inl ⟨(quotientVertexEquiv_project_active hNM R houtside x).symm,
          by
            change project (wiredRoots R M) (none : FiniteWired.Vertex M) =
              quotientVertexEquiv hNM R houtside
                (project (wiredRoots R N) (none : FiniteWired.Vertex N))
            rw [project_wired_sink,project_wired_sink,quotientVertexEquiv_none]⟩

/-- Survival is tested on actual contracted endpoints, not endpoint supports. -/
theorem copyInLarger_survives_iff {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) (e : FiniteWired.Edge N) :
    project (wiredRoots R M) ((WiredTrees.graph M).left (copyInLarger hNM e)) ≠
        project (wiredRoots R M) ((WiredTrees.graph M).right (copyInLarger hNM e)) ↔
      project (wiredRoots R N) ((WiredTrees.graph N).left e) ≠
        project (wiredRoots R N) ((WiredTrees.graph N).right e) := by
  change (project (wiredRoots R M) (FiniteWired.endpoints (copyInLarger hNM e)).1 ≠
      project (wiredRoots R M) (FiniteWired.endpoints (copyInLarger hNM e)).2) ↔
    (project (wiredRoots R N) (FiniteWired.endpoints e).1 ≠
      project (wiredRoots R N) (FiniteWired.endpoints e).2)
  rcases copyInLarger_quotient_endpoints hNM R houtside e with ⟨hl,hr⟩ | ⟨hl,hr⟩
  ·
    rw [hl,hr]
    exact not_congr (quotientVertexEquiv hNM R houtside).injective.eq_iff
  · rw [hl,hr]
    exact (not_congr (quotientVertexEquiv hNM R houtside).injective.eq_iff).trans ne_comm

/-- Every surviving large-quotient copy is incident to an actual small-box
nonroot; root-root exterior edges are deleted by the existing quotient. -/
theorem surviving_large_copy_in_range {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (e : Copy (WiredTrees.graph M) (wiredRoots R M)) :
    ∃ f : FiniteWired.Edge N, copyInLarger hNM f = e.val := by
  have hn : (WiredTrees.graph M).left e.val ∉ (wiredRoots R M).val ∨
      (WiredTrees.graph M).right e.val ∉ (wiredRoots R M).val := by
    by_cases hl : (WiredTrees.graph M).left e.val ∈ (wiredRoots R M).val
    · exact Or.inr (fun hr => e.property
        ((contracted_loop_iff (WiredTrees.graph M) (wiredRoots R M) e.val).mpr ⟨hl,hr⟩))
    · exact Or.inl hl
  rcases hn with hn | hn
  · obtain ⟨x,hx,hxin⟩ := nonroot_inside R houtside _ hn
    let a := FiniteWired.activeOfSite N (FiniteWired.site x) hxin
    have ha : activeEmbedding hNM a = x := FiniteWired.site_injective M rfl
    exact copyInLarger_covers_incident hNM a e.val (Or.inl (hx.trans (congrArg some ha).symm))
  · obtain ⟨x,hx,hxin⟩ := nonroot_inside R houtside _ hn
    let a := FiniteWired.activeOfSite N (FiniteWired.site x) hxin
    have ha : activeEmbedding hNM a = x := FiniteWired.site_injective M rfl
    exact copyInLarger_covers_incident hNM a e.val (Or.inr (hx.trans (congrArg some ha).symm))

/-- Surviving copies keep their original IDs; only endpoint-root labels change. -/
def quotientCopyMap {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (e : Copy (WiredTrees.graph N) (wiredRoots R N)) :
    Copy (WiredTrees.graph M) (wiredRoots R M) :=
  ⟨copyInLarger hNM e.val,(copyInLarger_survives_iff hNM R houtside e.val).mpr e.property⟩

theorem quotientCopyMap_bijective {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) :
    Function.Bijective (quotientCopyMap hNM R houtside) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact copyInLarger_injective hNM (congrArg Subtype.val hab)
  · intro e
    obtain ⟨f,hf⟩ := surviving_large_copy_in_range hNM R houtside e
    have hs : project (wiredRoots R N) ((WiredTrees.graph N).left f) ≠
        project (wiredRoots R N) ((WiredTrees.graph N).right f) :=
      (copyInLarger_survives_iff hNM R houtside f).mp (hf.symm ▸ e.property)
    exact ⟨⟨f,hs⟩,Subtype.ext hf⟩

/-- Actual quotient copied-edge equivalence, not an equivalence supplied as a premise. -/
def quotientCopyEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) :
    Copy (WiredTrees.graph N) (wiredRoots R N) ≃
      Copy (WiredTrees.graph M) (wiredRoots R M) :=
  Equiv.ofBijective (quotientCopyMap hNM R houtside)
    (quotientCopyMap_bijective hNM R houtside)

@[simp] theorem quotientCopyEquiv_val {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (e : Copy (WiredTrees.graph N) (wiredRoots R N)) :
    (quotientCopyEquiv hNM R houtside e).val = copyInLarger hNM e.val := rfl

theorem quotientCopyEquiv_endpoints {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (e : Copy (WiredTrees.graph N) (wiredRoots R N)) :
    ((graph (WiredTrees.graph M) (wiredRoots R M)).left (quotientCopyEquiv hNM R houtside e) =
        quotientVertexEquiv hNM R houtside ((graph (WiredTrees.graph N) (wiredRoots R N)).left e) ∧
      (graph (WiredTrees.graph M) (wiredRoots R M)).right (quotientCopyEquiv hNM R houtside e) =
        quotientVertexEquiv hNM R houtside ((graph (WiredTrees.graph N) (wiredRoots R N)).right e)) ∨
    ((graph (WiredTrees.graph M) (wiredRoots R M)).left (quotientCopyEquiv hNM R houtside e) =
        quotientVertexEquiv hNM R houtside ((graph (WiredTrees.graph N) (wiredRoots R N)).right e) ∧
      (graph (WiredTrees.graph M) (wiredRoots R M)).right (quotientCopyEquiv hNM R houtside e) =
        quotientVertexEquiv hNM R houtside ((graph (WiredTrees.graph N) (wiredRoots R N)).left e)) :=
  copyInLarger_quotient_endpoints hNM R houtside e.val

end
end FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
