import FiniteAvalanches.Wilson.Lattice.FiniteBoxForestEquiv

/-! Component colors on literal copied forests are unchanged by splitting the
one-colored exterior root. No Wilson-law equality is assumed. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

def collapseLarge {N M : ℕ} (_hNM : N ≤ M) : FiniteWired.Vertex M → FiniteWired.Vertex N
  | none => none
  | some x => wiredSite N (FiniteWired.site x)

@[simp] theorem collapseLarge_none {N M : ℕ} (hNM : N ≤ M) :
    collapseLarge hNM none = none := rfl

theorem collapseLarge_activeEmbedding {N M : ℕ} (hNM : N ≤ M)
    (x : FiniteWired.Active N) :
    collapseLarge hNM (some (activeEmbedding hNM x)) = some x := by
  have hx : FiniteWired.inBox N (FiniteWired.site x) := fun i => (x i).property
  change wiredSite N (FiniteWired.site x) = some x
  rw [wiredSite,dif_pos hx]
  exact congrArg some (FiniteWired.site_injective N rfl)

theorem collapseLarge_exterior_active {N M : ℕ} (hNM : N ≤ M)
    (x : FiniteWired.Active M) (hx : ¬FiniteWired.inBox N (FiniteWired.site x)) :
    collapseLarge hNM (some x) = none := by
  exact dif_neg hx

theorem collapseLarge_wiredSite {N M : ℕ} (hNM : N ≤ M) (x : Site 2) :
    collapseLarge hNM (wiredSite M x) = wiredSite N x := by
  by_cases hx : FiniteWired.inBox M x
  · rw [wiredSite,dif_pos hx]
    rfl
  · have hx' : ¬FiniteWired.inBox N x := fun hn => hx (inBox_mono hNM hn)
    rw [wiredSite,dif_neg hx,collapseLarge_none,wiredSite,dif_neg hx']

/-- Collapse preserves the unordered endpoints of every original copied edge. -/
theorem collapseLarge_copy_endpoints {N M : ℕ} (hNM : N ≤ M) (e : FiniteWired.Edge N) :
    (collapseLarge hNM ((FiniteWired.endpoints (copyInLarger hNM e)).1) =
        (FiniteWired.endpoints e).1 ∧
      collapseLarge hNM ((FiniteWired.endpoints (copyInLarger hNM e)).2) =
        (FiniteWired.endpoints e).2) ∨
    (collapseLarge hNM ((FiniteWired.endpoints (copyInLarger hNM e)).1) =
        (FiniteWired.endpoints e).2 ∧
      collapseLarge hNM ((FiniteWired.endpoints (copyInLarger hNM e)).2) =
        (FiniteWired.endpoints e).1) := by
  cases e with
  | inl e => exact Or.inl ⟨collapseLarge_activeEmbedding hNM e.val.1,
      collapseLarge_activeEmbedding hNM e.val.2⟩
  | inr e =>
    rcases e with ⟨⟨x,⟨i,b⟩⟩,he⟩
    cases b
    · change ¬FiniteWired.inBox N (FiniteWired.site x + -unit i) at he
      simp only [copyInLarger,FiniteWired.directionEdge]
      split_ifs with hm
      · have ho := collapseLarge_exterior_active hNM
          (FiniteWired.activeOfSite M (FiniteWired.site (activeEmbedding hNM x) - unit i) hm)
          (by simpa only [FiniteWired.site_activeOfSite,site_activeEmbedding,
            sub_eq_add_neg] using he)
        exact Or.inr ⟨ho,collapseLarge_activeEmbedding hNM x⟩
      · exact Or.inl ⟨collapseLarge_activeEmbedding hNM x,rfl⟩
    · change ¬FiniteWired.inBox N (FiniteWired.site x + unit i) at he
      simp only [copyInLarger,FiniteWired.directionEdge]
      split_ifs with hm
      · have ho := collapseLarge_exterior_active hNM
          (FiniteWired.activeOfSite M (FiniteWired.site (activeEmbedding hNM x) + unit i) hm)
          (by simpa only [FiniteWired.site_activeOfSite,site_activeEmbedding] using he)
        exact Or.inl ⟨collapseLarge_activeEmbedding hNM x,ho⟩
      · exact Or.inl ⟨collapseLarge_activeEmbedding hNM x,rfl⟩

 theorem finiteColors_reaches (R : RootPair) (N : ℕ) (F : FiniteForest R N)
    {x y : FiniteWired.Vertex N} (hxy : (WiredTrees.graph N).reaches F.val x y) :
    finiteColors R N F x = finiteColors R N F y := by
  unfold finiteColors
  apply Bool.decide_congr
  constructor
  · rintro ⟨r,hr,hxr⟩
    exact ⟨r,hr,((WiredTrees.graph N).reaches_symm hxy).trans hxr⟩
  · rintro ⟨r,hr,hyr⟩
    exact ⟨r,hr,hxy.trans hyr⟩

 theorem collapseLarge_mem_wiredZero {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (v : FiniteWired.Vertex M) (hv : v ∈ wiredZero R M) :
    collapseLarge hNM v ∈ wiredZero R N := by
  cases v with
  | none => exact hv.elim
  | some x =>
    have hx : FiniteWired.inBox N (FiniteWired.site x) := by
      by_contra hn
      exact Set.disjoint_left.mp R.disjoint hv (houtside _ hn)
    change wiredSite N (FiniteWired.site x) ∈ wiredZero R N
    rw [wiredSite,dif_pos hx]
    exact hv

 theorem collapseLarge_mem_wiredOne {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (v : FiniteWired.Vertex M) (hv : v ∈ wiredOne R M) :
    collapseLarge hNM v ∈ wiredOne R N := by
  cases v with
  | none => trivial
  | some x =>
    change wiredSite N (FiniteWired.site x) ∈ wiredOne R N
    by_cases hx : FiniteWired.inBox N (FiniteWired.site x)
    · rw [wiredSite,dif_pos hx]
      exact hv
    · rw [wiredSite,dif_neg hx]
      trivial

 theorem collapseLarge_color_reaches {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) (F : FiniteForest R N)
    {x y : FiniteWired.Vertex M}
    (hxy : (WiredTrees.graph M).reaches (finiteForestEquiv hNM R houtside F).val x y) :
    finiteColors R N F (collapseLarge hNM x) =
      finiteColors R N F (collapseLarge hNM y) := by
  induction hxy with
  | refl => rfl
  | tail _ he ih =>
    obtain ⟨e,he,hxy⟩ := he
    rw [finiteForestEquiv_copies] at he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    have hc := finiteColors_reaches R N F
      (Relation.ReflTransGen.single ⟨a,ha,Or.inl ⟨rfl,rfl⟩⟩)
    have heq : finiteColors R N F
          (collapseLarge hNM ((WiredTrees.graph M).left (copyInLarger hNM a))) =
        finiteColors R N F
          (collapseLarge hNM ((WiredTrees.graph M).right (copyInLarger hNM a))) := by
      change finiteColors R N F
          (collapseLarge hNM (FiniteWired.endpoints (copyInLarger hNM a)).1) =
        finiteColors R N F
          (collapseLarge hNM (FiniteWired.endpoints (copyInLarger hNM a)).2)
      rcases collapseLarge_copy_endpoints hNM a with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · rw [hl,hr]
        exact hc
      · rw [hl,hr]
        exact hc.symm
    rcases hxy with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact ih.trans (by simpa only [hl,hr] using heq)
    · exact ih.trans (by simpa only [hl,hr] using heq.symm)

/-- The actual component labels, including every original exterior root, agree. -/
theorem finiteForestEquiv_colors {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) (F : FiniteForest R N)
    (x : FiniteWired.Vertex M) :
    finiteColors R M (finiteForestEquiv hNM R houtside F) x =
      finiteColors R N F (collapseLarge hNM x) := by
  obtain ⟨r,hr,hxr,_⟩ := (finiteForestEquiv hNM R houtside F).property.2 x
  rw [finiteColors_reaches R M _ hxr,collapseLarge_color_reaches hNM R houtside F hxr]
  rcases hr with hz | ho
  · rw [finiteColors_zero R M _ hz,
      finiteColors_zero R N F (collapseLarge_mem_wiredZero hNM R houtside r hz)]
  · rw [finiteColors_one R M _ ho,
      finiteColors_one R N F (collapseLarge_mem_wiredOne hNM R r ho)]

/-- Equality holds at every actual lattice site, not just at the origin. -/
theorem finiteForestEquiv_site_colors {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one) (F : FiniteForest R N)
    (x : Site 2) :
    finiteColors R M (finiteForestEquiv hNM R houtside F) (wiredSite M x) =
      finiteColors R N F (wiredSite N x) := by
  rw [finiteForestEquiv_colors,collapseLarge_wiredSite]

end
end FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
