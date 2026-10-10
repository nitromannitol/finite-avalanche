import FiniteAvalanches.Trees.RootedForests
import FiniteAvalanches.Trees.Ancestors
import Mathlib.Data.Fintype.Card

/-! A fixed copied connector tree completes to a spanning tree precisely by
adjoining a rooted forest on its vertex support. Original copy identities and
isolated roots are retained. -/
set_option autoImplicit false
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E)

private theorem connector_reaches_map {A B : Finset E} (f : V → V)
    (hstep : ∀ e ∈ A, G.reaches B (f (G.left e)) (f (G.right e)))
    {x y : V} (h : G.reaches A x y) : G.reaches B (f x) (f y) := by
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨e, he, hxy | hxy⟩ := hab
    · apply ih.trans
      change G.reaches B (f a) (f b)
      rw [← hxy.1,← hxy.2]
      exact hstep e he
    · apply ih.trans
      change G.reaches B (f a) (f b)
      rw [← hxy.1,← hxy.2]
      exact G.reaches_symm (hstep e he)

private theorem connector_path_adj_of_reaches {T A : Finset E}
    (hT : G.is_tree Set.univ T) (hAT : A ⊆ T) {r s x y : V}
    (hA : G.reaches A r s)
    (he : s(x,y) ∈ (path (G.toSimple_isTree hT) r s).edges) : G.adjacent A x y := by
  obtain ⟨p⟩ := (G.toSimple_reachable A r s).mpr hA
  have hle : G.toSimple A ≤ G.toSimple T := by
    intro a b hab
    obtain ⟨e, he, hxy⟩ := hab
    exact ⟨e, hAT he, hxy⟩
  have hp := path_eq (G.toSimple_isTree hT)
    (p.toPath.val.mapLe hle) (p.toPath.property.mapLe hle)
  rw [hp] at he
  have he' : s(x,y) ∈ p.toPath.val.edges := by
    simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he
  exact p.toPath.val.adj_of_mem_edges he'

/-- In an actual copied tree, two disjoint copied subgraphs cannot both connect
 two distinct vertices. Copy injectivity is used only on the containing forest. -/
private theorem connector_eq_of_disjoint_reaches {T H F : Finset E}
    (hT : G.is_tree Set.univ T) (hHT : H ⊆ T) (hFT : F ⊆ T)
    (hdis : Disjoint H F) {r s : V} (hH : G.reaches H r s)
    (hF : G.reaches F r s) : r = s := by
  by_contra hne
  obtain ⟨z, _hrz, _q, hp⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne
    (path (G.toSimple_isTree hT) r s)
  have he : s(r,z) ∈ (path (G.toSimple_isTree hT) r s).edges := by
    rw [hp]
    exact List.mem_cons_self
  obtain ⟨e, heH, hexy⟩ := connector_path_adj_of_reaches G hT hHT hH he
  obtain ⟨f, hfF, hfxy⟩ := connector_path_adj_of_reaches G hT hFT hF he
  have hEe : G.edge e = s(r,z) := by
    rcases hexy with h | h
    · simp only [edge, h.1, h.2]
    · simp only [edge, h.1, h.2, Sym2.eq_swap]
  have hEf : G.edge f = s(r,z) := by
    rcases hfxy with h | h
    · simp only [edge, h.1, h.2]
    · simp only [edge, h.1, h.2, Sym2.eq_swap]
  have hef : e = f := G.edge_injOn_of_is_forest hT.2.2.2
    (hHT heH) (hFT hfF) (hEe.trans hEf.symm)
  exact Finset.disjoint_left.mp hdis heH (hef.symm ▸ hfF)

/-- All connector copies join two distinct roots, so no rooted forest selects
 any of them; distinct parallel root-root copies are excluded as well. -/
theorem rootedForest_disjoint_connector {R : Set V} {H F : Finset E}
    (hH : G.supported R H) (hF : G.is_rooted_forest R F) : Disjoint H F := by
  apply Finset.disjoint_left.mpr
  intro e heH heF
  obtain ⟨r, _, _, hu⟩ := hF.2 (G.left e)
  have hl : G.left e = r := hu _ (hH e heH).1 .refl
  have hr : G.right e = r := hu _ (hH e heH).2
    (.single ⟨e, heF, Or.inl ⟨rfl, rfl⟩⟩)
  exact G.loopless e (hl.trans hr.symm)

/-- Joining a fixed tree on the prescribed roots to a disjoint copied subset
 gives a spanning tree exactly when that subset is a rooted spanning forest. -/
theorem rootedForest_iff_connector_union_tree (R : Set V) (H F : Finset E)
    (hH : G.is_tree R H) (hdis : Disjoint H F) :
    G.is_rooted_forest R F ↔ G.is_tree Set.univ (H ∪ F) := by
  have hHU : H ⊆ H ∪ F := fun _ he => Finset.mem_union_left F he
  have hFU : F ⊆ H ∪ F := fun _ he => Finset.mem_union_right H he
  constructor
  · intro hF
    let ρ : V → V := fun x => (hF.2 x).choose
    have hρ (x : V) : ρ x ∈ R ∧ G.reaches F x (ρ x) ∧
        ∀ r ∈ R, G.reaches F x r → r = ρ x := (hF.2 x).choose_spec
    have hρroot (x : V) (hx : x ∈ R) : ρ x = x := ((hρ x).2.2 x hx .refl).symm
    have hρeq {x y : V} (hxy : G.reaches F x y) : ρ x = ρ y :=
      ((hρ x).2.2 _ (hρ y).1 (hxy.trans (hρ y).2.1)).symm
    refine ⟨⟨hH.1.choose, Set.mem_univ _⟩, ?_, ?_, ?_⟩
    · intro e he
      exact ⟨Set.mem_univ _, Set.mem_univ _⟩
    · intro x _ y _
      exact (G.reaches_mono hFU (hρ x).2.1).trans
        ((G.reaches_mono hHU (hH.2.2.1 _ (hρ x).1 _ (hρ y).1)).trans
          (G.reaches_symm (G.reaches_mono hFU (hρ y).2.1)))
    · intro e he halt
      rcases Finset.mem_union.mp he with heH | heF
      · have hstep : ∀ f ∈ (H ∪ F).erase e,
            G.reaches (H.erase e) (ρ (G.left f)) (ρ (G.right f)) := by
          intro f hf
          obtain ⟨hfe, hfU⟩ := Finset.mem_erase.mp hf
          rcases Finset.mem_union.mp hfU with hfH | hfF
          · rw [hρroot _ (hH.2.1 f hfH).1, hρroot _ (hH.2.1 f hfH).2]
            exact .single ⟨f, Finset.mem_erase.mpr ⟨hfe, hfH⟩, Or.inl ⟨rfl, rfl⟩⟩
          · rw [hρeq (.single ⟨f, hfF, Or.inl ⟨rfl, rfl⟩⟩)]
            exact .refl
        have hp := connector_reaches_map G ρ hstep halt
        apply hH.2.2.2 e heH
        simpa only [hρroot _ (hH.2.1 e heH).1,
          hρroot _ (hH.2.1 e heH).2] using hp
      · let r : V := ρ (G.left e)
        let π : V → V := fun x => if ρ x = r then x else r
        have hπroot (x : V) (hx : x ∈ R) : π x = r := by
          dsimp only [π]
          rw [hρroot x hx]
          split_ifs with h
          · exact h
          · rfl
        have hstep : ∀ f ∈ (H ∪ F).erase e,
            G.reaches (F.erase e) (π (G.left f)) (π (G.right f)) := by
          intro f hf
          obtain ⟨hfe, hfU⟩ := Finset.mem_erase.mp hf
          rcases Finset.mem_union.mp hfU with hfH | hfF
          · rw [hπroot _ (hH.2.1 f hfH).1, hπroot _ (hH.2.1 f hfH).2]
            exact .refl
          · have hroots := hρeq (.single ⟨f, hfF, Or.inl ⟨rfl, rfl⟩⟩)
            by_cases hl : ρ (G.left f) = r
            · have hr : ρ (G.right f) = r := hroots.symm.trans hl
              simp only [π, hl, hr, ↓reduceIte]
              exact .single ⟨f, Finset.mem_erase.mpr ⟨hfe, hfF⟩, Or.inl ⟨rfl, rfl⟩⟩
            · have hr : ρ (G.right f) ≠ r := fun h => hl (hroots.trans h)
              simp only [π, hl, hr, ↓reduceIte]
              exact .refl
        have hπleft : π (G.left e) = G.left e := by
          dsimp only [π]
          exact if_pos rfl
        have hρright : ρ (G.right e) = r :=
          (hρeq (.single ⟨e, heF, Or.inl ⟨rfl, rfl⟩⟩)).symm
        have hπright : π (G.right e) = G.right e := by
          dsimp only [π]
          exact if_pos hρright
        apply hF.1 e heF
        simpa only [hπleft, hπright] using connector_reaches_map G π hstep halt
  · intro hT
    refine ⟨G.is_forest_mono hFU hT.2.2.2, ?_⟩
    intro x
    obtain ⟨r₀, hr₀⟩ := hH.1
    have hhit : ∀ {y : V}, G.reaches (H ∪ F) x y →
        G.reaches F x y ∨ ∃ r ∈ R, G.reaches F x r := by
      intro y hy
      induction hy with
      | refl => exact Or.inl .refl
      | @tail a b _ hab ih =>
        rcases ih with ha | hr
        · obtain ⟨e, he, hxy⟩ := hab
          rcases Finset.mem_union.mp he with heH | heF
          · have haR : a ∈ R := by
              rcases hxy with h | h
              · exact h.1 ▸ (hH.2.1 e heH).1
              · exact h.1 ▸ (hH.2.1 e heH).2
            exact Or.inr ⟨a, haR, ha⟩
          · exact Or.inl (ha.tail ⟨e, heF, hxy⟩)
        · exact Or.inr hr
    obtain ⟨r, hr, hxr⟩ : ∃ r ∈ R, G.reaches F x r := by
      rcases hhit (hT.2.2.1 x (Set.mem_univ _) r₀ (Set.mem_univ _)) with hp | hp
      · exact ⟨r₀, hr₀, hp⟩
      · exact hp
    refine ⟨r, hr, hxr, ?_⟩
    intro s hs hxs
    exact connector_eq_of_disjoint_reaches G hT hHU hFU hdis
      (hH.2.2.1 s hs r hr) ((G.reaches_symm hxs).trans hxr)

omit [Fintype E] in
private theorem connector_union_sdiff (H T : Finset E) (hHT : H ⊆ T) : H ∪ (T \ H) = T := by
  ext e
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (heH | ⟨heT, _⟩)
    · exact hHT heH
    · exact heT
  · intro heT
    by_cases heH : e ∈ H
    · exact Or.inl heH
    · exact Or.inr ⟨heT, heH⟩

/-- Literal completion by adjoining H; both maps retain original copy IDs. -/
def connectorCompletionEquiv (R : Set V) (H : Finset E) (hH : G.is_tree R H) :
    {t : G.SpanningTree // H ⊆ t.val} ≃ G.RootedForest R where
  toFun t := ⟨t.val.val \ H, by
    have hd : Disjoint H (t.val.val \ H) := Finset.disjoint_left.mpr
      (fun _ heH heD => (Finset.mem_sdiff.mp heD).2 heH)
    apply (G.rootedForest_iff_connector_union_tree R H (t.val.val \ H) hH hd).mpr
    rw [connector_union_sdiff H t.val.val t.property]
    exact t.val.property⟩
  invFun F := ⟨⟨H ∪ F.val,
    (G.rootedForest_iff_connector_union_tree R H F.val hH
      (G.rootedForest_disjoint_connector hH.2.1 F.property)).mp F.property⟩,
    fun _ he => Finset.mem_union_left F.val he⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    change H ∪ (t.val.val \ H) = t.val.val
    exact connector_union_sdiff H t.val.val t.property
  right_inv F := by
    apply Subtype.ext
    change (H ∪ F.val) \ H = F.val
    have hd := G.rootedForest_disjoint_connector hH.2.1 F.property
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨heH | heF, hnH⟩
      · exact False.elim (hnH heH)
      · exact heF
    · intro heF
      exact ⟨Or.inr heF, fun heH => Finset.disjoint_left.mp hd heH heF⟩

@[simp] theorem connectorCompletionEquiv_to_copies (R : Set V) (H : Finset E)
    (hH : G.is_tree R H) (t : {t : G.SpanningTree // H ⊆ t.val}) :
    (G.connectorCompletionEquiv R H hH t).val = t.val.val \ H := rfl

@[simp] theorem connectorCompletionEquiv_symm_copies (R : Set V) (H : Finset E)
    (hH : G.is_tree R H) (F : G.RootedForest R) :
    ((G.connectorCompletionEquiv R H hH).symm F).val.val = H ∪ F.val := rfl

/-- Exact whole original-copy completion denominator, without renormalization. -/
theorem card_connector_completions (R : Set V) (H : Finset E)
    (hH : G.is_tree R H) :
    Nat.card {t : G.SpanningTree // H ⊆ t.val} = Nat.card (G.RootedForest R) :=
  Nat.card_congr (G.connectorCompletionEquiv R H hH)

end
end FiniteAvalanches.Trees.Multigraph
