import FiniteAvalanches.Trees.ConnectorCompletion
import FiniteAvalanches.Trees.Ancestors
import FiniteAvalanches.Trees.Past

/-! Zero-root dictionary for a copied connector: deleting the connector copies `H` from a
spanning tree `t` leaves a rooted forest on the connector support `R`, and its zero-root
component is exactly the ancestor past of `a` for the sink `s`. -/
set_option autoImplicit false
open scoped Classical
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Tree paths between vertices joined inside `A ⊆ T` use only copies of `A`. -/
private theorem zeroRoot_path_edge_adj {T A : Finset E}
    (hT : G.is_tree Set.univ T) (hAT : A ⊆ T) {r p x y : V}
    (hA : G.reaches A r p)
    (he : s(x, y) ∈ (path (G.toSimple_isTree hT) r p).edges) : G.adjacent A x y := by
  obtain ⟨q⟩ := (G.toSimple_reachable A r p).mpr hA
  have hle : G.toSimple A ≤ G.toSimple T := by
    intro a b hab
    obtain ⟨e, he', hxy⟩ := hab
    exact ⟨e, hAT he', hxy⟩
  have hp := path_eq (G.toSimple_isTree hT)
    (q.toPath.val.mapLe hle) (q.toPath.property.mapLe hle)
  rw [hp] at he
  have he' : s(x, y) ∈ q.toPath.val.edges := by
    simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using he
  exact q.toPath.val.adj_of_mem_edges he'

/-- A walk whose copies all lie in `A` gives reachability through copies of `A`. -/
private theorem zeroRoot_reaches_of_walk {A : Finset E} {T : SimpleGraph V} {x y : V}
    (q : T.Walk x y) :
    (∀ a b : V, s(a, b) ∈ q.edges → G.adjacent A a b) → G.reaches A x y := by
  induction q with
  | nil => intro _; exact Relation.ReflTransGen.refl
  | @cons u u' w hadj p ih =>
    intro hq
    exact Relation.ReflTransGen.head (hq u u' (by simp))
      (ih fun a b hab => hq a b (by simp [hab]))

/-- A walk ending in a root meets a root that is reached from its start in the forest. -/
private theorem zeroRoot_exists_reached {T : SimpleGraph V} {R : Set V} {A : Finset E}
    (hstep : ∀ u u' : V, u ∉ R → T.Adj u u' → G.adjacent A u u') {x y : V}
    (q : T.Walk x y) : y ∈ R → ∃ c ∈ q.support, c ∈ R ∧ G.reaches A x c := by
  induction q with
  | @nil u =>
    intro hy
    exact ⟨u, SimpleGraph.Walk.start_mem_support _, hy, Relation.ReflTransGen.refl⟩
  | @cons u u' w hadj p ih =>
    intro hy
    by_cases hu : u ∈ R
    · exact ⟨u, SimpleGraph.Walk.start_mem_support _, hu, Relation.ReflTransGen.refl⟩
    · obtain ⟨c, hc, hcR, hreach⟩ := ih hy
      exact ⟨c, by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hc, hcR,
        Relation.ReflTransGen.head (hstep u u' hu hadj) hreach⟩

/-- The zero-root component of the copied forest `t \ H` on the connector support `R` is the
ancestor past of `a` for the sink `s`. -/
theorem oneVertices_sdiff_connector_eq_descendants (t : G.SpanningTree) (R : Set V)
    (H : Finset E) (hH : G.is_tree R H) (hHt : H ⊆ t.val) {s a : V}
    (hs : s ∈ R) (ha : a ∈ R) :
    G.oneVertices (t.val \ H) (R ∩ G.descendants t s a) = G.descendants t s a := by
  have hT := G.toSimple_isTree t.property
  have hdis : Disjoint H (t.val \ H) := by
    apply Finset.disjoint_left.mpr
    intro e heH heD
    exact (Finset.mem_sdiff.mp heD).2 heH
  have hU : H ∪ (t.val \ H) = t.val := by
    ext x
    rw [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact hHt h
      · exact h
    · intro hx
      by_cases hxH : x ∈ H
      · exact Or.inl hxH
      · exact Or.inr ⟨hx, hxH⟩
  have hF : G.is_rooted_forest R (t.val \ H) :=
    (G.rootedForest_iff_connector_union_tree R H (t.val \ H) hH hdis).mpr
      (by rw [hU]; exact t.property)
  have hroot := hF.2
  have hsubF : t.val \ H ⊆ t.val := fun x hx => (Finset.mem_sdiff.mp hx).1
  -- a copy of `t` leaving the complement of `R` cannot be a connector copy
  have hFadj : ∀ u u' : V, u ∉ R → (G.toSimple t.val).Adj u u' →
      G.adjacent (t.val \ H) u u' := by
    rintro u u' hu ⟨e, he, huv⟩
    refine ⟨e, Finset.mem_sdiff.mpr ⟨he, fun heH => hu ?_⟩, huv⟩
    rcases huv with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [← h1]; exact (hH.2.1 e heH).1
    · rw [← h1]; exact (hH.2.1 e heH).2
  have hself : ∀ w ∈ R, ∀ z ∈ R, G.reaches (t.val \ H) w z → z = w := by
    intro w hw z hz hwz
    obtain ⟨r, _, _, hu⟩ := hroot w
    exact (hu z hz hwz).trans (hu w hw Relation.ReflTransGen.refl).symm
  have hsub : ∀ x y w : V, w ∈ (path hT x y).support →
      ∀ f : Sym2 V, f ∈ (path hT w y).edges → f ∈ (path hT x y).edges := by
    intro x y w hw f hf
    rw [path_split hT hw]
    simp only [SimpleGraph.Walk.edges_append, List.mem_append]
    exact Or.inr hf
  have key : ∀ v z : V, z ∈ R → G.reaches (t.val \ H) v z →
      (v ∈ G.descendants t s a ↔ z ∈ G.descendants t s a) := by
    intro v z hz hvz
    obtain ⟨r, _, _, hu⟩ := hroot v
    have hzr : z = r := hu z hz hvz
    -- the forest root of `v` lies on the tree path from `v` to the sink
    obtain ⟨c, hcp, hcR, hvc⟩ := zeroRoot_exists_reached G hFadj (path hT v s) hs
    have hcz : c = z := (hu c hcR hvc).trans hzr.symm
    rw [hcz] at hcp
    have hzv : ancestor hT s z v := by
      show z ∈ (path hT s v).support
      rw [path_reverse hT s v, SimpleGraph.Walk.support_reverse, List.mem_reverse]
      exact hcp
    have hF_on : ∀ a' b : V, s(a', b) ∈ (path hT v z).edges →
        G.adjacent (t.val \ H) a' b :=
      fun a' b h => zeroRoot_path_edge_adj G t.property hsubF hvz h
    -- no connector root other than `z` lies on the forest path from `v` to `z`
    have hC2 : ∀ w ∈ R, w ∈ (path hT v z).support → w = z := by
      intro w hw hwp
      have hwz : G.reaches (t.val \ H) w z :=
        zeroRoot_reaches_of_walk G (path hT w z)
          (fun a' b h => hF_on a' b (hsub v z w hwp s(a', b) h))
      exact (hself w hw z hz hwz).symm
    have hzd : v ∈ G.descendants t s a ↔ z ∈ G.descendants t s a := by
      show ancestor hT s a v ↔ ancestor hT s a z
      constructor
      · intro hav
        have hav' : a ∈ (path hT s v).support := hav
        rcases path_subset_union hT s v z hav' with h | h
        · exact h
        · have h' : a ∈ (path hT v z).support := by
            rw [path_reverse hT v z, SimpleGraph.Walk.support_reverse, List.mem_reverse]
            exact h
          rw [hC2 a ha h']
          exact ancestor_refl hT s z
      · intro haz
        exact ancestor_trans hT haz hzv
    exact hzd
  ext v
  simp only [oneVertices, Set.mem_setOf_eq, Set.mem_inter_iff]
  obtain ⟨z0, hz0R, hvz0, huniq⟩ := hroot v
  have hkey := key v z0 hz0R hvz0
  constructor
  · rintro ⟨z, ⟨hzR, hzd⟩, hvz⟩
    rw [huniq z hzR hvz] at hzd
    exact hkey.mpr hzd
  · intro hv
    exact ⟨z0, ⟨hz0R, hkey.mp hv⟩, hvz0⟩

/-- The same identity for the outgoing-edge past of a nonroot common ancestor. -/
theorem oneVertices_sdiff_connector_eq_past (t : G.SpanningTree) (R : Set V)
    (H : Finset E) (hH : G.is_tree R H) (hHt : H ⊆ t.val) {s a : V}
    (hs : s ∈ R) (ha : a ∈ R) (hne : a ≠ s) :
    G.oneVertices (t.val \ H) (R ∩ G.past t s a hne) = G.past t s a hne := by
  rw [G.past_eq_descendants t s a hne]
  exact G.oneVertices_sdiff_connector_eq_descendants t R H hH hHt hs ha

end FiniteAvalanches.Trees.Multigraph

#check @FiniteAvalanches.Trees.Multigraph.oneVertices_sdiff_connector_eq_descendants
#print axioms FiniteAvalanches.Trees.Multigraph.oneVertices_sdiff_connector_eq_descendants
#check @FiniteAvalanches.Trees.Multigraph.oneVertices_sdiff_connector_eq_past
#print axioms FiniteAvalanches.Trees.Multigraph.oneVertices_sdiff_connector_eq_past
