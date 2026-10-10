module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic

@[expose] public section

/-! Unique paths, actual connecting subtrees, and lowest common ancestors in finite trees. -/
open scoped Classical
namespace FiniteAvalanches.Trees.RootedPaths
variable {V : Type*} {T : SimpleGraph V} (hT : T.IsTree)

/-- The unique simple path; its existence and uniqueness precede this choice. -/
noncomputable def path (x y : V) : T.Walk x y := (hT.existsUnique_path x y).choose

theorem path_isPath (x y : V) : (path hT x y).IsPath :=
  (hT.existsUnique_path x y).choose_spec.1

theorem path_eq {x y : V} (p : T.Walk x y) (hp : p.IsPath) : path hT x y = p :=
  ((hT.existsUnique_path x y).choose_spec.2 p hp).symm

theorem path_reverse (x y : V) : path hT x y = (path hT y x).reverse :=
  path_eq hT _ (path_isPath hT y x).reverse

theorem path_takeUntil {r x a : V} (ha : a ∈ (path hT r x).support) :
    path hT r a = (path hT r x).takeUntil a ha :=
  path_eq hT _ ((path_isPath hT r x).takeUntil ha)

theorem path_dropUntil {r x a : V} (ha : a ∈ (path hT r x).support) :
    path hT a x = (path hT r x).dropUntil a ha :=
  path_eq hT _ ((path_isPath hT r x).dropUntil ha)

theorem path_split {r x a : V} (ha : a ∈ (path hT r x).support) :
    path hT r x = (path hT r a).append (path hT a x) := by
  rw [path_takeUntil hT ha, path_dropUntil hT ha]
  exact ((path hT r x).take_spec ha).symm

/-- a is on the unique path from the root r to x. -/
def ancestor (r a x : V) : Prop := a ∈ (path hT r x).support

theorem ancestor_refl (r x : V) : ancestor hT r x x := (path hT r x).end_mem_support

theorem ancestor_root (r x : V) : ancestor hT r r x := (path hT r x).start_mem_support

theorem ancestor_trans {r a b x : V} (hab : ancestor hT r a b)
    (hbx : ancestor hT r b x) : ancestor hT r a x := by
  have h := (path hT r x).support_takeUntil_subset_support hbx
  rw [← path_takeUntil hT hbx] at h
  exact h hab

theorem ancestor_length_le {r a x : V} (ha : ancestor hT r a x) :
    (path hT r a).length ≤ (path hT r x).length := by
  rw [path_takeUntil hT ha]
  exact (path hT r x).length_takeUntil_le_length ha

theorem ancestor_length_lt {r a x : V} (ha : ancestor hT r a x) (hne : a ≠ x) :
    (path hT r a).length < (path hT r x).length := by
  rw [path_takeUntil hT ha]
  exact (path hT r x).length_takeUntil_lt_length ha hne

theorem ancestor_antisymm {r a b : V} (hab : ancestor hT r a b)
    (hba : ancestor hT r b a) : a = b := by
  by_contra hne
  exact (Nat.not_lt_of_ge (ancestor_length_le hT hba)) (ancestor_length_lt hT hab hne)

theorem ancestor_of_length_le {r a b x : V} (ha : ancestor hT r a x)
    (hb : ancestor hT r b x) (hle : (path hT r a).length ≤ (path hT r b).length) :
    ancestor hT r a b := by
  have hget := (path hT r x).getVert_takeUntil hb
    (show (path hT r a).length ≤ ((path hT r x).takeUntil b hb).length by
      rwa [← path_takeUntil hT hb])
  have haeq : (path hT r x).getVert (path hT r a).length = a := by
    rw [path_takeUntil hT ha]
    exact (path hT r x).getVert_length_takeUntil ha
  unfold ancestor
  rw [path_takeUntil hT hb]
  rw [← haeq, ← hget]
  exact ((path hT r x).takeUntil b hb).getVert_mem_support _

theorem ancestor_comparable {r a b x : V} (ha : ancestor hT r a x)
    (hb : ancestor hT r b x) : ancestor hT r a b ∨ ancestor hT r b a := by
  rcases le_total (path hT r a).length (path hT r b).length with h | h
  · exact Or.inl (ancestor_of_length_le hT ha hb h)
  · exact Or.inr (ancestor_of_length_le hT hb ha h)

/-- The lowest common ancestor, characterized entirely by actual rooted paths. -/
def is_common_ancestor (r : V) (S : Set V) (a : V) : Prop :=
  (∀ x ∈ S, ancestor hT r a x) ∧
    ∀ b, (∀ x ∈ S, ancestor hT r b x) → ancestor hT r b a

theorem existsUnique_common_ancestor [Fintype V] (r : V) (S : Set V) (hS : S.Nonempty) :
    ∃! a, is_common_ancestor hT r S a := by
  let A : Finset V := Finset.univ.filter fun a => ∀ x ∈ S, ancestor hT r a x
  have hA : A.Nonempty := ⟨r, by simp [A, ancestor_root]⟩
  obtain ⟨a, ha, hmax⟩ := A.exists_max_image (fun a => (path hT r a).length) hA
  have hac : ∀ x ∈ S, ancestor hT r a x := (Finset.mem_filter.mp ha).2
  obtain ⟨x, hx⟩ := hS
  have hca : is_common_ancestor hT r S a := by
    refine ⟨hac, fun b hb => ?_⟩
    exact ancestor_of_length_le hT (hb x hx) (hac x hx) (hmax b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩))
  refine ⟨a, hca, ?_⟩
  intro b hb
  exact ancestor_antisymm hT (hca.2 b hb.1) (hb.2 a hac)

/-- The unique lowest common ancestor; no root or ancestor witness is supplied as input. -/
noncomputable def commonAncestor [Fintype V] (r : V) (S : Set V) (hS : S.Nonempty) : V :=
  (existsUnique_common_ancestor hT r S hS).choose

theorem commonAncestor_spec [Fintype V] (r : V) (S : Set V) (hS : S.Nonempty) :
    is_common_ancestor hT r S (commonAncestor hT r S hS) :=
  (existsUnique_common_ancestor hT r S hS).choose_spec.1

/-- The actual connecting subtree: the union of unique paths between marked vertices. -/
def connectingSubtree (S : Set V) : Set V :=
  {a | ∃ x ∈ S, ∃ y ∈ S, a ∈ (path hT x y).support}

theorem subset_connectingSubtree (S : Set V) : S ⊆ connectingSubtree hT S := by
  intro x hx
  exact ⟨x, hx, x, hx, (path hT x x).start_mem_support⟩

theorem path_subset_union (x y a : V) :
    ∀ ⦃z⦄, z ∈ (path hT x y).support →
      z ∈ (path hT x a).support ∨ z ∈ (path hT a y).support := by
  let w := (path hT x a).append (path hT a y)
  have he := path_eq hT w.toPath.val w.toPath.property
  rw [he]
  intro z hz
  have hz' := w.support_toPath_subset_support hz
  simpa only [w, SimpleGraph.Walk.mem_support_append_iff] using hz'

theorem ancestor_on_suffix {r a x z : V} (ha : ancestor hT r a x)
    (hz : z ∈ (path hT a x).support) : ancestor hT r a z := by
  have hsplit := path_split hT ha
  have hzx : ancestor hT r z x := by
    unfold ancestor
    rw [hsplit]
    exact SimpleGraph.Walk.support_subset_support_append_right _ _ hz
  rcases ancestor_comparable hT ha hzx with h | h
  · exact h
  · by_cases hza : z = a
    · subst z; exact ancestor_refl hT r a
    · have hp : ((path hT r a).append (path hT a x)).IsPath :=
        hsplit ▸ path_isPath hT r x
      exact (hp.ne_of_mem_support_of_append hza h hz rfl).elim

theorem connectingSubtree_subset_descendants (r : V) (S : Set V) {a : V}
    (ha : ∀ x ∈ S, ancestor hT r a x) :
    connectingSubtree hT S ⊆ {z | ancestor hT r a z} := by
  rintro z ⟨x, hx, y, hy, hz⟩
  rcases path_subset_union hT x y a hz with hz | hz
  · have hz' : z ∈ (path hT a x).support := by
      rw [path_reverse hT x a, SimpleGraph.Walk.support_reverse] at hz
      exact List.mem_reverse.mp hz
    exact ancestor_on_suffix hT (ha x hx) hz'
  · exact ancestor_on_suffix hT (ha y hy) hz

/-- Path convexity is the connected-subtree condition in a tree. -/
def is_path_convex (C : Set V) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ (path hT x y).support, z ∈ C

theorem connectingSubtree_minimal (S C : Set V) (hC : is_path_convex hT C) (hSC : S ⊆ C) :
    connectingSubtree hT S ⊆ C := by
  rintro z ⟨x, hx, y, hy, hz⟩
  exact hC x (hSC hx) y (hSC hy) z hz

theorem path_from_mark_subset_connectingSubtree {S : Set V} {b x : V} (hb : b ∈ S)
    (hx : x ∈ connectingSubtree hT S) :
    ∀ z ∈ (path hT b x).support, z ∈ connectingSubtree hT S := by
  obtain ⟨u, hu, v, hv, hxuv⟩ := hx
  have hcase := path_subset_union hT u v b hxuv
  have hx' : (∃ y ∈ S, x ∈ (path hT b y).support) := by
    rcases hcase with h | h
    · refine ⟨u, hu, ?_⟩
      rw [path_reverse hT u b, SimpleGraph.Walk.support_reverse] at h
      exact List.mem_reverse.mp h
    · exact ⟨v, hv, h⟩
  obtain ⟨y, hy, hxy⟩ := hx'
  intro z hz
  have hz' : z ∈ (path hT b y).support := by
    rw [path_takeUntil hT hxy] at hz
    exact (path hT b y).support_takeUntil_subset_support hxy hz
  exact ⟨b, hb, y, hy, hz'⟩

theorem connectingSubtree_convex (S : Set V) (hS : S.Nonempty) :
    is_path_convex hT (connectingSubtree hT S) := by
  obtain ⟨b, hb⟩ := hS
  intro x hx y hy z hz
  rcases path_subset_union hT x y b hz with h | h
  · rw [path_reverse hT x b, SimpleGraph.Walk.support_reverse] at h
    exact path_from_mark_subset_connectingSubtree hT hb hx z (List.mem_reverse.mp h)
  · exact path_from_mark_subset_connectingSubtree hT hb hy z h

theorem connectingSubtree_connected (S : Set V) (hS : S.Nonempty) :
    (T.induce (connectingSubtree hT S)).Connected := by
  have hconv := connectingSubtree_convex hT S hS
  obtain ⟨x, hx⟩ := hS
  letI : Nonempty (connectingSubtree hT S) := ⟨⟨x, subset_connectingSubtree hT S hx⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro x y
  exact ⟨((path hT x.val y.val).induce (connectingSubtree hT S)
    (fun z hz => hconv
      x.val x.property y.val y.property z hz)).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

theorem common_ancestor_mem_connectingSubtree {r : V} {S : Set V} (hS : S.Nonempty)
    {a : V} (ha : is_common_ancestor hT r S a) : a ∈ connectingSubtree hT S := by
  by_contra hnot
  obtain ⟨x, hx⟩ := hS
  have hax : a ≠ x := fun h => hnot (h ▸ subset_connectingSubtree hT S hx)
  obtain ⟨b, hab, q, hp⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hax (path hT a x)
  have hq : q.IsPath ∧ a ∉ q.support := by
    have h := path_isPath hT a x
    rw [hp, SimpleGraph.Walk.cons_isPath_iff] at h
    exact h
  have hba : b ∈ (path hT a x).support := by
    rw [hp]
    exact List.mem_cons_of_mem _ q.start_mem_support
  have hab' := ancestor_on_suffix hT (ha.1 x hx) hba
  have hbcommon : ∀ y ∈ S, ancestor hT r b y := by
    intro y hy
    let w := q.append (path hT x y)
    have haw : a ∉ w.support := by
      intro h
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp h with h | h
      · exact hq.2 h
      · exact hnot ⟨x, hx, y, hy, h⟩
    have han : a ∉ w.toPath.val.support :=
      fun h => haw (w.support_toPath_subset_support h)
    have hpy : path hT a y = SimpleGraph.Walk.cons hab w.toPath.val :=
      path_eq hT _ (w.toPath.property.cons han)
    have hby : b ∈ (path hT a y).support := by
      rw [hpy]
      exact List.mem_cons_of_mem _ w.toPath.val.start_mem_support
    unfold ancestor
    rw [path_split hT (ha.1 y hy)]
    exact SimpleGraph.Walk.support_subset_support_append_right _ _ hby
  exact hab.ne (ancestor_antisymm hT hab' (ha.2 b hbcommon))

theorem commonAncestor_mem_connectingSubtree [Fintype V] (r : V) (S : Set V) (hS : S.Nonempty) :
    commonAncestor hT r S hS ∈ connectingSubtree hT S :=
  common_ancestor_mem_connectingSubtree hT hS (commonAncestor_spec hT r S hS)

/-- A common ancestor equals the lowest common ancestor exactly when it lies in the
actual minimal connecting subtree; no arbitrary joining set is supplied. -/
theorem commonAncestor_eq_iff_mem_connectingSubtree [Fintype V] (r : V) (S : Set V) (hS : S.Nonempty)
    {a : V} (ha : ∀ x ∈ S, ancestor hT r a x) :
    commonAncestor hT r S hS = a ↔ a ∈ connectingSubtree hT S := by
  constructor
  · intro h
    exact h ▸ commonAncestor_mem_connectingSubtree hT r S hS
  · intro h
    have hc := commonAncestor_spec hT r S hS
    exact ancestor_antisymm hT
      (connectingSubtree_subset_descendants hT r S hc.1 h) (hc.2 a ha)

end FiniteAvalanches.Trees.RootedPaths
