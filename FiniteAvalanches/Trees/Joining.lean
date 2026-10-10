module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic

@[expose] public section

/-!
Internal elementary infrastructure for copied-edge joining. Edges are elements of a finite
carrier, not endpoint pairs. A forest is an edge subset in which deleting any edge separates
its endpoints (the ordinary undirected forest criterion, including parallel-edge cycles).
No sandpile, burning, ancestor, or probability conclusion is assumed here.
-/
namespace FiniteAvalanches.Trees

structure Multigraph (V E : Type*) [Fintype V] [Fintype E] where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

/-- Adapter for a literal finite edge-copy carrier with ordered endpoint pairs. -/
def Multigraph.ofEndpoints {V E : Type*} [Fintype V] [Fintype E]
    (ends : E → V × V) (hne : ∀ e, (ends e).1 ≠ (ends e).2) : Multigraph V E :=
  ⟨fun e => (ends e).1, fun e => (ends e).2, hne⟩

open scoped Classical

namespace Multigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Multigraph V E)

/-- Undirected adjacency with the individual witnessing edge copy retained. -/
def adjacent (s : Finset E) (x y : V) : Prop :=
  ∃ e ∈ s, (G.left e = x ∧ G.right e = y) ∨ (G.right e = x ∧ G.left e = y)

/-- Actual finite-walk reachability, including the walk of length zero. -/
def reaches (s : Finset E) : V → V → Prop := Relation.ReflTransGen (G.adjacent s)

/-- All edges of the subset have both endpoints in the indicated support. -/
def supported (C : Set V) (s : Finset E) : Prop :=
  ∀ e ∈ s, G.left e ∈ C ∧ G.right e ∈ C

/-- A forest has no edge whose endpoints remain connected after its deletion. -/
def is_forest (s : Finset E) : Prop :=
  ∀ e ∈ s, ¬G.reaches (s.erase e) (G.left e) (G.right e)

/-- A tree on exactly the nonempty vertex support C; isolated singleton trees are included. -/
def is_tree (C : Set V) (s : Finset E) : Prop :=
  C.Nonempty ∧ G.supported C s ∧
    (∀ x ∈ C, ∀ y ∈ C, G.reaches s x y) ∧ G.is_forest s

/-- The unique tree on a singleton support has no edges. -/
theorem is_tree_singleton_empty (a : V) : G.is_tree {a} ∅ := by
  refine ⟨⟨a, rfl⟩, ?_, ?_, ?_⟩
  · simp [supported]
  · intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst x; subst y
    exact .refl
  · simp [is_forest]

theorem eq_empty_of_is_tree_singleton {a : V} {s : Finset E}
    (hs : G.is_tree {a} s) : s = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  have h := hs.2.1 e he
  apply G.loopless e
  exact (Set.mem_singleton_iff.mp h.1).trans (Set.mem_singleton_iff.mp h.2).symm

/-- A crossing edge copy, in either orientation. -/
def crosses (C : Set V) (e : E) : Prop :=
  (G.left e ∈ C ∧ G.right e ∉ C) ∨ (G.left e ∉ C ∧ G.right e ∈ C)

omit [DecidableEq E] in
theorem adjacent_symm {s : Finset E} {x y : V} (h : G.adjacent s x y) :
    G.adjacent s y x := by
  rcases h with ⟨e, he, h | h⟩
  · exact ⟨e, he, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨e, he, Or.inl ⟨h.2, h.1⟩⟩

omit [DecidableEq E] in
theorem reaches_symm {s : Finset E} {x y : V} (h : G.reaches s x y) :
    G.reaches s y x := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact (Relation.ReflTransGen.single (G.adjacent_symm h)).trans ih

omit [DecidableEq E] in
theorem reaches_mono {s t : Finset E} (hst : s ⊆ t) {x y : V}
    (h : G.reaches s x y) : G.reaches t x y := by
  apply Relation.ReflTransGen.mono (fun _ _ h => ?_) _ _ h
  rcases h with ⟨e, he, h⟩
  exact ⟨e, hst he, h⟩

theorem is_forest_mono {s t : Finset E} (hst : s ⊆ t) (ht : G.is_forest t) :
    G.is_forest s := by
  intro e he h
  apply ht e (hst he)
  exact G.reaches_mono (by intro f hf; simpa using
    (show f ≠ e ∧ f ∈ t from ⟨(Finset.mem_erase.mp hf).1, hst (Finset.mem_erase.mp hf).2⟩)) h

omit [DecidableEq E] in
theorem reaches_mem_iff {C : Set V} {s : Finset E}
    (hs : ∀ e ∈ s, G.left e ∈ C ↔ G.right e ∈ C) {x y : V}
    (h : G.reaches s x y) : x ∈ C ↔ y ∈ C := by
  induction h with
  | refl => rfl
  | tail _ h ih =>
    rcases h with ⟨e, he, h | h⟩
    · exact ih.trans (by simpa [← h.1, ← h.2] using hs e he)
    · exact ih.trans (by simpa [← h.1, ← h.2] using (hs e he).symm)

/-- The two internal edge subsets contain no crossing copies. -/
theorem supported_union_same_side {C : Set V} {s t : Finset E}
    (hs : G.supported C s) (ht : G.supported Cᶜ t) :
    ∀ e ∈ s ∪ t, G.left e ∈ C ↔ G.right e ∈ C := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact iff_of_true (hs e he).1 (hs e he).2
  · exact iff_of_false (ht e he).1 (ht e he).2

theorem crosses_not_mem {C : Set V} {s t : Finset E}
    (hs : G.supported C s) (ht : G.supported Cᶜ t) {e : E} (he : G.crosses C e) :
    e ∉ s ∪ t := by
  intro h
  have hside := G.supported_union_same_side hs ht e h
  rcases he with h | h
  · exact h.2 (hside.mp h.1)
  · exact h.1 (hside.mpr h.2)

/-- Collapse the opposite component to the endpoint of the joining edge. -/
noncomputable def retract (C : Set V) (a : V) (x : V) : V := if x ∈ C then x else a

theorem reaches_retract {C : Set V} {s t : Finset E} {e f : E}
    (hs : G.supported C s) (ht : G.supported Cᶜ t)
    (hl : G.left e ∈ C) (hr : G.right e ∉ C) {x y : V}
    (h : G.reaches ((insert e (s ∪ t)).erase f) x y) :
    G.reaches (s.erase f) (retract C (G.left e) x) (retract C (G.left e) y) := by
  classical
  apply Relation.ReflTransGen.lift' (retract C (G.left e)) (fun _ _ h => ?_) _ _ h
  rcases h with ⟨a, ha, hxy⟩
  have haf := (Finset.mem_erase.mp ha).1
  rcases Finset.mem_insert.mp (Finset.mem_erase.mp ha).2 with rfl | ha
  · rcases hxy with hxy | hxy
    · rw [← hxy.1, ← hxy.2]
      simp only [Function.onFun, retract, if_pos hl, if_neg hr]
      exact .refl
    · rw [← hxy.1, ← hxy.2]
      simp only [Function.onFun, retract, if_pos hl, if_neg hr]
      exact .refl
  · rcases Finset.mem_union.mp ha with ha | ha
    · have hc := hs a ha
      rcases hxy with hxy | hxy
      · rw [← hxy.1, ← hxy.2]
        simp only [Function.onFun, retract, if_pos hc.1, if_pos hc.2]
        exact Relation.ReflTransGen.single
          ⟨a, Finset.mem_erase.mpr ⟨haf, ha⟩, Or.inl ⟨rfl, rfl⟩⟩
      · rw [← hxy.1, ← hxy.2]
        simp only [Function.onFun, retract, if_pos hc.1, if_pos hc.2]
        exact Relation.ReflTransGen.single
          ⟨a, Finset.mem_erase.mpr ⟨haf, ha⟩, Or.inr ⟨rfl, rfl⟩⟩
    · have hc := ht a ha
      rcases hxy with hxy | hxy
      · rw [← hxy.1, ← hxy.2]
        simp only [Function.onFun, retract, if_neg hc.1, if_neg hc.2]
        exact .refl
      · rw [← hxy.1, ← hxy.2]
        simp only [Function.onFun, retract, if_neg hc.1, if_neg hc.2]
        exact .refl

/-- Joining two component trees with a crossing copy gives an ordinary spanning tree. -/
theorem is_tree_insert_union {C : Set V} {s t : Finset E} {e : E}
    (hs : G.is_tree C s) (ht : G.is_tree Cᶜ t)
    (hl : G.left e ∈ C) (hr : G.right e ∉ C) :
    G.is_tree Set.univ (insert e (s ∪ t)) := by
  classical
  have he := G.crosses_not_mem hs.2.1 ht.2.1 (Or.inl ⟨hl, hr⟩)
  have hcross : G.reaches (insert e (s ∪ t)) (G.left e) (G.right e) :=
    Relation.ReflTransGen.single ⟨e, Finset.mem_insert_self _ _, Or.inl ⟨rfl, rfl⟩⟩
  have hleft (x : V) (hx : x ∈ C) :
      G.reaches (insert e (s ∪ t)) x (G.left e) :=
    G.reaches_mono (by intro a ha; simp [ha]) (hs.2.2.1 x hx _ hl)
  have hright (x : V) (hx : x ∉ C) :
      G.reaches (insert e (s ∪ t)) (G.right e) x :=
    G.reaches_mono (by intro a ha; simp [ha]) (ht.2.2.1 _ hr x hx)
  refine ⟨⟨G.left e, Set.mem_univ _⟩, (by intro a ha; simp), ?_, ?_⟩
  · intro x _ y _
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
    · exact G.reaches_mono (by intro a ha; simp [ha]) (hs.2.2.1 x hx y hy)
    · exact ((hleft x hx).trans hcross).trans (hright y hy)
    · exact G.reaches_symm (((hleft y hy).trans hcross).trans (hright x hx))
    · exact G.reaches_mono (by intro a ha; simp [ha]) (ht.2.2.1 x hx y hy)
  · intro f hf h
    rcases Finset.mem_insert.mp hf with rfl | hf
    · have hm := G.reaches_mem_iff (G.supported_union_same_side hs.2.1 ht.2.1)
        (by simpa [Finset.erase_insert, he] using h)
      exact hr (hm.mp hl)
    · rcases Finset.mem_union.mp hf with hf | hf
      · have h' := G.reaches_retract hs.2.1 ht.2.1 hl hr h
        have hc := hs.2.1 f hf
        apply hs.2.2.2 f hf
        simpa [retract, hc.1, hc.2] using h'
      · -- Reverse the chosen edge orientation and exchange the components.
        let G' : Multigraph V E := ⟨G.right, G.left, fun a => (G.loopless a).symm⟩
        have hadj (u : Finset E) : G'.adjacent u = G.adjacent u := by
          funext x y; apply propext; simp only [adjacent]; aesop
        have hreach (u : Finset E) : G'.reaches u = G.reaches u := by
          simp only [reaches, hadj]
        have hs' : G'.supported Cᶜ t := by intro a ha; exact ⟨(ht.2.1 a ha).2, (ht.2.1 a ha).1⟩
        have ht' : G'.supported (Cᶜ)ᶜ s := by
          intro a ha
          simpa [G'] using And.intro (hs.2.1 a ha).2 (hs.2.1 a ha).1
        have h' := G'.reaches_retract hs' ht' hr (by simpa using hl)
          (by simpa [hreach, Finset.union_comm] using G.reaches_symm h)
        have hc := ht.2.1 f hf
        apply ht.2.2.2 f hf
        have h'' : G.reaches (t.erase f) (G.right f) (G.left f) := by
          simpa [hreach, retract, hc.1, hc.2, G'] using h'
        exact G.reaches_symm h''

/-- Restrict an actual edge subset to the induced graph on C. -/
noncomputable def internalEdges (C : Set V) (s : Finset E) : Finset E :=
  s.filter (fun e => G.left e ∈ C ∧ G.right e ∈ C)

omit [DecidableEq E] in
theorem supported_internalEdges (C : Set V) (s : Finset E) :
    G.supported C (G.internalEdges C s) := by
  intro e he
  exact (Finset.mem_filter.mp he).2

omit [DecidableEq E] in
theorem reaches_internalEdges {C : Set V} {s : Finset E}
    (hs : ∀ e ∈ s, G.left e ∈ C ↔ G.right e ∈ C) {x y : V} (hx : x ∈ C)
    (h : G.reaches s x y) : G.reaches (G.internalEdges C s) x y := by
  have h' : y ∈ C ∧ G.reaches (G.internalEdges C s) x y := by
    induction h with
    | refl => exact ⟨hx, .refl⟩
    | @tail z y _ h ih =>
      rcases h with ⟨e, he, hxy⟩
      have heC : G.left e ∈ C ∧ G.right e ∈ C := by
        rcases hxy with hxy | hxy
        · have hl : G.left e ∈ C := hxy.1 ▸ ih.1
          exact ⟨hl, (hs e he).mp hl⟩
        · have hr : G.right e ∈ C := hxy.1 ▸ ih.1
          exact ⟨(hs e he).mpr hr, hr⟩
      have hy : y ∈ C := by rcases hxy with hxy | hxy; exact hxy.2 ▸ heC.2; exact hxy.2 ▸ heC.1
      exact ⟨hy, ih.2.tail ⟨e, Finset.mem_filter.mpr ⟨he, heC⟩, hxy⟩⟩
  exact h'.2

theorem is_tree_internalEdges {C : Set V} {s : Finset E} (hn : C.Nonempty)
    (hs : ∀ e ∈ s, G.left e ∈ C ↔ G.right e ∈ C)
    (hc : ∀ x ∈ C, ∀ y ∈ C, G.reaches s x y) (hf : G.is_forest s) :
    G.is_tree C (G.internalEdges C s) := by
  refine ⟨hn, G.supported_internalEdges C s, ?_, ?_⟩
  · intro x hx y hy
    exact G.reaches_internalEdges hs hx (hc x hx y hy)
  · exact G.is_forest_mono (Finset.filter_subset _ _) hf

theorem internalEdges_union_compl {C : Set V} {s : Finset E}
    (hs : ∀ e ∈ s, G.left e ∈ C ↔ G.right e ∈ C) :
    G.internalEdges C s ∪ G.internalEdges Cᶜ s = s := by
  ext e
  simp only [Finset.mem_union, internalEdges, Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro he
    by_cases hl : G.left e ∈ C
    · exact Or.inl ⟨he, hl, (hs e he).mp hl⟩
    · exact Or.inr ⟨he, hl, fun hr => hl ((hs e he).mpr hr)⟩

theorem internalEdges_union {C : Set V} {s t : Finset E}
    (hs : G.supported C s) (ht : G.supported Cᶜ t) :
    G.internalEdges C (s ∪ t) = s := by
  ext f
  simp only [internalEdges, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hf | hf, hl, _⟩
    · exact hf
    · exact ((ht f hf).1 hl).elim
  · intro hf
    exact ⟨Or.inl hf, hs f hf⟩

theorem internalEdges_insert_union {C : Set V} {s t : Finset E} {e : E}
    (hs : G.supported C s) (ht : G.supported Cᶜ t) (he : G.crosses C e) :
    G.internalEdges C (insert e (s ∪ t)) = s := by
  ext f
  simp only [internalEdges, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨hf, hl, hr⟩
    rcases hf with rfl | hf | hf
    · rcases he with he | he
      · exact (he.2 hr).elim
      · exact (he.1 hl).elim
    · exact hf
    · exact ((ht f hf).1 hl).elim
  · intro hf
    exact ⟨Or.inr (Or.inl hf), hs f hf⟩

/-- Deleting the marked crossing copy leaves precisely the two indicated components.
The support separation and the two connectivity clauses are literal walk conditions. -/
def cut_components (C : Set V) (s : Finset E) (e : E) : Prop :=
  e ∈ s ∧ G.crosses C e ∧
    (∀ f ∈ s.erase e, G.left f ∈ C ↔ G.right f ∈ C) ∧
    (∀ x ∈ C, ∀ y ∈ C, G.reaches (s.erase e) x y) ∧
    (∀ x ∈ Cᶜ, ∀ y ∈ Cᶜ, G.reaches (s.erase e) x y)

/-- Ordinary spanning trees with a marked cut whose components have supports C and Cᶜ. -/
abbrev CutTree (C : Set V) :=
  {p : Finset E × E // G.is_tree Set.univ p.1 ∧ G.cut_components C p.1 p.2}

/-- Component-tree subsets, together with an individual admissible crossing copy. -/
abbrev Joining (C : Set V) :=
  {p : Finset E × Finset E × E //
    G.is_tree C p.1 ∧ G.is_tree Cᶜ p.2.1 ∧ G.crosses C p.2.2}

theorem is_tree_insert_union_of_crosses {C : Set V} {s t : Finset E} {e : E}
    (hs : G.is_tree C s) (ht : G.is_tree Cᶜ t) (he : G.crosses C e) :
    G.is_tree Set.univ (insert e (s ∪ t)) := by
  rcases he with he | he
  · exact G.is_tree_insert_union hs ht he.1 he.2
  · rw [Finset.union_comm s t]
    exact G.is_tree_insert_union ht (by simpa using hs) he.1 (by simpa using he.2)

theorem cut_components_insert_union {C : Set V} {s t : Finset E} {e : E}
    (hs : G.is_tree C s) (ht : G.is_tree Cᶜ t) (he : G.crosses C e) :
    G.cut_components C (insert e (s ∪ t)) e := by
  have hnot := G.crosses_not_mem hs.2.1 ht.2.1 he
  have herase : (insert e (s ∪ t)).erase e = s ∪ t := by simp [hnot]
  refine ⟨Finset.mem_insert_self _ _, he, ?_, ?_, ?_⟩
  · simpa [herase] using G.supported_union_same_side hs.2.1 ht.2.1
  · intro x hx y hy
    rw [herase]
    exact G.reaches_mono Finset.subset_union_left (hs.2.2.1 x hx y hy)
  · intro x hx y hy
    rw [herase]
    exact G.reaches_mono Finset.subset_union_right (ht.2.2.1 x hx y hy)

/-- Literal insertion of the marked edge copy, with connectivity and acyclicity proved. -/
def join (C : Set V) (p : G.Joining C) : G.CutTree C :=
  ⟨(insert p.val.2.2 (p.val.1 ∪ p.val.2.1), p.val.2.2),
    G.is_tree_insert_union_of_crosses p.property.1 p.property.2.1 p.property.2.2,
    G.cut_components_insert_union p.property.1 p.property.2.1 p.property.2.2⟩

/-- Delete the marked copy and recover the two induced component edge subsets. -/
noncomputable def split (C : Set V) (p : G.CutTree C) : G.Joining C := by
  let s := p.val.1.erase p.val.2
  have hs : G.is_forest s := G.is_forest_mono (Finset.erase_subset _ _) p.property.1.2.2.2
  have hside := p.property.2.2.2.1
  have hcross := p.property.2.2.1
  have hC : C.Nonempty := by
    rcases hcross with h | h
    · exact ⟨G.left p.val.2, h.1⟩
    · exact ⟨G.right p.val.2, h.2⟩
  have hD : Cᶜ.Nonempty := by
    rcases hcross with h | h
    · exact ⟨G.right p.val.2, h.2⟩
    · exact ⟨G.left p.val.2, h.1⟩
  exact ⟨(G.internalEdges C s, G.internalEdges Cᶜ s, p.val.2),
    G.is_tree_internalEdges hC hside p.property.2.2.2.2.1 hs,
    G.is_tree_internalEdges hD (fun e he => not_congr (hside e he))
      p.property.2.2.2.2.2 hs, hcross⟩

theorem split_join (C : Set V) (p : G.Joining C) : G.split C (G.join C p) = p := by
  apply Subtype.ext
  have he := G.crosses_not_mem p.property.1.2.1 p.property.2.1.2.1 p.property.2.2
  change (G.internalEdges C ((insert p.val.2.2 (p.val.1 ∪ p.val.2.1)).erase p.val.2.2),
    G.internalEdges Cᶜ ((insert p.val.2.2 (p.val.1 ∪ p.val.2.1)).erase p.val.2.2), p.val.2.2) = p.val
  have herase : (insert p.val.2.2 (p.val.1 ∪ p.val.2.1)).erase p.val.2.2 =
      p.val.1 ∪ p.val.2.1 := by simp [he]
  have hC := G.internalEdges_union p.property.1.2.1 p.property.2.1.2.1
  have hD : G.internalEdges Cᶜ (p.val.1 ∪ p.val.2.1) = p.val.2.1 := by
    rw [Finset.union_comm]
    exact G.internalEdges_union p.property.2.1.2.1 (by simpa using p.property.1.2.1)
  simp only [herase, hC, hD]

theorem join_split (C : Set V) (p : G.CutTree C) : G.join C (G.split C p) = p := by
  apply Subtype.ext
  change (insert p.val.2 (G.internalEdges C (p.val.1.erase p.val.2) ∪
    G.internalEdges Cᶜ (p.val.1.erase p.val.2)), p.val.2) = p.val
  rw [G.internalEdges_union_compl p.property.2.2.2.1,
    Finset.insert_erase p.property.2.1]

/-- A proved copied-edge joining equivalence, not a supplied tree-bijection hypothesis. -/
noncomputable def joiningEquiv (C : Set V) : G.Joining C ≃ G.CutTree C where
  toFun := G.join C
  invFun := G.split C
  left_inv := G.split_join C
  right_inv := G.join_split C

/-- Forgetting the mark is injective for a prescribed cut support C. -/
theorem cutTree_edges_injective (C : Set V) :
    Function.Injective (fun p : G.CutTree C => p.val.1) := by
  intro p q hpq
  change p.val.1 = q.val.1 at hpq
  have he : p.val.2 = q.val.2 := by
    by_contra hne
    have hmem : q.val.2 ∈ p.val.1.erase p.val.2 :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, (by rw [hpq]; exact q.property.2.1)⟩
    have hside := p.property.2.2.2.1 _ hmem
    rcases q.property.2.2.1 with h | h
    · exact h.2 (hside.mp h.1)
    · exact h.1 (hside.mpr h.2)
  apply Subtype.ext
  exact Prod.ext hpq he

/-- A spanning-tree subset of the induced component graph, including singleton trees. -/
abbrev ComponentTree (C : Set V) := {s : Finset E // G.is_tree C s}

/-- The C endpoint of a crossing edge is in the specified joining set K. -/
def admissible (C K : Set V) (e : E) : Prop :=
  (G.left e ∈ C ∩ K ∧ G.right e ∉ C) ∨ (G.right e ∈ C ∩ K ∧ G.left e ∉ C)

omit [DecidableEq E] in
theorem admissible_iff_of_subset {C K : Set V} (hK : K ⊆ C) (e : E) :
    G.admissible C K e ↔
      (G.left e ∈ K ∧ G.right e ∉ C) ∨ (G.right e ∈ K ∧ G.left e ∉ C) := by
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨h.1.2, h.2⟩
    · exact Or.inr ⟨h.1.2, h.2⟩
  · rintro (h | h)
    · exact Or.inl ⟨⟨hK h.1, h.1⟩, h.2⟩
    · exact Or.inr ⟨⟨hK h.1, h.1⟩, h.2⟩

omit [DecidableEq E] in
theorem admissible_implies_crosses {C K : Set V} {e : E}
    (he : G.admissible C K e) : G.crosses C e := by
  rcases he with he | he
  · exact Or.inl ⟨he.1.1, he.2⟩
  · exact Or.inr ⟨he.2, he.1.1⟩

omit [DecidableEq E] in
theorem crosses_of_admissible {C K : Set V} (hK : K ⊆ C) {e : E}
    (he : G.admissible C K e) : G.crosses C e := by
  rcases (G.admissible_iff_of_subset hK e).mp he with he | he
  · exact Or.inl ⟨hK he.1, he.2⟩
  · exact Or.inr ⟨he.2, hK he.1⟩

abbrev FixedJoining (C K : Set V) (t : G.ComponentTree C) :=
  {p : G.Joining C // p.val.1 = t.val ∧ G.admissible C K p.val.2.2}

/-- Completed ordinary spanning trees with the prescribed inside restriction and a
cut-edge endpoint in K. The mark is unique by cutTree_edges_injective. -/
abbrev FixedCutTree (C K : Set V) (t : G.ComponentTree C) :=
  {p : G.CutTree C // G.internalEdges C p.val.1 = t.val ∧ G.admissible C K p.val.2}

noncomputable def fixedJoiningEquiv (C K : Set V) (t : G.ComponentTree C) (hK : K ⊆ C) :
    (G.ComponentTree Cᶜ × {e : E // G.admissible C K e}) ≃ G.FixedJoining C K t where
  toFun p := ⟨⟨(t.val, p.1.val, p.2.val), t.property, p.1.property,
    G.crosses_of_admissible hK p.2.property⟩, rfl, p.2.property⟩
  invFun p := (⟨p.val.val.2.1, p.val.property.2.1⟩, ⟨p.val.val.2.2, p.property.2⟩)
  left_inv p := by rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext p.property.1.symm rfl

noncomputable def fixedCutEquiv (C K : Set V) (t : G.ComponentTree C) (hK : K ⊆ C) :
    (G.ComponentTree Cᶜ × {e : E // G.admissible C K e}) ≃ G.FixedCutTree C K t :=
  (G.fixedJoiningEquiv C K t hK).trans
    ((G.joiningEquiv C).subtypeEquiv fun p => by
      have hi := G.internalEdges_insert_union p.property.1.2.1 p.property.2.1.2.1
        p.property.2.2
      change (p.val.1 = t.val ∧ G.admissible C K p.val.2.2) ↔
        (G.internalEdges C (insert p.val.2.2 (p.val.1 ∪ p.val.2.1)) = t.val ∧
          G.admissible C K p.val.2.2)
      rw [hi])

section Finite

/-- All admissible copies, explicitly enumerated in the edge carrier. -/
noncomputable def admissibleEdges (C K : Set V) : Finset E :=
  Finset.univ.filter (G.admissible C K)

/-- All individual copies joining v to the opposite side of C. -/
noncomputable def crossingAt (C : Set V) (v : V) : Finset E :=
  Finset.univ.filter fun e =>
    v ∈ C ∧ ((G.left e = v ∧ G.right e ∉ C) ∨ (G.right e = v ∧ G.left e ∉ C))

theorem admissibleEdges_eq_biUnion (C K : Set V) :
    G.admissibleEdges C K = K.toFinset.biUnion (G.crossingAt C) := by
  ext e
  simp only [admissibleEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, Set.mem_toFinset, crossingAt, admissible, Set.mem_inter_iff]
  constructor
  · rintro (h | h)
    · exact ⟨G.left e, h.1.2, h.1.1, Or.inl ⟨rfl, h.2⟩⟩
    · exact ⟨G.right e, h.1.2, h.1.1, Or.inr ⟨rfl, h.2⟩⟩
  · rintro ⟨v, hv, hvC, h | h⟩
    · exact Or.inl ⟨⟨h.1 ▸ hvC, h.1 ▸ hv⟩, h.2⟩
    · exact Or.inr ⟨⟨h.1 ▸ hvC, h.1 ▸ hv⟩, h.2⟩

omit [DecidableEq E] in
@[simp] theorem admissible_empty (K : Set V) (e : E) :
    ¬G.admissible ∅ K e := by simp [admissible]

omit [DecidableEq E] in
@[simp] theorem crossingAt_eq_empty_of_not_mem {C : Set V} {v : V} (hv : v ∉ C) :
    G.crossingAt C v = ∅ := by simp [crossingAt, hv]

omit [DecidableEq E] in
@[simp] theorem crossingAt_empty (v : V) : G.crossingAt ∅ v = ∅ := by
  simp [crossingAt]

/-- The literal edge-copy fiber size is the sum of opposite-side degrees over K. -/
theorem card_admissibleEdges (C K : Set V) (hK : K ⊆ C) :
    (G.admissibleEdges C K).card = ∑ v ∈ K.toFinset, (G.crossingAt C v).card := by
  classical
  rw [G.admissibleEdges_eq_biUnion]
  apply Finset.card_biUnion
  intro v hv w hw hvw
  apply Finset.disjoint_left.mpr
  intro e hev hew
  have hvC := hK (Set.mem_toFinset.mp hv)
  have hwC := hK (Set.mem_toFinset.mp hw)
  have hve := (Finset.mem_filter.mp hev).2.2
  have hwe := (Finset.mem_filter.mp hew).2.2
  rcases hve with hve | hve <;> rcases hwe with hwe | hwe
  · exact hvw (hve.1.symm.trans hwe.1)
  · exact hwe.2 (hve.1 ▸ hvC)
  · exact hve.2 (hwe.1 ▸ hwC)
  · exact hvw (hve.1.symm.trans hwe.1)

/-- Exactly ell ordinary completions for each fixed pair of component trees. -/
theorem card_fixedCutTree (C K : Set V) (t : G.ComponentTree C) (hK : K ⊆ C) :
    Fintype.card (G.FixedCutTree C K t) =
      Fintype.card (G.ComponentTree Cᶜ) * (G.admissibleEdges C K).card := by
  rw [← Fintype.card_congr (G.fixedCutEquiv C K t hK), Fintype.card_prod]
  congr 1
  exact Fintype.subtype_card _ (by intro e; simp)

/-- Reciprocal joining cancellation at fixed C and inside tree, retaining common mass c.
There are no completions when ell=0, so that branch contributes zero. -/
theorem reciprocal_fixedCutTree (C K : Set V) (t : G.ComponentTree C) (hK : K ⊆ C)
    (c : ℝ) :
    (∑ _q : G.FixedCutTree C K t, c / (G.admissibleEdges C K).card) =
      if (G.admissibleEdges C K).Nonempty then c * Fintype.card (G.ComponentTree Cᶜ) else 0 := by
  classical
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, G.card_fixedCutTree C K t hK,
    Nat.cast_mul]
  by_cases h : (G.admissibleEdges C K).Nonempty
  · rw [if_pos h]
    have hc : ((G.admissibleEdges C K).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr h
    field_simp
  · have hc : (G.admissibleEdges C K).card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp h)
    simp [h, hc]

end Finite

end Multigraph

end FiniteAvalanches.Trees
