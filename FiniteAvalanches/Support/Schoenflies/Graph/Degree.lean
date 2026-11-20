/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Graph/Degree.lean.
Modified for this project: comments removed and replaced by a one-line module docstring.
-/
import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 































































open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {e f : β} {x y : α}

 

 


class Finite (G : Graph α β) : Prop where
   
  finite_vertexSet : V(G).Finite
   
  finite_edgeSet : E(G).Finite

theorem finite_vertexSet (G : Graph α β) [G.Finite] : V(G).Finite := Finite.finite_vertexSet

theorem finite_edgeSet (G : Graph α β) [G.Finite] : E(G).Finite := Finite.finite_edgeSet

instance [G.Finite] : _root_.Finite V(G) := Set.finite_coe_iff.2 (finite_vertexSet G)

instance [G.Finite] : _root_.Finite E(G) := Set.finite_coe_iff.2 (finite_edgeSet G)

 

theorem Finite.of_le (h : H ≤ G) [G.Finite] : H.Finite :=
  ⟨(_root_.Graph.finite_vertexSet G).subset h.vertexSet_mono,
   (_root_.Graph.finite_edgeSet G).subset h.edgeSet_mono⟩

 
noncomputable def vertexFinset (G : Graph α β) [G.Finite] : Finset α :=
  (finite_vertexSet G).toFinset

 
noncomputable def edgeFinset (G : Graph α β) [G.Finite] : Finset β :=
  (finite_edgeSet G).toFinset

@[simp]
theorem mem_vertexFinset [G.Finite] : x ∈ G.vertexFinset ↔ x ∈ V(G) :=
  Set.Finite.mem_toFinset _

@[simp]
theorem mem_edgeFinset [G.Finite] : e ∈ G.edgeFinset ↔ e ∈ E(G) :=
  Set.Finite.mem_toFinset _

@[simp, norm_cast]
theorem coe_vertexFinset [G.Finite] : (G.vertexFinset : Set α) = V(G) :=
  Set.Finite.coe_toFinset _

@[simp, norm_cast]
theorem coe_edgeFinset [G.Finite] : (G.edgeFinset : Set β) = E(G) :=
  Set.Finite.coe_toFinset _

@[simp]
theorem card_vertexFinset [G.Finite] : G.vertexFinset.card = V(G).ncard := by
  rw [← Set.ncard_coe_finset, coe_vertexFinset]

@[simp]
theorem card_edgeFinset [G.Finite] : G.edgeFinset.card = E(G).ncard := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

 

theorem incidenceSet_eq_setOf (G : Graph α β) (x : α) : G.incidenceSet x = {e | G.Inc e x} :=
  rfl

theorem loopSet_eq_setOf (G : Graph α β) (x : α) : G.loopSet x = {e | G.IsLoopAt e x} :=
  rfl

theorem finite_incidenceSet [G.Finite] (x : α) : (G.incidenceSet x).Finite :=
  (finite_edgeSet G).subset (G.incidenceSet_subset_edgeSet x)

theorem finite_loopSet [G.Finite] (x : α) : (G.loopSet x).Finite :=
  (finite_incidenceSet x).subset (G.loopSet_subset_incidenceSet x)

 

 

noncomputable def degree (G : Graph α β) (x : α) : ℕ :=
  (G.incidenceSet x).ncard + (G.loopSet x).ncard

theorem degree_def (G : Graph α β) (x : α) :
    G.degree x = (G.incidenceSet x).ncard + (G.loopSet x).ncard := rfl

 
@[simp]
theorem degree_eq_zero_of_notMem (h : x ∉ V(G)) : G.degree x = 0 := by
  have h1 : G.incidenceSet x = ∅ := by
    ext e
    simp only [mem_incidenceSet, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h hx.vertex_mem
  have h2 : G.loopSet x = ∅ :=
    Set.eq_empty_of_subset_empty (h1 ▸ G.loopSet_subset_incidenceSet x)
  rw [degree_def, h1, h2]
  simp

 

theorem ncard_loopSet_le_ncard_incidenceSet [G.Finite] (x : α) :
    (G.loopSet x).ncard ≤ (G.incidenceSet x).ncard :=
  Set.ncard_le_ncard (G.loopSet_subset_incidenceSet x) (finite_incidenceSet x)

theorem ncard_incidenceSet_le_degree (x : α) : (G.incidenceSet x).ncard ≤ G.degree x :=
  Nat.le_add_right _ _

 
theorem degree_eq_ncard_incidenceSet (h : ∀ e, ¬ G.IsLoopAt e x) :
    G.degree x = (G.incidenceSet x).ncard := by
  have : G.loopSet x = ∅ := by
    ext e
    simpa using h e
  rw [degree_def, this]
  simp

 
theorem IsLoopAt.two_le_degree [G.Finite] (h : G.IsLoopAt e x) : 2 ≤ G.degree x := by
  have h1 : 1 ≤ (G.loopSet x).ncard :=
    (Set.ncard_pos (finite_loopSet x)).2 ⟨e, h⟩
  have h2 : 1 ≤ (G.incidenceSet x).ncard :=
    (Set.ncard_pos (finite_incidenceSet x)).2 ⟨e, h.inc⟩
  rw [degree_def]
  omega

theorem degree_pos_of_inc [G.Finite] (h : G.Inc e x) : 0 < G.degree x := by
  have : 0 < (G.incidenceSet x).ncard := (Set.ncard_pos (finite_incidenceSet x)).2 ⟨e, h⟩
  rw [degree_def]
  omega

theorem degree_eq_zero_iff [G.Finite] : G.degree x = 0 ↔ ∀ e, ¬ G.Inc e x := by
  refine ⟨fun h e he => ?_, fun h => ?_⟩
  · exact absurd h (degree_pos_of_inc he).ne'
  · have h1 : G.incidenceSet x = ∅ := by
      ext e
      simpa using h e
    have h2 : G.loopSet x = ∅ :=
      Set.eq_empty_of_subset_empty (h1 ▸ G.loopSet_subset_incidenceSet x)
    rw [degree_def, h1, h2]
    simp

 






 

theorem ncard_inc_add_ncard_isLoopAt (G : Graph α β) (he : e ∈ E(G)) :
    {x | G.Inc e x}.ncard + {x | G.IsLoopAt e x}.ncard = 2 := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  by_cases huv' : u = v
  · 
    subst huv'
    have hl : G.IsLoopAt e u := huv
    have h1 : {x | G.Inc e x} = {u} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => (hl.eq_of_inc h).symm, fun h => h ▸ hl.inc⟩
    have h2 : {x | G.IsLoopAt e x} = {u} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h => (hl.eq_of_inc h.inc).symm, fun h => h ▸ hl⟩
    rw [h1, h2]
    simp
  · 
    have h1 : {x | G.Inc e x} = {u, v} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨fun h => h.eq_or_eq_of_isLink huv,
        fun h => h.elim (fun hz => hz ▸ huv.inc_left) (fun hz => hz ▸ huv.inc_right)⟩
    have h2 : {x | G.IsLoopAt e x} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hz
      exact huv' ((hz.eq_of_inc huv.inc_left).symm.trans (hz.eq_of_inc huv.inc_right))
    rw [h1, h2, Set.ncard_pair huv']
    simp

 

 


private theorem ncard_setOf_eq_sum_ite {γ : Type*} (s : Finset γ) (p : γ → Prop)
    [DecidablePred p] (hsub : ∀ z, p z → z ∈ s) :
    {z | p z}.ncard = ∑ z ∈ s, if p z then 1 else 0 := by
  rw [← Finset.card_filter p s, ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp only [Finset.coe_filter, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨hsub z h, h⟩, fun h => h.2⟩

 






theorem sum_degree_eq_two_mul_ncard_edgeSet (G : Graph α β) [G.Finite] :
    ∑ x ∈ G.vertexFinset, G.degree x = 2 * E(G).ncard := by
  classical
  
  set ends : β → α → ℕ :=
    fun e x => (if G.Inc e x then 1 else 0) + (if G.IsLoopAt e x then 1 else 0) with hends
  
  have hdeg : ∀ x, G.degree x = ∑ e ∈ G.edgeFinset, ends e x := by
    intro x
    have h1 : (G.incidenceSet x).ncard = ∑ e ∈ G.edgeFinset, if G.Inc e x then 1 else 0 := by
      rw [incidenceSet_eq_setOf]
      exact ncard_setOf_eq_sum_ite _ _ fun z hz => mem_edgeFinset.2 hz.edge_mem
    have h2 : (G.loopSet x).ncard = ∑ e ∈ G.edgeFinset, if G.IsLoopAt e x then 1 else 0 := by
      rw [loopSet_eq_setOf]
      exact ncard_setOf_eq_sum_ite _ _ fun z hz => mem_edgeFinset.2 hz.edge_mem
    rw [degree_def, h1, h2, hends, ← Finset.sum_add_distrib]
  
  have hedge : ∀ e ∈ G.edgeFinset, ∑ x ∈ G.vertexFinset, ends e x = 2 := by
    intro e he
    rw [mem_edgeFinset] at he
    have h1 : {x | G.Inc e x}.ncard = ∑ x ∈ G.vertexFinset, if G.Inc e x then 1 else 0 :=
      ncard_setOf_eq_sum_ite _ _ fun z hz => mem_vertexFinset.2 hz.vertex_mem
    have h2 : {x | G.IsLoopAt e x}.ncard
        = ∑ x ∈ G.vertexFinset, if G.IsLoopAt e x then 1 else 0 :=
      ncard_setOf_eq_sum_ite _ _ fun z hz => mem_vertexFinset.2 hz.vertex_mem
    rw [hends, Finset.sum_add_distrib, ← h1, ← h2]
    exact G.ncard_inc_add_ncard_isLoopAt he
  calc ∑ x ∈ G.vertexFinset, G.degree x
      = ∑ x ∈ G.vertexFinset, ∑ e ∈ G.edgeFinset, ends e x := by
        exact Finset.sum_congr rfl fun x _ => hdeg x
    _ = ∑ e ∈ G.edgeFinset, ∑ x ∈ G.vertexFinset, ends e x := Finset.sum_comm
    _ = ∑ _e ∈ G.edgeFinset, 2 := Finset.sum_congr rfl hedge
    _ = 2 * E(G).ncard := by
        rw [Finset.sum_const, card_edgeFinset, smul_eq_mul, Nat.mul_comm]

 
theorem sum_degree_eq_two_mul_card_edgeFinset (G : Graph α β) [G.Finite] :
    ∑ x ∈ G.vertexFinset, G.degree x = 2 * G.edgeFinset.card := by
  rw [card_edgeFinset]
  exact G.sum_degree_eq_two_mul_ncard_edgeSet

 
theorem even_sum_degree (G : Graph α β) [G.Finite] :
    Even (∑ x ∈ G.vertexFinset, G.degree x) :=
  ⟨E(G).ncard, by rw [G.sum_degree_eq_two_mul_ncard_edgeSet, two_mul]⟩

 

 
def IsLeaf (G : Graph α β) (x : α) : Prop := x ∈ V(G) ∧ G.degree x = 1

theorem IsLeaf.mem_vertexSet (h : G.IsLeaf x) : x ∈ V(G) := h.1

theorem IsLeaf.degree_eq_one (h : G.IsLeaf x) : G.degree x = 1 := h.2

theorem isLeaf_iff : G.IsLeaf x ↔ x ∈ V(G) ∧ G.degree x = 1 := Iff.rfl

 
theorem IsLeaf.not_isLoopAt [G.Finite] (h : G.IsLeaf x) (e : β) : ¬ G.IsLoopAt e x := by
  intro hl
  have h2 := hl.two_le_degree
  have hd := h.2
  omega

 
theorem IsLeaf.ncard_incidenceSet [G.Finite] (h : G.IsLeaf x) :
    (G.incidenceSet x).ncard = 1 := by
  have hle := ncard_loopSet_le_ncard_incidenceSet (G := G) x
  have hd : (G.incidenceSet x).ncard + (G.loopSet x).ncard = 1 := h.2
  omega

theorem IsLeaf.loopSet_eq_empty [G.Finite] (h : G.IsLeaf x) : G.loopSet x = ∅ := by
  have hle := ncard_loopSet_le_ncard_incidenceSet (G := G) x
  have hd : (G.incidenceSet x).ncard + (G.loopSet x).ncard = 1 := h.2
  have : (G.loopSet x).ncard = 0 := by omega
  exact (Set.ncard_eq_zero (finite_loopSet x)).1 this

 
theorem IsLeaf.existsUnique_inc [G.Finite] (h : G.IsLeaf x) : ∃! e, G.Inc e x := by
  obtain ⟨e, he⟩ := Set.ncard_eq_one.1 h.ncard_incidenceSet
  refine ⟨e, ?_, fun f hf => ?_⟩
  · have : e ∈ G.incidenceSet x := by rw [he]; rfl
    exact this
  · have : f ∈ G.incidenceSet x := hf
    rw [he] at this
    exact this

 
theorem IsLeaf.exists_isLink [G.Finite] (h : G.IsLeaf x) :
    ∃ e y, y ≠ x ∧ G.IsLink e x y := by
  obtain ⟨e, he, -⟩ := h.existsUnique_inc
  obtain ⟨y, hy⟩ := he
  refine ⟨e, y, ?_, hy⟩
  rintro rfl
  exact h.not_isLoopAt e hy

 
theorem IsLeaf.isNonloopAt [G.Finite] (h : G.IsLeaf x) (he : G.Inc e x) :
    G.IsNonloopAt e x :=
  he.isLoopAt_or_isNonloopAt.resolve_left (h.not_isLoopAt e)

 

theorem isLeaf_of_isNonloopAt (hx : x ∈ V(G))
    (h : ∀ f, G.Inc f x ↔ f = e) (hne : G.IsNonloopAt e x) : G.IsLeaf x := by
  refine ⟨hx, ?_⟩
  have h1 : G.incidenceSet x = {e} := by
    ext f
    simpa using h f
  have h2 : G.loopSet x = ∅ := by
    ext f
    simp only [mem_loopSet, Set.mem_empty_iff_false, iff_false]
    intro hf
    exact hne.not_isLoopAt x (((h f).1 hf.inc) ▸ hf)
  rw [degree_def, h1, h2]
  simp

end Graph
