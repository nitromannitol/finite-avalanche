import FiniteAvalanches.Electrical.Geometry.CellCases
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open scoped Classical
noncomputable section

theorem walk_reaches_within {X : Type} (G : SimpleGraph X) (S : Set X) (C : Finset X)
    {x y : S} (w : (G.induce S).Walk x y)
    (hC : ∀ v ∈ w.support, v.val ∈ C) :
    Relation.ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ G.Adj a b) x.val y.val := by
  induction w with
  | nil => exact .refl
  | @cons x z y h w ih =>
    have hC' : ∀ v ∈ w.support, v.val ∈ C := by
      intro v hv
      exact hC v (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hv)
    apply Relation.ReflTransGen.trans _ (ih hC')
    exact .single ⟨hC x (by simp), hC z (by simp), h⟩

theorem finite_connected_span {X : Type} (G : SimpleGraph X) (S : Set X)
    (hc : (G.induce S).Connected) (T : Finset X) (hTS : (↑T : Set X) ⊆ S)
    (r : X) (hr : r ∈ S) :
    ∃ C : Finset X, T ⊆ C ∧ (↑C : Set X) ⊆ S ∧ r ∈ C ∧
      ∀ x ∈ C, Relation.ReflTransGen
        (fun a b => a ∈ C ∧ b ∈ C ∧ G.Adj a b) r x := by
  let w (t : T) : (G.induce S).Walk ⟨r, hr⟩ ⟨t.val, hTS t.property⟩ :=
    Classical.choice (hc ⟨r, hr⟩ ⟨t.val, hTS t.property⟩)
  let sites (t : T) : Finset X := (w t).support.toFinset.image Subtype.val
  let C : Finset X := {r} ∪ T.attach.biUnion sites
  have hrC : r ∈ C := Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have sites_subset (t : T) : sites t ⊆ C := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t, Finset.mem_attach _ _, hx⟩)
  have hs (t : T) (v : S) (hv : v ∈ (w t).support) : v.val ∈ C :=
    sites_subset t (Finset.mem_image.mpr ⟨v, List.mem_toFinset.mpr hv, rfl⟩)
  refine ⟨C, ?_, ?_, hrC, ?_⟩
  · intro t ht
    exact hs ⟨t, ht⟩ _ (w ⟨t, ht⟩).end_mem_support
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_singleton.mp hx ▸ hr
    · obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ht
      exact hv ▸ v.property
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_singleton.mp hx ▸ Relation.ReflTransGen.refl
    · obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
      have hv' : v ∈ (w t).support := List.mem_toFinset.mp hv
      exact walk_reaches_within G S C ((w t).takeUntil v hv')
        (fun u hu => hs t u ((w t).support_takeUntil_subset_support hv' hu))

end
end FiniteAvalanches.Electrical.LatticeDrawing
