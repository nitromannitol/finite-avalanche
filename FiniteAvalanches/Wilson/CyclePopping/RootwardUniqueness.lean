import FiniteAvalanches.Wilson.CyclePopping.RootwardForest

/-! A rooted copied forest determines the outgoing copy at every nonroot. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E]

/-- Two rootward arrow assignments selecting the same copied edges select the
same copy at every nonroot vertex. -/
theorem rootwardCopies_eq_imp_edge_eq (G : Multigraph V E) (R : Set V)
    (f g : V → V) (edgeF edgeG : V → E)
    (hf : ∀ v, ∃ n, f^[n] v ∈ R) (hg : ∀ v, ∃ n, g^[n] v ∈ R)
    (hendF : ∀ v ∉ R, (G.left (edgeF v) = v ∧ G.right (edgeF v) = f v) ∨
      (G.right (edgeF v) = v ∧ G.left (edgeF v) = f v))
    (hendG : ∀ v ∉ R, (G.left (edgeG v) = v ∧ G.right (edgeG v) = g v) ∨
      (G.right (edgeG v) = v ∧ G.left (edgeG v) = g v))
    (heq : rootwardCopies R edgeF = rootwardCopies R edgeG)
    {u : V} (hu : u ∉ R) : edgeF u = edgeG u := by
  by_contra hne
  let D := rootDescendants R f hf u
  have huD : u ∈ D := mem_rootDescendants_self R f hf u
  have hfuD : f u ∉ D := successor_not_mem_rootDescendants R f hf hu
  have hroot : ∀ r ∈ R, r ∉ D := fun _ hr => root_not_mem_rootDescendants R f hf hu hr
  have hcut : ∀ e ∈ (rootwardCopies R edgeF).erase (edgeF u),
      G.left e ∈ D ↔ G.right e ∈ D :=
    rootwardCopies_descendant_cut G R f edgeF hf hendF u
  have hclosed : ∀ v ∈ D, v ∉ R → g v ∈ D := by
    intro v hvD hvR
    have hvE : edgeG v ∈ rootwardCopies R edgeF := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvR⟩, rfl⟩
    by_cases hvEq : edgeG v = edgeF u
    · have hinc : v = u ∨ v = f u := by
        rcases hendG v hvR with ⟨hl, _⟩ | ⟨hr, _⟩
        · rw [hvEq] at hl
          rcases hendF u hu with ⟨hlF, _⟩ | ⟨_, hlF⟩
          · exact Or.inl (hl.symm.trans hlF)
          · exact Or.inr (hl.symm.trans hlF)
        · rw [hvEq] at hr
          rcases hendF u hu with ⟨_, hrF⟩ | ⟨hrF, _⟩
          · exact Or.inr (hr.symm.trans hrF)
          · exact Or.inl (hr.symm.trans hrF)
      rcases hinc with he | he
      · subst v
        exact (hne hvEq.symm).elim
      · exact (hfuD (he ▸ hvD)).elim
    · have hc := hcut (edgeG v) (Finset.mem_erase.mpr ⟨hvEq, hvE⟩)
      rcases hendG v hvR with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hl, hr] at hc
        exact hc.mp hvD
      · rw [hl, hr] at hc
        exact hc.mpr hvD
  have hiter : ∀ n, g^[n] u ∈ D := by
    intro n
    induction n with
    | zero => exact huD
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hclosed _ ih (fun hr => hroot _ hr ih)
  obtain ⟨n, hn⟩ := hg u
  exact hroot _ hn (hiter n)

end
end FiniteAvalanches.Wilson.CyclePopping
