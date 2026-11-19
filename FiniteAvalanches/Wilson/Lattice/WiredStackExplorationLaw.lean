import FiniteAvalanches.Wilson.Lattice.WiredCyclePoppingLaw
import FiniteAvalanches.Wilson.CyclePopping.StackExploration

/-! The finite wired stack exploration has the uniform rooted-forest law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Exploring every vertex in any order produces the uniform wired rooted forest. -/
theorem directionStackLaw_exploration_eq (R : RootPair) (N : ℕ)
    (k : Cursor (FiniteWired.Vertex N)) (L : List (FiniteWired.Vertex N))
    (hL : ∀ v, v ∈ L) (S : Set (FiniteForest R N)) :
    directionStackLaw (FiniteWired.Vertex N)
      {σ | ∃ (t : Cursor (FiniteWired.Vertex N))
          (ht : terminal (wiredRoots R N).val (wiredHead N) (fun v i => σ (v, i)) t),
        Relation.ReflTransGen (pop_step (wiredRoots R N).val (wiredHead N)
            (fun v i => σ (v, i))) k t ∧
        stackExplore (wiredHead N) (fun v i => σ (v, i)) (wiredRoots R N).val k L =
          some (Set.univ, t) ∧
        wiredArrowForest R N ⟨fun v => σ (v, t v), ht⟩ ∈ S} =
      finiteUniformLaw R N S := by
  have he : {σ : FiniteWired.Vertex N × ℕ → FiniteWired.Direction | ∃ (t : Cursor (FiniteWired.Vertex N))
          (ht : terminal (wiredRoots R N).val (wiredHead N) (fun v i => σ (v, i)) t),
        Relation.ReflTransGen (pop_step (wiredRoots R N).val (wiredHead N)
            (fun v i => σ (v, i))) k t ∧
        stackExplore (wiredHead N) (fun v i => σ (v, i)) (wiredRoots R N).val k L =
          some (Set.univ, t) ∧
        wiredArrowForest R N ⟨fun v => σ (v, t v), ht⟩ ∈ S} =
      {σ : FiniteWired.Vertex N × ℕ → FiniteWired.Direction | ∃ a : GoodArrows (wiredRoots R N).val (wiredHead N),
        wiredArrowForest R N a ∈ S ∧
        σ ∈ terminalOutputEvent (wiredRoots R N).val (wiredHead N) k (fun v i σ => σ (v, i)) a} := by
    ext σ
    constructor
    · rintro ⟨t, ht, hrun, _, hS⟩
      exact ⟨⟨fun v => σ (v, t v), ht⟩, hS, t, hrun, fun _ => rfl⟩
    · rintro ⟨a, hS, t, hrun, htop⟩
      have ht : terminal (wiredRoots R N).val (wiredHead N) (fun v i => σ (v, i)) t :=
        terminal_of_top_eq _ _ _ t a.val a.property htop
      have ha : (⟨fun v => σ (v, t v), ht⟩ : GoodArrows (wiredRoots R N).val (wiredHead N)) = a := by
        apply Subtype.ext
        funext v
        exact htop v
      refine ⟨t, ht, hrun, ?_, ?_⟩
      · exact stackExplore_all_of_terminal _ _ _ k t hrun ht L hL
      · rwa [ha]
  rw [he]
  exact directionStackLaw_forestEvent_eq R N k S

end
end FiniteAvalanches.Wilson.Lattice
