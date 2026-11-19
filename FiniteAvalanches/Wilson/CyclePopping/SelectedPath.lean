import FiniteAvalanches.Wilson.CyclePopping.ProtectedPaths
import FiniteAvalanches.Wilson.CyclePopping.Erasure

/-! A rootward selected path survives all later legal cycle pops. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [Quiver V] [DecidableEq V]

omit [DecidableEq V] in
/-- Every vertex of a path following a function reaches the endpoint by iteration. -/
theorem follows_vertex_reaches_end (f : V → V) {a b : V} (p : Path a b)
    (hp : follows f p) {v : V} (hv : v ∈ p.vertices) : ∃ n, f^[n] v = b := by
  obtain ⟨n, hn, he⟩ := follows_vertex_iterate f p hp hv
  refine ⟨p.length - n, ?_⟩
  rw [← he, ← Function.iterate_add_apply, Nat.sub_add_cancel hn]
  exact follows_iterate_end f p hp

/-- The vertices of a root-ending selected path remain rootward under cycle pops. -/
theorem selected_path_cursor_preserved (R : Set V) (σ : ArrowStacks (V := V))
    {k l : Cursor V} {a b : V} (p : Path a b) (hp : selected σ k p) (hb : b ∈ R)
    (hrun : Relation.ReflTransGen (pop_step R (fun _ s => s.1) σ) k l) :
    ∀ v ∈ p.vertices, l v = k v := by
  let f : V → V := next (fun _ s => s.1) σ k
  let B : Set V := R ∪ {v | v ∈ p.vertices}
  have hf : follows f p := selected_follows σ k p hp
  have hclosed : ∀ v ∈ B, v ∉ R → f v ∈ B := by
    intro v hv hroot
    rcases hv with hv | hv
    · exact (hroot hv).elim
    · change v ∈ p.vertices at hv
      have hdep : v ∈ departures p := by
        have hh : v ∈ departures p ++ [b] := by
          simpa only [departures, Path.dropLast_append_end_eq] using hv
        rcases List.mem_append.mp hh with hh | hh
        · exact hh
        · have he := List.mem_singleton.mp hh
          exact (hroot (he ▸ hb)).elim
      exact Or.inr (follows_successor_mem f p hf hdep)
  have hreach : ∀ v ∈ B, ∃ n, f^[n] v ∈ R := by
    intro v hv
    rcases hv with hv | hv
    · exact ⟨0, hv⟩
    · obtain ⟨n, hn⟩ := follows_vertex_reaches_end f p hf hv
      exact ⟨n, hn.symm ▸ hb⟩
  intro v hv
  exact pop_run_preserves_rootward_set R B _ σ hclosed hreach hrun v (Or.inr hv)

/-- A root-ending selected path retains every original arrow during later pops. -/
theorem selected_path_preserved (R : Set V) (σ : ArrowStacks (V := V))
    {k l : Cursor V} {a b : V} (p : Path a b) (hp : selected σ k p) (hb : b ∈ R)
    (hrun : Relation.ReflTransGen (pop_step R (fun _ s => s.1) σ) k l) :
    selected σ l p := by
  apply selected_congr σ p hp
  intro v hv
  symm
  apply selected_path_cursor_preserved R σ p hp hb hrun v
  exact List.mem_of_mem_dropLast hv

end
end FiniteAvalanches.Wilson.CyclePopping
