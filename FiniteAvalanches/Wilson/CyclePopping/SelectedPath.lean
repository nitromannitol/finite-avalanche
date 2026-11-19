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

omit [DecidableEq V] in
/-- A path following a function stays in the union of its vertices and the roots
until it reaches a root. -/
theorem follows_rootward_set (R : Set V) (f : V → V) {a b : V} (p : Path a b)
    (hp : follows f p) (hb : b ∈ R) :
    (∀ v ∈ R ∪ {v | v ∈ p.vertices}, v ∉ R → f v ∈ R ∪ {v | v ∈ p.vertices}) ∧
    (∀ v ∈ R ∪ {v | v ∈ p.vertices}, ∃ n, f^[n] v ∈ R) := by
  constructor
  · intro v hv hroot
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
      exact Or.inr (follows_successor_mem f p hp hdep)
  · intro v hv
    rcases hv with hv | hv
    · exact ⟨0, hv⟩
    · obtain ⟨n, hn⟩ := follows_vertex_reaches_end f p hp hv
      exact ⟨n, hn.symm ▸ hb⟩

/-- The vertices of a root-ending selected path remain rootward under cycle pops. -/
theorem selected_path_cursor_preserved (R : Set V) (σ : ArrowStacks (V := V))
    {k l : Cursor V} {a b : V} (p : Path a b) (hp : selected σ k p) (hb : b ∈ R)
    (hrun : Relation.ReflTransGen (pop_step R (fun _ s => s.1) σ) k l) :
    ∀ v ∈ p.vertices, l v = k v := by
  have h := follows_rootward_set R _ p (selected_follows σ k p hp) hb
  intro v hv
  exact pop_run_preserves_rootward_set R (R ∪ {v | v ∈ p.vertices}) _ σ
    h.1 h.2 hrun v (Or.inr hv)

/-- A selected root-ending path can be added to the roots for the rest of a legal run. -/
theorem selected_path_pop_run_with_roots (R : Set V) (σ : ArrowStacks (V := V))
    {k l : Cursor V} {a b : V} (p : Path a b) (hp : selected σ k p) (hb : b ∈ R)
    (hrun : Relation.ReflTransGen (pop_step R (fun _ s => s.1) σ) k l) :
    Relation.ReflTransGen (pop_step (R ∪ {v | v ∈ p.vertices}) (fun _ s => s.1) σ) k l := by
  have h := follows_rootward_set R _ p (selected_follows σ k p hp) hb
  exact pop_run_with_rootward_set R (R ∪ {v | v ∈ p.vertices}) _ σ h.1 h.2 hrun

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
