import FiniteAvalanches.Wilson.CyclePopping.WordErasureNaturality
import FiniteAvalanches.Wilson.CyclePopping.RootOrbits

/-! Root avoidance and rootward orbits of erased paths. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Quiver FiniteAvalanches.Wilson
open scoped Classical

noncomputable section

variable {V : Type*} [Quiver V] [DecidableEq V]

/-- Every departure retained by loop erasure was a departure in the original path. -/
theorem departures_loopErase_subset {a b : V} (p : Path a b) :
    ∀ v ∈ departures (loopErase p), v ∈ departures p := by
  intro v hv
  have hvertex := (loopErase_vertices_sublist p).subset (List.mem_of_mem_dropLast hv)
  have hm : v ∈ departures p ++ [b] := by
    simpa only [departures, Path.dropLast_append_end_eq] using hvertex
  rcases List.mem_append.mp hm with hm | hm
  · exact hm
  · have he : v = b := List.mem_singleton.mp hm
    subst v
    have hn := (Path.dropLast_append_end_eq (loopErase p)) ▸ loopErase_vertices_nodup p
    exact False.elim ((List.nodup_append.mp hn).2.2 b hv b (List.mem_singleton_self b) rfl)

omit [DecidableEq V] in
/-- Along a path that follows an arrow map without departing from a root,
every vertex has the same first root as the endpoint. -/
theorem firstRoot_eq_of_follows_avoids (R : Set V) (f : V → V)
    (h : ∀ v, ∃ n, f^[n] v ∈ R) {a b : V} (p : Path a b)
    (hp : follows f p) (havoid : ∀ v ∈ departures p, v ∉ R) :
    ∀ v ∈ p.vertices, firstRoot R f h v = firstRoot R f h b := by
  induction p with
  | nil =>
    intro v hv
    have he : v = _ := List.mem_singleton.mp hv
    subst v
    rfl
  | @cons b c p e ih =>
    have hpast : ∀ v ∈ departures p, v ∉ R := by
      intro v hv
      apply havoid v
      rw [departures_cons]
      exact List.mem_append_left _ hv
    have hb : b ∉ R := by
      apply havoid b
      rw [departures_cons]
      exact List.mem_append_right _ (List.mem_singleton_self b)
    have hbc : firstRoot R f h b = firstRoot R f h c := by
      rw [firstRoot_succ R f h hb, hp.2]
    intro v hv
    rcases (Path.mem_vertices_cons p e).mp hv with hv | rfl
    · exact (ih hp.1 hpast v hv).trans hbc
    · rfl

end
end FiniteAvalanches.Wilson.CyclePopping
