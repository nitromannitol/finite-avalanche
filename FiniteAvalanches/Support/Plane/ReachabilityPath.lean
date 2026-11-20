import FiniteAvalanches.Support.Plane.ReachabilityTrace

/-!
# Plane paths from copied graph walks

A copied-edge walk gives a continuous path in the corresponding drawing trace,
including when some of the copied edges are loops.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Classical

/-- Reachable vertices are joined by a path inside the selected drawing trace. -/
theorem Drawing.exists_path_of_reaches {V E : Type} [Fintype V] [Fintype E]
    {G : CopiedGraph V E} (D : Drawing G) (A : Finset E) {u v : V}
    (h : G.reaches A u v) :
    ∃ p : Path (D.point u) (D.point v), range p ⊆ D.trace Set.univ A := by
  induction h with
  | refl =>
    refine ⟨Path.refl _, ?_⟩
    rintro z ⟨t, rfl⟩
    exact Or.inl ⟨_, mem_univ _, rfl⟩
  | @tail w v _ hedge ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨e, he, ⟨hle, hre⟩ | ⟨hre, hle⟩⟩ := hedge
    · let q : Path (D.point w) (D.point v) :=
        ⟨⟨D.curve e, D.continuous e⟩, (D.start e).trans (congrArg D.point hle),
          (D.finish e).trans (congrArg D.point hre)⟩
      refine ⟨p.trans q, ?_⟩
      rw [Path.trans_range]
      rintro z (hz | ⟨t, rfl⟩)
      · exact hp hz
      · exact Or.inr ⟨e, he, t, rfl⟩
    · let q : Path (D.point v) (D.point w) :=
        ⟨⟨D.curve e, D.continuous e⟩, (D.start e).trans (congrArg D.point hle),
          (D.finish e).trans (congrArg D.point hre)⟩
      refine ⟨p.trans q.symm, ?_⟩
      rw [Path.trans_range, Path.symm_range]
      rintro z (hz | ⟨t, rfl⟩)
      · exact hp hz
      · exact Or.inr ⟨e, he, t, rfl⟩

end FiniteAvalanches.Electrical.StatementGeometry
