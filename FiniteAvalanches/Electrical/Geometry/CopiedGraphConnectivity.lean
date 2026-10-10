import FiniteAvalanches.Electrical.Trees.GroveNoncrossing

/-! Connectivity and one-copy deletion for graphs that may contain loops.
All vertices and original copied edge IDs remain literal. -/
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open FiniteAvalanches.Electrical
open scoped Classical

variable {V E E₀ : Type} (J : CopiedGraph V E)

/-- A copied walk gives a supporting-graph walk; loop steps contribute no motion. -/
theorem supportGraph_reachable_of_reaches {F : Finset E} {x y : V}
    (h : J.reaches F x y) : (supportGraph J.left J.right).Reachable x y := by
  induction h with
  | refl => exact .rfl
  | @tail u v _ hadj ih =>
    by_cases huv : u = v
    · simpa only [huv] using ih
    · obtain ⟨e, _, hends⟩ := hadj
      exact ih.trans (SimpleGraph.Adj.reachable ⟨huv, e, hends⟩)

/-- Connectivity by original copied walks implies supporting-graph connectivity. -/
theorem supportGraph_preconnected_of_reaches [Fintype E]
    (hconn : ∀ x y : V, J.reaches Finset.univ x y) :
    (supportGraph J.left J.right).Preconnected := by
  intro x y
  exact J.supportGraph_reachable_of_reaches (hconn x y)

/-- Every supporting-graph walk lifts to a walk using actual original copied IDs. -/
theorem reaches_univ_of_supportGraph_reachable [Fintype E] {x y : V}
    (h : (supportGraph J.left J.right).Reachable x y) :
    J.reaches Finset.univ x y := by
  have h' := ((supportGraph J.left J.right).reachable_iff_reflTransGen x y).mp h
  clear h
  induction h' with
  | refl => exact .refl
  | @tail u v _ hadj ih =>
    obtain ⟨_, e, hends⟩ := hadj
    exact ih.tail ⟨e, Finset.mem_univ e, hends⟩

/-- Replace only the marked original occurrence by a path avoiding that occurrence. -/
theorem reaches_erase_of_alternative {F : Finset E} (marked : E)
    (halt : J.reaches (F.erase marked) (J.left marked) (J.right marked))
    {x y : V} (h : J.reaches F x y) : J.reaches (F.erase marked) x y := by
  induction h with
  | refl => exact .refl
  | @tail u v _ hadj ih =>
    obtain ⟨e, he, hends⟩ := hadj
    by_cases hem : e = marked
    · subst e
      have hstep : J.reaches (F.erase marked) u v := by
        rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
        · simpa only [hl, hr] using halt
        · simpa only [hl, hr] using J.grove_reaches_symm halt
      exact ih.trans hstep
    · exact ih.tail ⟨e, Finset.mem_erase.mpr ⟨hem, he⟩, hends⟩

/-- Transfer a retained-copy walk through the exact equivalence of original IDs. -/
theorem reaches_of_erase_equiv [Fintype E] [Fintype E₀]
    (K : CopiedGraph V E₀) (marked : E)
    (copies : E₀ ≃ {e : E // e ≠ marked})
    (hleft : ∀ e : E₀, K.left e = J.left (copies e).val)
    (hright : ∀ e : E₀, K.right e = J.right (copies e).val)
    {x y : V} (h : J.reaches (Finset.univ.erase marked) x y) :
    K.reaches Finset.univ x y := by
  induction h with
  | refl => exact .refl
  | @tail u v _ hadj ih =>
    obtain ⟨e, he, hends⟩ := hadj
    let e₀ : E₀ := copies.symm ⟨e, (Finset.mem_erase.mp he).1⟩
    have he₀ : (copies e₀).val = e :=
      congrArg Subtype.val (copies.apply_symm_apply ⟨e, (Finset.mem_erase.mp he).1⟩)
    have hl : K.left e₀ = J.left e :=
      (hleft e₀).trans (congrArg J.left he₀)
    have hr : K.right e₀ = J.right e :=
      (hright e₀).trans (congrArg J.right he₀)
    apply ih.tail
    refine ⟨e₀, Finset.mem_univ e₀, ?_⟩
    simpa only [hl, hr] using hends

/-- A connected copied graph stays connected after one original ID is removed,
provided its endpoints are joined by retained copies. The vertex carrier is unchanged. -/
theorem supportGraph_preconnected_of_erase_equiv [Fintype E] [Fintype E₀]
    (K : CopiedGraph V E₀) (marked : E)
    (copies : E₀ ≃ {e : E // e ≠ marked})
    (hleft : ∀ e : E₀, K.left e = J.left (copies e).val)
    (hright : ∀ e : E₀, K.right e = J.right (copies e).val)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (halt : J.reaches (Finset.univ.erase marked) (J.left marked) (J.right marked)) :
    (supportGraph K.left K.right).Preconnected := by
  apply K.supportGraph_preconnected_of_reaches
  intro x y
  apply J.reaches_of_erase_equiv K marked copies hleft hright
  exact J.reaches_erase_of_alternative marked halt
    (J.reaches_univ_of_supportGraph_reachable (hconn x y))

end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
