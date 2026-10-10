import FiniteAvalanches.Electrical.Trees.SeparatingForestCompletion

/-! The two actual components of a separating forest determine every edge cut. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type}

theorem twoRootForest_cover (J : CopiedGraph V E) (u v : V)
    (F : J.TwoRootForest u v) (x : V) : J.reaches F.val x u ∨ J.reaches F.val x v := by
  obtain ⟨r, hr, hx, _⟩ := F.property.2 x
  rcases hr with rfl | rfl
  · exact Or.inl hx
  · exact Or.inr hx

/-- Reachability is exactly equality of the component labeled by the first root. -/
theorem twoRootForest_reaches_iff (J : CopiedGraph V E) (u v : V)
    (F : J.TwoRootForest u v) (x y : V) :
    J.reaches F.val x y ↔ (J.reaches F.val x u ↔ J.reaches F.val y u) := by
  constructor
  · intro h
    exact ⟨fun hx => (TwoCopy.reaches_symm J h).trans hx, fun hy => h.trans hy⟩
  · intro h
    by_cases hx : J.reaches F.val x u
    · exact hx.trans (TwoCopy.reaches_symm J (h.mp hx))
    · have hy : ¬J.reaches F.val y u := fun hy => hx (h.mpr hy)
      exact ((twoRootForest_cover J u v F x).resolve_left hx).trans
        (TwoCopy.reaches_symm J ((twoRootForest_cover J u v F y).resolve_left hy))

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
