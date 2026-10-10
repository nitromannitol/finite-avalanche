import FiniteAvalanches.Electrical.Plane.Incidence

namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators
noncomputable section

/-- Relabelling all copies and faces preserves boundary of a gradient. Simultaneous
reversal of a primal copy and its dual copy leaves its signed summand unchanged. -/
theorem copyBoundary_gradient_transport_of_per_edge_equations
    {V F G E I : Type} [Fintype E] [Fintype I]
    (copies : E ≃ I) (faces : F ≃ G)
    (u v : E → V) (s t : I → V) (a b : E → F) (c d : I → G)
    (h : ∀ e,
      (u e = s (copies e) ∧ v e = t (copies e) ∧
        faces (a e) = c (copies e) ∧ faces (b e) = d (copies e)) ∨
      (u e = t (copies e) ∧ v e = s (copies e) ∧
        faces (a e) = d (copies e) ∧ faces (b e) = c (copies e)))
    (q : V → ℝ) (F0 : F) :
    copyBoundary a b (copyGradient u v q) F0 =
      copyBoundary c d (copyGradient s t q) (faces F0) := by
  unfold copyBoundary copyGradient
  rw [← copies.sum_comp]
  apply Finset.sum_congr rfl
  intro e _
  have ha : a e = F0 ↔ faces (a e) = faces F0 := faces.injective.eq_iff.symm
  have hb : b e = F0 ↔ faces (b e) = faces F0 := faces.injective.eq_iff.symm
  rcases h e with ⟨hu, hv, hc, hd⟩ | ⟨hu, hv, hd, hc⟩
  · rw [hu, hv, ha, hb, hc, hd]
  · rw [hu, hv, ha, hb, hc, hd]
    split_ifs <;> ring

end
end FiniteAvalanches.Electrical.Plane
