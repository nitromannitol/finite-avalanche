import FiniteAvalanches.Wilson.Lattice.WiredDualFaceBox

/-! The exact dual face-edge carrier of a wired square box. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Crossing a dual base edge returns its corresponding primal base edge. -/
theorem crossingEdgeEquiv_baseEdge (p : Site 2 × Fin 2) :
    crossingEdgeEquiv (baseEdge p) = baseEdge (p.1 + unit p.2, 1 - p.2) := by
  change edgeEquiv (dualBaseEquiv (edgeEquiv.symm (baseEdge p))) = _
  rw [show edgeEquiv.symm (baseEdge p) = p from edgeEquiv.symm_apply_apply p]
  rfl

/-- A dual edge inside the face square crosses a primal edge incident to the original box. -/
theorem crossingBase_has_endpoint_inBox (B : ℕ) (z : Site 2) (i : Fin 2)
    (hz : inDualFaceBox B z) (hz' : inDualFaceBox B (z + unit i)) :
    FiniteWired.inBox B (z + unit i) ∨
      FiniteWired.inBox B (z + unit i + unit (1 - i)) := by
  have hz0 := hz 0
  have hz1 := hz 1
  have hz'0 := hz' 0
  have hz'1 := hz' 1
  fin_cases i <;>
    simp only [FiniteWired.inBox, Fin.forall_fin_two, Pi.add_apply, unit, Pi.single_apply] at * <;>
    norm_num at * <;> omega

/-- A dual edge belongs to the face square exactly when it crosses one of the
original wired-box copies. -/
theorem dualFaceEdge_iff_wiredCopy (B : ℕ) (e : LatticeEdge) :
    (∀ z ∈ e.val, inDualFaceBox B z) ↔ ∃ q : FiniteWired.Edge B, wiredCopyDualEdge q = e := by
  constructor
  · intro hbox
    obtain ⟨⟨z, i⟩, he⟩ := baseEdge_surjective e
    have hz : inDualFaceBox B z := by
      apply hbox z
      rw [← he]
      simp [baseEdge]
    have hz' : inDualFaceBox B (z + unit i) := by
      apply hbox (z + unit i)
      rw [← he]
      simp [baseEdge]
    have hp := crossingBase_has_endpoint_inBox B z i hz hz'
    have hex : ∃ v ∈ (crossingEdgeEquiv e).val, FiniteWired.inBox B v := by
      rw [← he, crossingEdgeEquiv_baseEdge]
      rcases hp with h1 | h2
      · exact ⟨z + unit i, by simp [baseEdge], h1⟩
      · exact ⟨z + unit i + unit (1 - i), by simp [baseEdge], h2⟩
    obtain ⟨q, hq⟩ := exists_wiredCopy_of_endpoint_inBox B (crossingEdgeEquiv e) hex
    refine ⟨q, ?_⟩
    apply crossingEdgeEquiv.injective
    simpa only [wiredCopyDualEdge, Equiv.apply_symm_apply] using hq
  · rintro ⟨q, rfl⟩
    exact wiredCopyDualEdge_endpoints_inDualFaceBox B q

/-- Wired edge copies biject with the original edges of the shifted dual face square. -/
def wiredCopyDualFaceEdgeEquiv (B : ℕ) :
    FiniteWired.Edge B ≃ {e : LatticeEdge // ∀ z ∈ e.val, inDualFaceBox B z} :=
  Equiv.ofBijective (fun e => ⟨wiredCopyDualEdge e, wiredCopyDualEdge_endpoints_inDualFaceBox B e⟩)
    ⟨fun _ _ h => wiredCopyDualEdge_injective B (congrArg Subtype.val h), by
      intro e
      obtain ⟨q, hq⟩ := (dualFaceEdge_iff_wiredCopy B e.val).mp e.property
      exact ⟨q, Subtype.ext hq⟩⟩

end
end FiniteAvalanches.Wilson.Lattice
