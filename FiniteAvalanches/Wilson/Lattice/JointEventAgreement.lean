import FiniteAvalanches.Wilson.Lattice.Sampler

/-! Joint observation events depend only on their queried coordinates. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Trees.Lattice

/-- Equality on queried edge and color coordinates preserves a joint event. -/
theorem jointEvent_mem_iff_of_agree (E : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) (ω η : ForestField)
    (he : ∀ e ∈ E, ω.1 e = η.1 e) (hd : ∀ z ∈ D, ω.2 z = η.2 z) :
    (ω ∈ jointEvent E D pe pc ↔ η ∈ jointEvent E D pe pc) := by
  constructor
  · intro h
    exact ⟨fun e he' => (he e he').symm.trans (h.1 e he'),
      fun z hz => (hd z hz).symm.trans (h.2 z hz)⟩
  · intro h
    exact ⟨fun e he' => (he e he').trans (h.1 e he'),
      fun z hz => (hd z hz).trans (h.2 z hz)⟩

end FiniteAvalanches.Wilson.Lattice
