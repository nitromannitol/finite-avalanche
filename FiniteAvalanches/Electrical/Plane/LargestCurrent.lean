import FiniteAvalanches.Electrical.Plane.Incidences

/-! The literal incidence maximum agrees with the source maximum over adjacent vertices. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical

theorem largestCurrent_le_iff {V E : Type*} [Fintype E] (a b : E → V) (phi : V → ℝ) (x : V)
    (hx : (incidenceDarts a b x).Nonempty) (c : ℝ) :
    largestCurrent a b phi x hx ≤ c ↔ ∀ d : Dart E, tail a b d = x → |current a b phi d| ≤ c := by
  constructor
  · intro h d hd
    exact (current_le_largestCurrent a b phi x hx d hd).trans h
  · intro h
    apply Finset.max'_le
    intro v hv
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hv
    exact h d ((mem_incidenceDarts a b x d).mp hd)

/-- With the source's no-loop assumption, the maximum has precisely the neighbor-current characterization. -/
theorem largestCurrent_le_iff_neighbors {V E : Type*} [Fintype E] (a b : E → V)
    (hloop : ∀ e, a e ≠ b e) (phi : V → ℝ) (x : V)
    (hx : (incidenceDarts a b x).Nonempty) (c : ℝ) :
    largestCurrent a b phi x hx ≤ c ↔
      ∀ y, (supportGraph a b).Adj x y → |phi x-phi y| ≤ c := by
  rw [largestCurrent_le_iff]
  constructor
  · intro h y hxy
    obtain ⟨_,e,he⟩ := hxy
    rcases he with he | he
    · have hh := h (e,false) he.1
      change |phi (a e)-phi (b e)| ≤ c at hh
      rw [he.1,he.2] at hh
      exact hh
    · have hh := h (e,true) he.1
      change |phi (b e)-phi (a e)| ≤ c at hh
      rw [he.1,he.2] at hh
      exact hh
  · intro h d hd
    have hadj : (supportGraph a b).Adj x (head a b d) := by
      rcases d with ⟨e,k⟩
      cases k
      · change a e = x at hd
        subst x
        exact ⟨hloop e,e,Or.inl ⟨rfl,rfl⟩⟩
      · change b e = x at hd
        subst x
        exact ⟨(hloop e).symm,e,Or.inr ⟨rfl,rfl⟩⟩
    change |phi (tail a b d)-phi (head a b d)| ≤ c
    rw [hd]
    exact h _ hadj

end FiniteAvalanches.Electrical.Plane
