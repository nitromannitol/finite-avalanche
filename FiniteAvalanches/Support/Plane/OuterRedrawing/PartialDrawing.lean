import FiniteAvalanches.Support.Plane.OuterRedrawing.StraightSetting

/-!
# Drawings of selected parts of a copied graph

A partial drawing draws a selected set of vertices and a selected set of edges
with the axioms of a plane drawing. A map that is continuous and injective on
its trace transports it to another partial drawing, and two partial drawings
whose traces meet only at common vertex points combine into one.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set
open scoped Classical

noncomputable section

variable {V E : Type} {J : CopiedGraph V E}

/-- A drawing of the selected vertices `S` and selected edges `T`. -/
structure PartialDrawing (J : CopiedGraph V E) (S : Set V) (T : Set E) where
  point : V → ℝ × ℝ
  curve : E → ArcParameter → ℝ × ℝ
  point_injOn : InjOn point S
  continuous : ∀ e ∈ T, Continuous (curve e)
  injOn : ∀ e ∈ T, InjOn (curve e) {t | t.val < 1}
  start : ∀ e ∈ T, curve e zeroParam = point (J.left e)
  finish : ∀ e ∈ T, curve e oneParam = point (J.right e)
  avoids : ∀ e ∈ T, ∀ t : ArcParameter, 0 < t.val → t.val < 1 → ∀ v ∈ S, curve e t ≠ point v
  intersects : ∀ e ∈ T, ∀ f ∈ T, e ≠ f → ∀ s t, curve e s = curve f t →
    (s.val = 0 ∨ s.val = 1) ∧ (t.val = 0 ∨ t.val = 1)

namespace PartialDrawing

variable {S : Set V} {T : Set E}

/-- The points drawn by a partial drawing. -/
def trace (P : PartialDrawing J S T) : Set (ℝ × ℝ) :=
  P.point '' S ∪ {z | ∃ e ∈ T, ∃ t, P.curve e t = z}

theorem point_mem_trace (P : PartialDrawing J S T) {v : V} (hv : v ∈ S) :
    P.point v ∈ P.trace := Or.inl ⟨v, hv, rfl⟩

theorem curve_mem_trace (P : PartialDrawing J S T) {e : E} (he : e ∈ T) (t : ArcParameter) :
    P.curve e t ∈ P.trace := Or.inr ⟨e, he, t, rfl⟩

/-- A curve point equal to a drawn vertex is an end of the curve. -/
theorem param_of_eq_point (P : PartialDrawing J S T) {e : E} (he : e ∈ T) {t : ArcParameter}
    {v : V} (hv : v ∈ S) (h : P.curve e t = P.point v) : t.val = 0 ∨ t.val = 1 := by
  by_contra hne
  push Not at hne
  exact P.avoids e he t (lt_of_le_of_ne t.2.1 (Ne.symm hne.1))
    (lt_of_le_of_ne t.2.2 hne.2) v hv h

/-- Transport of a partial drawing by a map continuous and injective on its trace. -/
def map (P : PartialDrawing J S T) (Ψ : ℝ × ℝ → ℝ × ℝ) (hcont : ContinuousOn Ψ P.trace)
    (hinj : InjOn Ψ P.trace) : PartialDrawing J S T where
  point v := Ψ (P.point v)
  curve e t := Ψ (P.curve e t)
  point_injOn v hv w hw h := P.point_injOn hv hw (hinj (P.point_mem_trace hv)
    (P.point_mem_trace hw) h)
  continuous e he := hcont.comp_continuous (P.continuous e he) fun t => P.curve_mem_trace he t
  injOn e he s hs t ht h := P.injOn e he hs ht (hinj (P.curve_mem_trace he s)
    (P.curve_mem_trace he t) h)
  start e he := by rw [P.start e he]
  finish e he := by rw [P.finish e he]
  avoids e he t h0 h1 v hv h := P.avoids e he t h0 h1 v hv
    (hinj (P.curve_mem_trace he t) (P.point_mem_trace hv) h)
  intersects e he f hf hef s t h := P.intersects e he f hf hef s t
    (hinj (P.curve_mem_trace he s) (P.curve_mem_trace hf t) h)

theorem map_trace (P : PartialDrawing J S T) (Ψ : ℝ × ℝ → ℝ × ℝ)
    (hcont : ContinuousOn Ψ P.trace) (hinj : InjOn Ψ P.trace) :
    (P.map Ψ hcont hinj).trace = Ψ '' P.trace := by
  ext z
  constructor
  · rintro (⟨v, hv, rfl⟩ | ⟨e, he, t, rfl⟩)
    · exact ⟨_, P.point_mem_trace hv, rfl⟩
    · exact ⟨_, P.curve_mem_trace he t, rfl⟩
  · rintro ⟨w, (⟨v, hv, rfl⟩ | ⟨e, he, t, rfl⟩), rfl⟩
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨e, he, t, rfl⟩

/-- Restriction of a partial drawing to fewer vertices and edges. -/
def restrict (P : PartialDrawing J S T) {S' : Set V} {T' : Set E} (hS : S' ⊆ S) (hT : T' ⊆ T) :
    PartialDrawing J S' T' where
  point := P.point
  curve := P.curve
  point_injOn := P.point_injOn.mono hS
  continuous e he := P.continuous e (hT he)
  injOn e he := P.injOn e (hT he)
  start e he := P.start e (hT he)
  finish e he := P.finish e (hT he)
  avoids e he t h0 h1 v hv := P.avoids e (hT he) t h0 h1 v (hS hv)
  intersects e he f hf := P.intersects e (hT he) f (hT hf)

theorem restrict_trace_subset (P : PartialDrawing J S T) {S' : Set V} {T' : Set E} (hS : S' ⊆ S)
    (hT : T' ⊆ T) : (P.restrict hS hT).trace ⊆ P.trace := by
  rintro z (⟨v, hv, rfl⟩ | ⟨e, he, t, rfl⟩)
  · exact Or.inl ⟨v, hS hv, rfl⟩
  · exact Or.inr ⟨e, hT he, t, rfl⟩

/-- Two partial drawings whose traces meet only at common vertex points combine. -/
def union {S₁ S₂ : Set V} {T₁ T₂ : Set E} (P₁ : PartialDrawing J S₁ T₁)
    (P₂ : PartialDrawing J S₂ T₂) (hTS₁ : ∀ e ∈ T₁, J.left e ∈ S₁ ∧ J.right e ∈ S₁)
    (hTS₂ : ∀ e ∈ T₂, J.left e ∈ S₂ ∧ J.right e ∈ S₂)
    (hpt : ∀ v ∈ S₁ ∩ S₂, P₁.point v = P₂.point v)
    (hmeet : ∀ z ∈ P₁.trace, z ∈ P₂.trace → ∃ v ∈ S₁ ∩ S₂, z = P₁.point v) :
    PartialDrawing J (S₁ ∪ S₂) (T₁ ∪ T₂) where
  point v := if v ∈ S₁ then P₁.point v else P₂.point v
  curve e := if e ∈ T₁ then P₁.curve e else P₂.curve e
  point_injOn := by
    have cross : ∀ v ∈ S₁, ∀ w ∈ S₂, P₁.point v = P₂.point w → v = w := by
      intro v hv w hw h
      obtain ⟨u, ⟨hu1, hu2⟩, hzu⟩ := hmeet _ (P₁.point_mem_trace hv) (h ▸ P₂.point_mem_trace hw)
      have hvu : v = u := P₁.point_injOn hv hu1 hzu
      have hwu : w = u := P₂.point_injOn hw hu2 (h.symm.trans (hzu.trans (hpt u ⟨hu1, hu2⟩)))
      rw [hvu, hwu]
    intro v hv w hw h
    simp only at h
    by_cases hv1 : v ∈ S₁ <;> by_cases hw1 : w ∈ S₁ <;> simp only [hv1, hw1, if_true,
      if_false] at h
    · exact P₁.point_injOn hv1 hw1 h
    · exact cross v hv1 w (hw.resolve_left hw1) h
    · exact (cross w hw1 v (hv.resolve_left hv1) h.symm).symm
    · exact P₂.point_injOn (hv.resolve_left hv1) (hw.resolve_left hw1) h
  continuous e he := by
    by_cases h1 : e ∈ T₁
    · simp only [h1, if_true]
      exact P₁.continuous e h1
    · simp only [h1, if_false]
      exact P₂.continuous e (he.resolve_left h1)
  injOn e he := by
    by_cases h1 : e ∈ T₁
    · simp only [h1, if_true]
      exact P₁.injOn e h1
    · simp only [h1, if_false]
      exact P₂.injOn e (he.resolve_left h1)
  start e he := by
    by_cases h1 : e ∈ T₁
    · simp only [h1, if_true, (hTS₁ e h1).1]
      exact P₁.start e h1
    · have h2 := he.resolve_left h1
      simp only [h1, if_false]
      by_cases hl : J.left e ∈ S₁
      · simp only [hl, if_true]
        rw [P₂.start e h2, hpt _ ⟨hl, (hTS₂ e h2).1⟩]
      · simp only [hl, if_false]
        exact P₂.start e h2
  finish e he := by
    by_cases h1 : e ∈ T₁
    · simp only [h1, if_true, (hTS₁ e h1).2]
      exact P₁.finish e h1
    · have h2 := he.resolve_left h1
      simp only [h1, if_false]
      by_cases hr : J.right e ∈ S₁
      · simp only [hr, if_true]
        rw [P₂.finish e h2, hpt _ ⟨hr, (hTS₂ e h2).2⟩]
      · simp only [hr, if_false]
        exact P₂.finish e h2
  avoids e he t h0 h1 v hv := by
    by_cases he1 : e ∈ T₁ <;> by_cases hv1 : v ∈ S₁ <;> simp only [he1, hv1, if_true, if_false]
    · exact P₁.avoids e he1 t h0 h1 v hv1
    · intro h
      have hv2 := hv.resolve_left hv1
      obtain ⟨u, ⟨hu1, hu2⟩, hzu⟩ :=
        hmeet _ (P₁.curve_mem_trace he1 t) (h ▸ P₂.point_mem_trace hv2)
      exact P₁.avoids e he1 t h0 h1 u hu1 hzu
    · intro h
      have he2 := he.resolve_left he1
      obtain ⟨u, ⟨hu1, hu2⟩, hzu⟩ :=
        hmeet _ (P₁.point_mem_trace hv1) (h ▸ P₂.curve_mem_trace he2 t)
      exact P₂.avoids e he2 t h0 h1 u hu2 (h.trans (hzu.trans (hpt u ⟨hu1, hu2⟩)))
    · exact P₂.avoids e (he.resolve_left he1) t h0 h1 v (hv.resolve_left hv1)
  intersects e he f hf hef s t h := by
    have cross : ∀ e ∈ T₁, ∀ f ∈ T₂, ∀ s t, P₁.curve e s = P₂.curve f t →
        (s.val = 0 ∨ s.val = 1) ∧ (t.val = 0 ∨ t.val = 1) := by
      intro e he f hf s t h
      obtain ⟨u, ⟨hu1, hu2⟩, hzu⟩ :=
        hmeet _ (P₁.curve_mem_trace he s) (h ▸ P₂.curve_mem_trace hf t)
      exact ⟨P₁.param_of_eq_point he hu1 hzu,
        P₂.param_of_eq_point hf hu2 (h.symm.trans (hzu.trans (hpt u ⟨hu1, hu2⟩)))⟩
    by_cases he1 : e ∈ T₁ <;> by_cases hf1 : f ∈ T₁ <;> simp only [he1, hf1, if_true,
      if_false] at h
    · exact P₁.intersects e he1 f hf1 hef s t h
    · exact cross e he1 f (hf.resolve_left hf1) s t h
    · exact (cross f hf1 e (he.resolve_left he1) t s h.symm).symm
    · exact P₂.intersects e (he.resolve_left he1) f (hf.resolve_left hf1) hef s t h

theorem union_trace_subset {S₁ S₂ : Set V} {T₁ T₂ : Set E} (P₁ : PartialDrawing J S₁ T₁)
    (P₂ : PartialDrawing J S₂ T₂) (hTS₁ : ∀ e ∈ T₁, J.left e ∈ S₁ ∧ J.right e ∈ S₁)
    (hTS₂ : ∀ e ∈ T₂, J.left e ∈ S₂ ∧ J.right e ∈ S₂)
    (hpt : ∀ v ∈ S₁ ∩ S₂, P₁.point v = P₂.point v)
    (hmeet : ∀ z ∈ P₁.trace, z ∈ P₂.trace → ∃ v ∈ S₁ ∩ S₂, z = P₁.point v) :
    (P₁.union P₂ hTS₁ hTS₂ hpt hmeet).trace ⊆ P₁.trace ∪ P₂.trace := by
  rintro z (⟨v, hv, rfl⟩ | ⟨e, he, t, rfl⟩)
  · change (if v ∈ S₁ then P₁.point v else P₂.point v) ∈ _
    by_cases hv1 : v ∈ S₁
    · simp only [hv1, if_true]
      exact Or.inl (P₁.point_mem_trace hv1)
    · simp only [hv1, if_false]
      exact Or.inr (P₂.point_mem_trace (hv.resolve_left hv1))
  · change (if e ∈ T₁ then P₁.curve e else P₂.curve e) t ∈ _
    by_cases he1 : e ∈ T₁
    · simp only [he1, if_true]
      exact Or.inl (P₁.curve_mem_trace he1 t)
    · simp only [he1, if_false]
      exact Or.inr (P₂.curve_mem_trace (he.resolve_left he1) t)

theorem union_point_left {S₁ S₂ : Set V} {T₁ T₂ : Set E} (P₁ : PartialDrawing J S₁ T₁)
    (P₂ : PartialDrawing J S₂ T₂) (hTS₁ : ∀ e ∈ T₁, J.left e ∈ S₁ ∧ J.right e ∈ S₁)
    (hTS₂ : ∀ e ∈ T₂, J.left e ∈ S₂ ∧ J.right e ∈ S₂)
    (hpt : ∀ v ∈ S₁ ∩ S₂, P₁.point v = P₂.point v)
    (hmeet : ∀ z ∈ P₁.trace, z ∈ P₂.trace → ∃ v ∈ S₁ ∩ S₂, z = P₁.point v) {v : V}
    (hv : v ∈ S₁) : (P₁.union P₂ hTS₁ hTS₂ hpt hmeet).point v = P₁.point v := by
  change (if v ∈ S₁ then P₁.point v else P₂.point v) = _
  simp only [hv, if_true]

theorem union_point_right {S₁ S₂ : Set V} {T₁ T₂ : Set E} (P₁ : PartialDrawing J S₁ T₁)
    (P₂ : PartialDrawing J S₂ T₂) (hTS₁ : ∀ e ∈ T₁, J.left e ∈ S₁ ∧ J.right e ∈ S₁)
    (hTS₂ : ∀ e ∈ T₂, J.left e ∈ S₂ ∧ J.right e ∈ S₂)
    (hpt : ∀ v ∈ S₁ ∩ S₂, P₁.point v = P₂.point v)
    (hmeet : ∀ z ∈ P₁.trace, z ∈ P₂.trace → ∃ v ∈ S₁ ∩ S₂, z = P₁.point v) {v : V}
    (hv : v ∈ S₂) : (P₁.union P₂ hTS₁ hTS₂ hpt hmeet).point v = P₂.point v := by
  change (if v ∈ S₁ then P₁.point v else P₂.point v) = _
  by_cases hv1 : v ∈ S₁
  · simp only [hv1, if_true]
    exact hpt v ⟨hv1, hv⟩
  · simp only [hv1, if_false]

theorem union_curve_left {S₁ S₂ : Set V} {T₁ T₂ : Set E} (P₁ : PartialDrawing J S₁ T₁)
    (P₂ : PartialDrawing J S₂ T₂) (hTS₁ : ∀ e ∈ T₁, J.left e ∈ S₁ ∧ J.right e ∈ S₁)
    (hTS₂ : ∀ e ∈ T₂, J.left e ∈ S₂ ∧ J.right e ∈ S₂)
    (hpt : ∀ v ∈ S₁ ∩ S₂, P₁.point v = P₂.point v)
    (hmeet : ∀ z ∈ P₁.trace, z ∈ P₂.trace → ∃ v ∈ S₁ ∩ S₂, z = P₁.point v) {e : E}
    (he : e ∈ T₁) : (P₁.union P₂ hTS₁ hTS₂ hpt hmeet).curve e = P₁.curve e := by
  change (if e ∈ T₁ then P₁.curve e else P₂.curve e) = _
  simp only [he, if_true]

theorem union_curve_right {S₁ S₂ : Set V} {T₁ T₂ : Set E} (P₁ : PartialDrawing J S₁ T₁)
    (P₂ : PartialDrawing J S₂ T₂) (hTS₁ : ∀ e ∈ T₁, J.left e ∈ S₁ ∧ J.right e ∈ S₁)
    (hTS₂ : ∀ e ∈ T₂, J.left e ∈ S₂ ∧ J.right e ∈ S₂)
    (hpt : ∀ v ∈ S₁ ∩ S₂, P₁.point v = P₂.point v)
    (hmeet : ∀ z ∈ P₁.trace, z ∈ P₂.trace → ∃ v ∈ S₁ ∩ S₂, z = P₁.point v) {e : E}
    (he1 : e ∉ T₁) : (P₁.union P₂ hTS₁ hTS₂ hpt hmeet).curve e = P₂.curve e := by
  change (if e ∈ T₁ then P₁.curve e else P₂.curve e) = _
  simp only [he1, if_false]

end PartialDrawing

/-- A drawing of the whole graph as a partial drawing of a selection. -/
def Drawing.toPartial [Fintype V] [Fintype E] (D : Drawing J) (S : Set V) (T : Set E) : PartialDrawing J S T where
  point := D.point
  curve := D.curve
  point_injOn := D.point_injective.injOn
  continuous e _ := D.continuous e
  injOn e _ := D.injective e
  start e _ := D.start e
  finish e _ := D.finish e
  avoids e _ t h0 h1 v _ := D.avoids e t h0 h1 v
  intersects e _ f _ := D.intersects e f

/-- A partial drawing of all vertices and all edges is a drawing. -/
def PartialDrawing.toDrawing [Fintype V] [Fintype E] (P : PartialDrawing J univ univ) : Drawing J where
  point := P.point
  point_injective v w h := P.point_injOn (mem_univ v) (mem_univ w) h
  curve := P.curve
  continuous e := P.continuous e (mem_univ e)
  injective e := P.injOn e (mem_univ e)
  start e := P.start e (mem_univ e)
  finish e := P.finish e (mem_univ e)
  avoids e t h0 h1 v := P.avoids e (mem_univ e) t h0 h1 v (mem_univ v)
  intersects e f hef := P.intersects e (mem_univ e) f (mem_univ f) hef

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
