module

public import FiniteAvalanches.Sandpile.Burning.SourceFields
public import Mathlib.Data.Fin.SuccPred

@[expose] public section

/-! Reindex stable fields and all forbidden-subset tests through proved carrier
and degree identities. No field is extended by a default value. -/
namespace FiniteAvalanches.Sandpile.Burning
open scoped Classical
noncomputable section
variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

def reindexHeights (e : X ≃ Y) (d : X → ℕ) (q : Y → ℕ)
    (hd : ∀ x, q (e x) = d x) : ((x : X) → Fin (d x)) ≃ ((y : Y) → Fin (q y)) :=
  e.piCongr fun x => finCongr (hd x).symm

omit [DecidableEq X] [DecidableEq Y] in
theorem reindex_heights_val (e : X ≃ Y) (d : X → ℕ) (q : Y → ℕ)
    (hd : ∀ x, q (e x) = d x) (h : (x : X) → Fin (d x)) (x : X) :
    (reindexHeights e d q hd h (e x)).val = (h x).val := by
  simp only [reindexHeights, Equiv.piCongr_apply_apply, finCongr_apply_coe]

theorem indexed_allowed_iff (e : X ≃ Y) (d : X → ℕ) (q : Y → ℕ)
    (hd : ∀ x, q (e x) = d x) (k : Finset X → X → ℕ) (l : Finset Y → Y → ℕ)
    (hk : ∀ S x, l (S.image e) (e x) = k S x) (h : (x : X) → Fin (d x)) :
    (∀ S : Finset X, ¬(S.Nonempty ∧ ∀ x ∈ S, (h x).val < k S x)) ↔
      ∀ T : Finset Y, ¬(T.Nonempty ∧ ∀ y ∈ T,
        (reindexHeights e d q hd h y).val < l T y) := by
  constructor
  · intro hn T hf
    let S := T.image e.symm
    have hST : S.image e = T := by simp [S, Finset.image_image]
    apply hn S
    refine ⟨hf.1.image e.symm, ?_⟩
    intro x hx
    have he : e x ∈ T := by rw [← hST]; exact Finset.mem_image_of_mem e hx
    have hh := hf.2 (e x) he
    rw [reindex_heights_val] at hh
    have heq := hk S x
    rw [hST] at heq
    exact heq ▸ hh
  · intro hn S hf
    apply hn (S.image e)
    refine ⟨hf.1.image e, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [reindex_heights_val, hk]
    exact hf.2 x hx

omit [DecidableEq Y] in
theorem restricted_allowed_iff (p : X → Prop) (h : {x : X // p x} → ℕ)
    (k : Finset X → X → ℕ) :
    (∀ H (hP : ∀ x ∈ H, p x), ¬(H.Nonempty ∧ ∀ x (hx : x ∈ H),
      h ⟨x, hP x hx⟩ < k H x)) ↔
      ∀ T : Finset {x : X // p x}, ¬(T.Nonempty ∧ ∀ x ∈ T,
        h x < k (T.image Subtype.val) x.val) := by
  constructor
  · intro hn T hf
    have hp : ∀ x ∈ T.image Subtype.val, p x := by
      intro x hx
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
      exact v.property
    apply hn (T.image Subtype.val) hp
    refine ⟨hf.1.image Subtype.val, ?_⟩
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hf.2 v hv
  · intro hn H hp hf
    let f : {x : X // x ∈ H} → {x : X // p x} := fun x => ⟨x.val, hp x.val x.property⟩
    let T := H.attach.image f
    have hTH : T.image Subtype.val = H := by
      dsimp only [T]
      rw [Finset.image_image]
      change H.attach.image Subtype.val = H
      exact Finset.attach_image_val
    apply hn T
    obtain ⟨x, hx⟩ := hf.1
    refine ⟨⟨f ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩⟩, ?_⟩
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    rw [hTH]
    exact hf.2 w.val w.property

end
end FiniteAvalanches.Sandpile.Burning
