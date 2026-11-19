import FiniteAvalanches.Support.Plane.DeletedEdgeFaces
import FiniteAvalanches.Support.Plane.DualFaceCoverage

/-!
# Dual walks and faces of a subdrawing

After deleting edges from a finite plane drawing, two original faces lie in the
same face of the subdrawing exactly when they are joined in the dual using the
deleted edges.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST ComplementFaces DrawingContraction Set
open scoped Classical

/-- Faces project to the same subdrawing face exactly when a dual walk uses
only the omitted original edges. -/
theorem faceProjection_eq_iff_dual_reaches_of_restrictDrawing
    {V E E₀ : Type} [Fintype V] [Fintype E] [Fintype E₀] [Nonempty E]
    {J : CopiedGraph V E} {K : CopiedGraph V E₀} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (i : E₀ → E) (hi : Function.Injective i)
    (hl : ∀ f, J.left (i f) = K.left f) (hr : ∀ f, J.right (i f) = K.right f)
    (S : Finset E) (hS : ∀ e, e ∈ S ↔ e ∉ range i) (A B : Face D) :
    let R := restrictDrawing D i hi hl hr
    let traceSub : drawingTrace R ⊆ drawingTrace D :=
      drawingTrace_restrictDrawing_subset D i hi hl hr
    let dual : CopiedGraph (Face D) E :=
      ⟨fun e => negativeChartFace D e (charts e),
        fun e => positiveChartFace D e (charts e)⟩
    faceProjection D R traceSub A = faceProjection D R traceSub B ↔ dual.reaches S A B := by
  let R := restrictDrawing D i hi hl hr
  let traceSub : drawingTrace R ⊆ drawingTrace D :=
    drawingTrace_restrictDrawing_subset D i hi hl hr
  let dual : CopiedGraph (Face D) E :=
    ⟨fun e => negativeChartFace D e (charts e),
      fun e => positiveChartFace D e (charts e)⟩
  change faceProjection D R traceSub A = faceProjection D R traceSub B ↔ dual.reaches S A B
  constructor
  swap
  · intro h
    apply faceProjection_eq_of_dual_reaches D R traceSub charts S
    · intro e he
      exact midpoint_off_restrictDrawing D i hi hl hr e ((hS e).mp he)
    · exact h
  · intro hproject
    by_contra hAB
    letI : Finite (Face D) := (finite_faces_and_card_le D charts).1
    let P : Face D → Prop := fun F => dual.reaches S A F
    let C : Set Plane := ⋃ F : {F : Face D // P F}, closure (faceRegion D F.val)
    let N : Set Plane := ⋃ F : {F : Face D // ¬ P F}, closure (faceRegion D F.val)
    have hC : IsClosed C := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
    have hN : IsClosed N := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
    let T : Set Plane := faceRegion R (faceProjection D R traceSub A) \ range D.point
    have hT : IsPreconnected T :=
      isPreconnected_sdiff_finite (punctured_faceRegion_isOpen R _)
        (faceRegion_isConnected R _).isPreconnected (finite_range D.point)
    have hmeet : ∀ {z : Plane}, z ∈ T → ∀ F G : Face D,
        z ∈ closure (faceRegion D F) → z ∈ closure (faceRegion D G) → (P F ↔ P G) := by
      intro z hz F G hF hG
      by_cases hd : z ∈ drawingTrace D
      · rcases hd with hv | he
        · exact (hz.2 hv).elim
        · obtain ⟨e, t, ht⟩ := mem_iUnion.mp he
          have ht0 : 0 < t.val := by
            by_contra h
            have h0 : t.val = 0 := le_antisymm (le_of_not_gt h) t.property.1
            have ht' : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext h0
            apply hz.2
            refine ⟨J.left e, ?_⟩
            rw [← ht, ht', D.start]
          have ht1 : t.val < 1 := by
            by_contra h
            have h1 : t.val = 1 := le_antisymm t.property.2 (le_of_not_gt h)
            have ht' : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext h1
            apply hz.2
            refine ⟨J.right e, ?_⟩
            rw [← ht, ht', D.finish]
          have heS : e ∈ S := (hS e).mpr (by
            rintro ⟨f, rfl⟩
            apply hz.1.1
            exact Or.inr (mem_iUnion.mpr ⟨f, t, ht⟩))
          have hF' := (mem_closure_faceRegion_iff_chart_face_of_interior
            D e (charts e) F t ht0 ht1).mp (ht ▸ hF)
          have hG' := (mem_closure_faceRegion_iff_chart_face_of_interior
            D e (charts e) G t ht0 ht1).mp (ht ▸ hG)
          have hposneg : dual.reaches S (positiveChartFace D e (charts e))
              (negativeChartFace D e (charts e)) :=
            .single ⟨e, heS, Or.inr ⟨rfl, rfl⟩⟩
          have hnegpos : dual.reaches S (negativeChartFace D e (charts e))
              (positiveChartFace D e (charts e)) :=
            .single ⟨e, heS, Or.inl ⟨rfl, rfl⟩⟩
          have hFG : dual.reaches S F G := by
            rcases hF' with hF' | hF' <;> rcases hG' with hG' | hG' <;>
              simp only [hF', hG']
            · exact .refl
            · exact hposneg
            · exact hnegpos
            · exact .refl
          have hGF : dual.reaches S G F := by
            rcases hF' with hF' | hF' <;> rcases hG' with hG' | hG' <;>
              simp only [hF', hG']
            · exact .refl
            · exact hnegpos
            · exact hposneg
            · exact .refl
          exact ⟨fun h => h.trans hFG, fun h => h.trans hGF⟩
      · have hF' := mem_faceRegion_of_mem_closure D F hd hF
        have hG' := mem_faceRegion_of_mem_closure D G hd hG
        have heq : F = G := hF'.2.symm.trans hG'.2
        rw [heq]
    have hCN : ∀ z ∈ T, ¬ (z ∈ C ∧ z ∈ N) := by
      intro z hz ⟨hc, hn⟩
      obtain ⟨F, hF⟩ := mem_iUnion.mp hc
      obtain ⟨G, hG⟩ := mem_iUnion.mp hn
      exact G.property ((hmeet hz F.val G.val hF hG).mp F.property)
    have hTCN : T ⊆ Nᶜ ∪ Cᶜ := by
      intro z hz
      by_cases hn : z ∈ N
      · exact Or.inr (fun hc => hCN z hz ⟨hc, hn⟩)
      · exact Or.inl hn
    have hcover : ∀ z : Plane, ∃ F : Face D, z ∈ closure (faceRegion D F) := by
      have hfaces : (⋃ F : Face D, faceRegion D F) = (drawingTrace D)ᶜ := by
        ext z
        constructor
        · intro hz
          obtain ⟨F, hF⟩ := mem_iUnion.mp hz
          exact hF.1
        · intro hz
          exact mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨z, hz⟩, hz, rfl⟩
      intro z
      have hdense : Dense (drawingTrace D)ᶜ :=
        interior_eq_empty_iff_dense_compl.mp (drawingTrace_interior_eq_empty D)
      have hz : z ∈ closure (⋃ F : Face D, faceRegion D F) := by
        rw [hfaces]
        exact hdense z
      rw [closure_iUnion_of_finite] at hz
      exact mem_iUnion.mp hz
    obtain ⟨x, hx⟩ := (faceRegion_isConnected D A).nonempty
    obtain ⟨y, hy⟩ := (faceRegion_isConnected D B).nonempty
    have hxT : x ∈ T := ⟨faceRegion_subset_faceProjection D R traceSub A hx,
      fun hv => hx.1 (Or.inl hv)⟩
    have hyT : y ∈ T := ⟨hproject ▸ faceRegion_subset_faceProjection D R traceSub B hy,
      fun hv => hy.1 (Or.inl hv)⟩
    have hxC : x ∈ C := mem_iUnion.mpr ⟨⟨A, .refl⟩, subset_closure hx⟩
    have hyN : y ∈ N := mem_iUnion.mpr ⟨⟨B, hAB⟩, subset_closure hy⟩
    obtain ⟨z, hz, hzN, hzC⟩ := hT Nᶜ Cᶜ hN.isOpen_compl hC.isOpen_compl hTCN
      ⟨x, hxT, fun hn => hCN x hxT ⟨hxC, hn⟩⟩
      ⟨y, hyT, fun hc => hCN y hyT ⟨hc, hyN⟩⟩
    obtain ⟨F, hF⟩ := hcover z
    by_cases hPF : P F
    · exact hzC (mem_iUnion.mpr ⟨⟨F, hPF⟩, hF⟩)
    · exact hzN (mem_iUnion.mpr ⟨⟨F, hPF⟩, hF⟩)

end FiniteAvalanches.Electrical.StatementGeometry
