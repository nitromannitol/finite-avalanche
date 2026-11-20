import FiniteAvalanches.Wilson.Lattice.WiredDualFaceIncident

/-! Independent dual face stacks restricted to the centered interior. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Each face vertex has at least one incident copy. -/
instance wiredDualFaceIncidentNonempty (B : ℕ) (x : WiredDualFace B) :
    Nonempty (IncidentCopy (wiredDualFaceGraph B) x) := by
  let a : WiredDualFace B := wiredDualFaceOfSite B 0 (by intro i; simp)
  let b : WiredDualFace B := wiredDualFaceOfSite B (-unit 0) (by
    intro i
    fin_cases i <;> simp [unit] <;> omega)
  have hab : a ≠ b := by
    intro h
    have h0 := congrArg (fun z : WiredDualFace B => (z 0).val) h
    simp [a, b, wiredDualFaceOfSite, unit] at h0
  by_cases hx : x = a
  · subst x
    exact incidentCopy_nonempty_of_reaches_ne _ Finset.univ hab
      (wiredDualFaceGraph_connected B a b)
  · exact incidentCopy_nonempty_of_reaches_ne _ Finset.univ hx
      (wiredDualFaceGraph_connected B x a)

/-- At an interior vertex the four directions biject with face-square incident copies. -/
def wiredDualFaceInteriorDirectionEquiv (B : ℕ) (x : FiniteWired.Active (B + 1))
    (hx : FiniteWired.inBox B (FiniteWired.site x)) :
    FiniteWired.Direction ≃
      IncidentCopy (wiredDualFaceGraph (B + 1)) (wiredDualFaceInnerVertex (B + 1) x) :=
  (freeInteriorDirectionEquiv B x hx).trans (wiredDualFaceInnerIncidentEquiv B x hx)

/-- Corresponding interior directions have the same successor in both graphs. -/
theorem wiredDualFaceInteriorDirection_head (B : ℕ) (x : FiniteWired.Active (B + 1))
    (hx : FiniteWired.inBox B (FiniteWired.site x)) (d : FiniteWired.Direction) :
    incidentCopyHead (wiredDualFaceGraph (B + 1)) (wiredDualFaceInnerVertex (B + 1) x)
        (wiredDualFaceInteriorDirectionEquiv B x hx d) =
      wiredDualFaceInnerVertex (B + 1)
        (incidentCopyHead (freeBoxGraph (B + 1)) x (freeInteriorDirectionEquiv B x hx d)) :=
  wiredDualFaceInnerIncident_head (B + 1) x (freeInteriorDirectionEquiv B x hx d)

/-- Uniform face-square instructions give uniform directions in the interior. -/
theorem wiredDualFaceInterior_uniform_map_direction (B : ℕ)
    (x : FiniteWired.Active (B + 1)) (hx : FiniteWired.inBox B (FiniteWired.site x)) :
    (FiniteAvalanches.uniformMeasure
      (IncidentCopy (wiredDualFaceGraph (B + 1)) (wiredDualFaceInnerVertex (B + 1) x))).map
      (wiredDualFaceInteriorDirectionEquiv B x hx).symm = directionLaw :=
  FiniteAvalanches.uniform_measure_map_equiv (wiredDualFaceInteriorDirectionEquiv B x hx).symm

/-- The direction stacks on the centered interior of the dual face square. -/
def wiredDualFaceInteriorDirectionStacks (B : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1) :
    FreeInterior B × ℕ → FiniteWired.Direction :=
  fun p => (wiredDualFaceInteriorDirectionEquiv B p.1.val p.1.property).symm
    (σ (wiredDualFaceInnerVertex (B + 1) p.1.val, p.2))

/-- Interior face-square stacks are independent uniform direction stacks. -/
theorem variableStackLaw_map_wiredDualFaceInteriorDirections (B : ℕ) :
    (variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))).map
      (wiredDualFaceInteriorDirectionStacks B) = directionStackLaw (FreeInterior B) := by
  let f : FreeInterior B × ℕ → WiredDualFace (B + 1) × ℕ :=
    fun p => (wiredDualFaceInnerVertex (B + 1) p.1.val, p.2)
  have hf : Function.Injective f := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    have he : (wiredDualFaceInnerVertex (B + 1) x.val, i) =
        (wiredDualFaceInnerVertex (B + 1) y.val, j) := h
    cases Prod.mk.inj he with
    | intro hxy hij =>
      exact Prod.ext (Subtype.ext (wiredDualFaceInnerVertex_injective (B + 1) hxy)) hij
  let P : (p : WiredDualFace (B + 1) × ℕ) →
      Measure (IncidentCopy (wiredDualFaceGraph (B + 1)) p.1) :=
    fun p => FiniteAvalanches.uniformMeasure (IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
  have hrestrict := Measure.map_infinitePi_infinitePi_of_inj (P := P) hf
  let g : ((p : FreeInterior B × ℕ) →
      IncidentCopy (wiredDualFaceGraph (B + 1)) (wiredDualFaceInnerVertex (B + 1) p.1.val)) →
      (FreeInterior B × ℕ → FiniteWired.Direction) :=
    fun σ p => (wiredDualFaceInteriorDirectionEquiv B p.1.val p.1.property).symm (σ p)
  have hm : Measurable g := measurable_pi_iff.mpr fun p =>
    (measurable_of_finite (wiredDualFaceInteriorDirectionEquiv B p.1.val p.1.property).symm).comp
      (measurable_pi_apply p)
  have hproj : Measurable (fun σ : (p : WiredDualFace (B + 1) × ℕ) →
      IncidentCopy (wiredDualFaceGraph (B + 1)) p.1 => fun p : FreeInterior B × ℕ => σ (f p)) :=
    measurable_pi_iff.mpr fun p => measurable_pi_apply (f p)
  change (Measure.infinitePi P).map (wiredDualFaceInteriorDirectionStacks B) = _
  rw [show wiredDualFaceInteriorDirectionStacks B = g ∘ (fun σ p => σ (f p)) from rfl,
    ← Measure.map_map hm hproj, hrestrict]
  have hg : (Measure.infinitePi (fun p : FreeInterior B × ℕ => P (f p))).map g =
      Measure.infinitePi (fun _ : FreeInterior B × ℕ => directionLaw) := by
    rw [Measure.infinitePi_map_pi (fun p : FreeInterior B × ℕ => P (f p))
      (fun p => measurable_of_finite (wiredDualFaceInteriorDirectionEquiv B p.1.val p.1.property).symm)]
    congr 1
    funext p
    exact wiredDualFaceInterior_uniform_map_direction B p.1.val p.1.property
  exact hg

/-- The free-box and dual face-square interior direction stacks have the same law. -/
theorem free_and_dualFace_interior_direction_stacks_law (B : ℕ) :
    (variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))).map
        (freeInteriorDirectionStacks B) =
      (variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))).map
        (wiredDualFaceInteriorDirectionStacks B) := by
  rw [variableStackLaw_map_freeInteriorDirections,
    variableStackLaw_map_wiredDualFaceInteriorDirections]

end
end FiniteAvalanches.Wilson.Lattice
