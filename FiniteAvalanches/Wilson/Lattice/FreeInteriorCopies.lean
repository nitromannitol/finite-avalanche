import FiniteAvalanches.Wilson.Lattice.FreeBoxGraph
import FiniteAvalanches.Wilson.Lattice.WiredActiveStackLaw

/-! Free and wired incident copies agree away from the boundary. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance (N : ℕ) : DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- All neighbors of a site in a smaller box lie in the next larger box. -/
theorem inBox_succ_of_step (N : ℕ) (z : Site 2) (hz : FiniteWired.inBox N z)
    (d : FiniteWired.Direction) : FiniteWired.inBox (N + 1) (z + FiniteWired.step d) := by
  have h0 := hz 0
  have h1 := hz 1
  rcases d with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    simp only [FiniteWired.inBox, Fin.forall_fin_two, Pi.add_apply, FiniteWired.step,
      Bool.false_eq_true, if_false, if_true, unit, Pi.neg_apply, Pi.single_apply] <;>
    norm_num <;> omega

/-- An interior copied edge is also an incident copy in the wired graph. -/
def freeIncidentToWired {N : ℕ} (x : FiniteWired.Active N)
    (e : IncidentCopy (freeBoxGraph N) x) : IncidentCopy (WiredTrees.graph N) (some x) :=
  ⟨.inl e.val, by
    rcases e.property with h | h
    · left
      exact congrArg some h
    · right
      exact congrArg some h⟩

/-- The inclusion of free incident copies into wired copies is injective. -/
theorem freeIncidentToWired_injective {N : ℕ} (x : FiniteWired.Active N) :
    Function.Injective (freeIncidentToWired x) := by
  intro e f h
  apply Subtype.ext
  exact Sum.inl.inj (congrArg Subtype.val h)

/-- At a site of the smaller box every incident wired copy is an interior copy. -/
theorem freeIncidentToWired_surjective (N : ℕ) (x : FiniteWired.Active (N + 1))
    (hx : FiniteWired.inBox N (FiniteWired.site x)) :
    Function.Surjective (freeIncidentToWired x) := by
  intro e
  rcases e with ⟨e, he⟩
  cases e with
  | inl e =>
    have hi : (freeBoxGraph (N + 1)).left e = x ∨
        (freeBoxGraph (N + 1)).right e = x := by
      rcases he with h | h
      · left
        exact Option.some.inj h
      · right
        exact Option.some.inj h
    exact ⟨⟨e, hi⟩, rfl⟩
  | inr e =>
    have heq : e.val.1 = x := by
      rcases he with h | h
      · exact Option.some.inj h
      · cases h
    have hbox := inBox_succ_of_step N (FiniteWired.site x) hx e.val.2
    apply False.elim
    apply e.property
    simpa only [heq] using hbox

/-- Free incident copies at an interior site are exactly the four directions. -/
def freeInteriorDirectionEquiv (N : ℕ) (x : FiniteWired.Active (N + 1))
    (hx : FiniteWired.inBox N (FiniteWired.site x)) :
    FiniteWired.Direction ≃ IncidentCopy (freeBoxGraph (N + 1)) x :=
  (wiredActiveCopyEquiv x).trans
    (Equiv.ofBijective (freeIncidentToWired x)
      ⟨freeIncidentToWired_injective x, freeIncidentToWired_surjective N x hx⟩).symm

/-- Uniform free incident copies at an interior vertex induce a uniform direction. -/
theorem freeInterior_uniform_map_direction (N : ℕ) (x : FiniteWired.Active (N + 1))
    (hx : FiniteWired.inBox N (FiniteWired.site x)) :
    (FiniteAvalanches.uniformMeasure (IncidentCopy (freeBoxGraph (N + 1)) x)).map
      (freeInteriorDirectionEquiv N x hx).symm = directionLaw :=
  FiniteAvalanches.uniform_measure_map_equiv (freeInteriorDirectionEquiv N x hx).symm

/-- Inclusion of an interior incident copy preserves its other endpoint. -/
theorem freeIncidentToWired_head {N : ℕ} (x : FiniteWired.Active N)
    (e : IncidentCopy (freeBoxGraph N) x) :
    incidentCopyHead (WiredTrees.graph N) (some x) (freeIncidentToWired x e) =
      some (incidentCopyHead (freeBoxGraph N) x e) := by
  simp only [incidentCopyHead, freeIncidentToWired, WiredTrees.graph, freeBoxGraph,
    Multigraph.ofEndpoints, FiniteWired.endpoints, Option.some.injEq]
  split_ifs <;> rfl

/-- The direction of an interior free-box instruction gives its lattice successor. -/
theorem freeInteriorDirection_head (N : ℕ) (x : FiniteWired.Active (N + 1))
    (hx : FiniteWired.inBox N (FiniteWired.site x)) (d : FiniteWired.Direction) :
    some (incidentCopyHead (freeBoxGraph (N + 1)) x (freeInteriorDirectionEquiv N x hx d)) =
      wiredHead (N + 1) (some x) d := by
  let e := freeInteriorDirectionEquiv N x hx d
  have he : freeIncidentToWired x e = wiredActiveCopyEquiv x d := by
    change (Equiv.ofBijective (freeIncidentToWired x)
      ⟨freeIncidentToWired_injective x, freeIncidentToWired_surjective N x hx⟩)
      ((Equiv.ofBijective (freeIncidentToWired x)
        ⟨freeIncidentToWired_injective x, freeIncidentToWired_surjective N x hx⟩).symm
          (wiredActiveCopyEquiv x d)) = _
    exact Equiv.apply_symm_apply _ _
  have h := incidentCopyHead_eq_wiredHead x (freeIncidentToWired x e)
  rw [freeIncidentToWired_head, he, Equiv.symm_apply_apply] at h
  exact h

/-- Vertices in the inner box, viewed inside the next larger free box. -/
abbrev FreeInterior (N : ℕ) :=
  {x : FiniteWired.Active (N + 1) // FiniteWired.inBox N (FiniteWired.site x)}

/-- The direction instructions on all vertices of the inner box. -/
def freeInteriorDirectionStacks (N : ℕ)
    (σ : (p : FiniteWired.Active (N + 1) × ℕ) →
      IncidentCopy (freeBoxGraph (N + 1)) p.1) : FreeInterior N × ℕ → FiniteWired.Direction :=
  fun p => (freeInteriorDirectionEquiv N p.1.val p.1.property).symm (σ (p.1.val, p.2))

/-- Inner free-box stacks are jointly independent uniform direction stacks. -/
theorem variableStackLaw_map_freeInteriorDirections (N : ℕ) :
    (variableStackLaw (IncidentCopy (freeBoxGraph (N + 1)))).map
      (freeInteriorDirectionStacks N) = directionStackLaw (FreeInterior N) := by
  let f : FreeInterior N × ℕ → FiniteWired.Active (N + 1) × ℕ :=
    fun p => (p.1.val, p.2)
  have hf : Function.Injective f := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    have he : (x.val, i) = (y.val, j) := h
    cases Prod.mk.inj he with
    | intro hxy hij => exact Prod.ext (Subtype.ext hxy) hij
  let P : (p : FiniteWired.Active (N + 1) × ℕ) →
      Measure (IncidentCopy (freeBoxGraph (N + 1)) p.1) :=
    fun p => FiniteAvalanches.uniformMeasure (IncidentCopy (freeBoxGraph (N + 1)) p.1)
  have hrestrict := Measure.map_infinitePi_infinitePi_of_inj (P := P) hf
  let g : ((p : FreeInterior N × ℕ) → IncidentCopy (freeBoxGraph (N + 1)) p.1.val) →
      (FreeInterior N × ℕ → FiniteWired.Direction) :=
    fun σ p => (freeInteriorDirectionEquiv N p.1.val p.1.property).symm (σ p)
  have hm : Measurable g := measurable_pi_iff.mpr fun p =>
    (measurable_of_finite (freeInteriorDirectionEquiv N p.1.val p.1.property).symm).comp
      (measurable_pi_apply p)
  have hproj : Measurable (fun σ : (p : FiniteWired.Active (N + 1) × ℕ) →
      IncidentCopy (freeBoxGraph (N + 1)) p.1 => fun p : FreeInterior N × ℕ => σ (f p)) :=
    measurable_pi_iff.mpr fun p => measurable_pi_apply (f p)
  change (Measure.infinitePi P).map (freeInteriorDirectionStacks N) = _
  rw [show freeInteriorDirectionStacks N = g ∘ (fun σ p => σ (f p)) from rfl,
    ← Measure.map_map hm hproj, hrestrict]
  have hg : (Measure.infinitePi (fun p : FreeInterior N × ℕ => P (f p))).map g =
      Measure.infinitePi (fun _ : FreeInterior N × ℕ => directionLaw) := by
    rw [Measure.infinitePi_map_pi (fun p : FreeInterior N × ℕ => P (f p))
      (fun p => measurable_of_finite (freeInteriorDirectionEquiv N p.1.val p.1.property).symm)]
    congr 1
    funext p
    exact freeInterior_uniform_map_direction N p.1.val p.1.property
  exact hg

end
end FiniteAvalanches.Wilson.Lattice
