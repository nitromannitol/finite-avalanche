import FiniteAvalanches.Wilson.Lattice.LocalComparison.SourceObservable

set_option autoImplicit false
namespace LocalBoxActualSourceConsumer
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.Plane.SourceLattice MeasureTheory
open scoped Classical
noncomputable section

/-- Bare source D/P data produce a bijection between both entire actual forest carriers. -/
def box_root_contraction_bijection (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N ≃
      (primalGraph D P).RootedForest ({alpha D P,beta D P} : Set (Vertex D P)) :=
  LocalBoxContraction.forestEquiv D P N hDbox

theorem box_inverse_identities (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    (∀ F, (box_root_contraction_bijection D P N hDbox).symm
      (box_root_contraction_bijection D P N hDbox F) = F) ∧
    (∀ F, box_root_contraction_bijection D P N hDbox
      ((box_root_contraction_bijection D P N hDbox).symm F) = F) :=
  ⟨LocalBoxContraction.forestEquiv_left_inv D P N hDbox,
    LocalBoxContraction.forestEquiv_right_inv D P N hDbox⟩

theorem copied_edge_membership (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    (e : FiniteWired.Edge N) :
    (∃ c ∈ (box_root_contraction_bijection D P N hDbox F).val,
      c.val = LocalBoxContraction.boxID e) ↔ e ∈ F.val := by
  rw [← Finset.mem_image]
  change LocalBoxContraction.boxID e ∈
    (LocalBoxContraction.forestEquiv D P N hDbox F).val.image Subtype.val ↔ _
  rw [LocalBoxContraction.forestEquiv_original_ids]
  constructor
  · rintro he
    obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp he
    exact (LocalBoxContraction.boxID_injective N hfe) ▸ hf
  · intro he
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩

theorem whole_denominator (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    finiteForestCount (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N =
      Nat.card ((primalGraph D P).RootedForest ({alpha D P,beta D P} : Set (Vertex D P))) :=
  LocalBoxContraction.full_denominator D P N hDbox

theorem actual_P_color (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    (x : Site 2) :
    (primalGraph D P).reaches (box_root_contraction_bijection D P N hDbox F).val
        (project D P x) (beta D P) ↔
      ∃ y : FiniteWired.Active N, FiniteWired.site y ∈ P.val.image Subtype.val ∧
        (WiredTrees.graph N).reaches F.val (wiredSite N x) (some y) := by
  rw [← LocalActualSourceConsumer.domain_field_true_iff D P N F x]
  have h := congrFun (LocalBoxContraction.field_transport D P N hDbox F) x
  change decide ((primalGraph D P).reaches (box_root_contraction_bijection D P N hDbox F).val
    (project D P x) (beta D P)) = LocalZeroExterior.field (LocalZeroExterior.domainRoots D P) N F x at h
  rw [← h, decide_eq_true_eq]

/-- Every exterior root, including the wired sink, has the source alpha color. -/
theorem actual_exterior_color (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    (x : FiniteWired.Vertex N) :
    (primalGraph D P).reaches (box_root_contraction_bijection D P N hDbox F).val
      (LocalBoxContraction.vertexMap D P N x) (alpha D P) ↔
      ∃ r ∈ wiredOne (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N,
        (WiredTrees.graph N).reaches F.val x r :=
  LocalBoxContraction.reaches_alpha_iff D P N hDbox F x

/-- Both actual unique-root witnesses are produced internally for every box vertex. -/
theorem actual_unique_root (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    (x : FiniteWired.Vertex N) :
    ∃ r : FiniteWired.Vertex N,
      r ∈ (wiredRoots (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N).val ∧
      (WiredTrees.graph N).reaches F.val x r ∧
      LocalBoxContraction.vertexMap D P N r ∈ ({alpha D P,beta D P} : Set (Vertex D P)) ∧
      (primalGraph D P).reaches (box_root_contraction_bijection D P N hDbox F).val
        (LocalBoxContraction.vertexMap D P N x) (LocalBoxContraction.vertexMap D P N r) ∧
      (∀ s ∈ ({alpha D P,beta D P} : Set (Vertex D P)),
        (primalGraph D P).reaches (box_root_contraction_bijection D P N hDbox F).val
          (LocalBoxContraction.vertexMap D P N x) s → s = LocalBoxContraction.vertexMap D P N r) ∧
      (∀ s ∈ (wiredRoots (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N).val,
        (WiredTrees.graph N).reaches F.val x s → s = r) := by
  obtain ⟨r,hr,hxr,hu⟩ := F.property.2 x
  obtain ⟨hm,hreach,hunique⟩ := LocalBoxContraction.unique_root_transport D P N hDbox F x r hr hxr
  exact ⟨r,hr,hxr,hm,hreach,hunique,hu⟩

/-- The entire actual H0 uniform color law, with every mathematical arrow discharged internally. -/
theorem actual_H0_color_law (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (marked : MarkedCopy D P) :
    letI : Nonempty ((StatementTypes.graph D P marked).RootedForest
      ({alpha D P,beta D P} : Set (Vertex D P))) :=
        LocalBoxContraction.referenceForest_nonempty D P N hDbox marked
    (uniformMeasure ((StatementTypes.graph D P marked).RootedForest
      ({alpha D P,beta D P} : Set (Vertex D P)))).map
      (fun F x => decide ((StatementTypes.graph D P marked).reaches F.val (project D P x) (beta D P))) =
        wilsonColorLaw (LocalZeroExterior.domainRoots D P) :=
  LocalBoxContraction.reference_color_law D P N hDbox marked

/-- The retained original-copy observable consumes the full boundary accounting. -/
theorem actual_H0_observable (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P)
    (F : (StatementTypes.graph D P marked).RootedForest
      ({alpha D P,beta D P} : Set (Vertex D P))) (A : Set (Site 2)) :
    ReferenceMoment.boundaryContacts D P marked F =
      (LocalBoxContraction.exteriorContacts D A
        (fun x => decide ((StatementTypes.graph D P marked).reaches F.val (project D P x) (beta D P))) : ℝ) - 1 +
      (LocalBoxContraction.exteriorContacts D ((D : Set (Site 2))ᶜ \ A)
        (fun x => decide ((StatementTypes.graph D P marked).reaches F.val (project D P x) (beta D P))) : ℝ) :=
  LocalBoxContraction.source_observable_identity D P marked F A

end
end LocalBoxActualSourceConsumer
