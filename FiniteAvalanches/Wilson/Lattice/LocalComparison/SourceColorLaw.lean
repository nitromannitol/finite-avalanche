import FiniteAvalanches.Wilson.Lattice.LocalComparison.ZeroExteriorLaw
import FiniteAvalanches.Wilson.Lattice.LocalComparison.MarkedForestTransport

set_option autoImplicit false
namespace LocalActualSourceConsumer
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Electrical.Plane.SourceLattice MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- The actual D/P source law, consuming color-swap and the fixed-box theorem internally. -/
theorem domain_color_law (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    (finiteUniformLaw (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N).map
      (LocalZeroExterior.field (LocalZeroExterior.domainRoots D P) N) =
        wilsonColorLaw (LocalZeroExterior.domainRoots D P) := by
  apply LocalZeroExterior.zero_exterior_color_law
  intro x hx
  change x ∉ D
  exact fun hd => hx (hDbox x hd)

/-- Every site's complemented forest color means reachability to the original P. -/
theorem domain_field_true_iff (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    (x : Site 2) :
    LocalZeroExterior.field (LocalZeroExterior.domainRoots D P) N F x = true ↔
      ∃ y : FiniteWired.Active N, FiniteWired.site y ∈ P.val.image Subtype.val ∧
        (WiredTrees.graph N).reaches F.val (wiredSite N x) (some y) := by
  rw [LocalZeroExterior.field_true_iff]
  constructor
  · rintro ⟨r, hr, hxr⟩
    cases r with
    | none => exact hr.elim
    | some y => exact ⟨y, hr, hxr⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨some y, hy, hxy⟩

/-- The local source contact event on the actual law and the full box forest carrier. -/
theorem local_contact_event_count (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (A : Set (Site 2)) (a : Site 2) (r : ℕ) (t : ℝ) :
    wilsonColorLaw (LocalZeroExterior.domainRoots D P) (localContactEvent A a r t) =
      (Nat.card {F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N |
        t ≤ (localContacts A a r (LocalZeroExterior.field
          (LocalZeroExterior.domainRoots D P) N F) : ℝ)} : ℝ≥0∞) /
        finiteForestCount (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N :=
  LocalZeroExterior.local_contact_event_count D P N hDbox A a r t

/-- The whole law of the source contact observable, without an event restriction. -/
theorem local_contact_observable_law (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (A : Set (Site 2)) (a : Site 2) (r : ℕ) :
    (wilsonColorLaw (LocalZeroExterior.domainRoots D P)).map (localContacts A a r) =
      (finiteUniformLaw (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N).map
        (fun F => localContacts A a r (LocalZeroExterior.field
          (LocalZeroExterior.domainRoots D P) N F)) := by
  have hm : Measurable (localContacts A a r) := (continuous_contacts _).measurable
  rw [← domain_color_law D P N hDbox]
  rw [Measure.map_map hm
    (LocalZeroExterior.measurable_field _ N)]
  rfl

/-- Swapping colors reverses the source contact threshold, with all four incidences counted. -/
theorem local_contact_threshold_swap (D : Finset (Site 2)) (P : OneSet D)
    (A : Set (Site 2)) (a : Site 2) (r : ℕ) (t : ℝ) :
    wilsonColorLaw (LocalZeroExterior.domainRoots D P) (localContactEvent A a r t) =
      wilsonColorLaw (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P))
        {σ | (localContacts A a r σ : ℝ) ≤
          (4 * ((window a r).filter (fun x => x ∈ A)).card : ℕ) - t} := by
  have h := LocalColorSwap.probability_preimage
    (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) (localContactEvent A a r t)
    (isClopen_localContactEvent A a r t).isClosed.measurableSet
  rw [LocalColorSwap.roots_involutive] at h
  rw [h]
  congr 1
  ext σ
  have he : (localContacts A a r (LocalColorSwap.colors σ) : ℝ) +
      (localContacts A a r σ : ℝ) =
        (4 * ((window a r).filter (fun x => x ∈ A)).card : ℕ) := by
    exact_mod_cast LocalColorSwap.contacts_complement
      ((window a r).filter (fun x => x ∈ A)) σ
  change t ≤ (localContacts A a r (LocalColorSwap.colors σ) : ℝ) ↔
    (localContacts A a r σ : ℝ) ≤ (4 * ((window a r).filter (fun x => x ∈ A)).card : ℕ) - t
  constructor <;> intro ht <;> linarith only [he, ht]

/-- The precise source H/H0 comparison consumes the earlier deletion result internally. -/
theorem reference_primal_color_event_count (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (S : Set (Vertex D P → Bool)) :
    (Nat.card {F : (StatementTypes.graph D P marked).RootedForest
      ({alpha D P, beta D P} : Set (Vertex D P)) |
      (fun x => decide ((StatementTypes.graph D P marked).reaches F.val x (beta D P))) ∈ S} : ℝ) /
      Nat.card ((StatementTypes.graph D P marked).RootedForest
        ({alpha D P, beta D P} : Set (Vertex D P))) =
    (Nat.card {F : (primalGraph D P).RootedForest ({alpha D P, beta D P} : Set (Vertex D P)) |
      (fun x => decide ((primalGraph D P).reaches F.val x (beta D P))) ∈ S} : ℝ) /
      Nat.card ((primalGraph D P).RootedForest ({alpha D P, beta D P} : Set (Vertex D P))) :=
  LocalMarkedForest.color_event_count D P marked S

end
end LocalActualSourceConsumer
