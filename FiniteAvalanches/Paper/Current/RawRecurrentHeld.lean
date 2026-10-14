import FiniteAvalanches.Paper.Current.RawGraphConnectivity
import FiniteAvalanches.Sandpile.Recurrence.RawGraphTreeTransport
import FiniteAvalanches.Sandpile.Burning.RawHeldLaw

/-! Source recurrence is all-integer accessibility. Both actual clocks and
the whole signed field law transport through the internally proved criterion. -/
namespace FiniteAvalanches.Paper.CurrentRawBurning
open FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

theorem source_recurrence_criterion (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (η : RawGraph.StableState G s) :
    RawGraph.Accessible G s η.val ↔ RawGraph.NoFSC G s η.val :=
  (RawGraph.no_fsc_iff_accessible G s ((connected_iff_reaches G).mpr hconn) η.val).symm

def sourceAllowedEquiv (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    RawGraph.RecurrentState G s ≃ RawGraph.AllowedState G s :=
  RawGraph.recurrentAllowedEquiv G s ((connected_iff_reaches G).mpr hconn)

theorem source_allowed_field_value (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (η : RawGraph.RecurrentState G s) : (sourceAllowedEquiv G s hconn η).val.val = η.val.val := rfl

/-- The two independently produced integer recursions agree at every clock. -/
theorem peer_clock_eq_raw (η : RawGraph.Field s) (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    RawGraph.heldParallelRemainder G s η B n = RawGraph.rawParallelRemainder G s η B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [RawGraph.heldParallelRemainder, RawGraph.rawParallelRemainder, ih]

theorem source_parallel_eq_peer (η : RawGraph.StableState G s)
    (B : Finset (Burning.SourceVertex s)) (n : ℕ) :
    RawGraph.sourceHeldParallelRemainder G s η B n = RawGraph.heldParallelRemainder G s η.val B n :=
  (peer_clock_eq_raw G s η.val B n).symm

theorem source_terminal_eq_peer (η : RawGraph.StableState G s)
    (B : Finset (Burning.SourceVertex s)) :
    RawGraph.sourceHeldBurning G s η B = RawGraph.heldBurning G s η.val B :=
  source_parallel_eq_peer G s η B (Fintype.card (Burning.SourceVertex s))

theorem source_closed_iff_peer (η : RawGraph.Field s) (B A : Finset (Burning.SourceVertex s)) :
    RawGraph.heldClosed G s η B A ↔ RawGraph.HeldClosed G s η B A := Iff.rfl

theorem source_terminal_characterization_peer (η : RawGraph.StableState G s)
    (B A : Finset (Burning.SourceVertex s)) :
    RawGraph.sourceHeldBurning G s η B = A ↔
      RawGraph.HeldClosed G s η.val B A ∧ ∀ D, RawGraph.HeldClosed G s η.val B D → D ⊆ A :=
  RawGraph.source_terminal_characterization G s η B A

theorem source_stop_of_recurrent (η : RawGraph.RecurrentState G s)
    (B : Finset (Burning.SourceVertex s)) :
    RawGraph.sourceHeldBurning G s η.val B = RawGraph.heldStop G s B η :=
  source_terminal_eq_peer G s η.val B

def sourceRecurrentLaw (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    Measure (RawGraph.RecurrentState G s) :=
  RawGraph.recurrentLaw G s ((connected_iff_reaches G).mpr hconn)

theorem source_recurrent_allowed_law (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    letI := RawGraph.recurrentFintype G s ((connected_iff_reaches G).mpr hconn)
    letI := RawGraph.recurrentNonempty G s ((connected_iff_reaches G).mpr hconn)
    letI : Nonempty (RawGraph.AllowedState G s) := Nonempty.map (sourceAllowedEquiv G s hconn) inferInstance
    Measure.map (sourceAllowedEquiv G s hconn) (sourceRecurrentLaw G s hconn) =
      FiniteAvalanches.uniformMeasure (RawGraph.AllowedState G s) := by
  letI := RawGraph.recurrentFintype G s ((connected_iff_reaches G).mpr hconn)
  letI := RawGraph.recurrentNonempty G s ((connected_iff_reaches G).mpr hconn)
  letI : Nonempty (RawGraph.AllowedState G s) := Nonempty.map (sourceAllowedEquiv G s hconn) inferInstance
  exact FiniteAvalanches.uniform_measure_map_equiv (sourceAllowedEquiv G s hconn)

/-- Whole signed source field, with accessibility recurrence and no order input. -/
theorem source_recurrent_signed_field_law
    (hconn : ∀ x y : V, G.reaches Finset.univ x y) [MeasurableSpace (RawGraph.Field s)] :
    letI := RawGraph.recurrentFintype G s ((connected_iff_reaches G).mpr hconn)
    letI := RawGraph.recurrentNonempty G s ((connected_iff_reaches G).mpr hconn)
    letI : Nonempty {h : Burning.SourceHeights G s // Burning.noForbidden G (Finset.univ.erase s) h} :=
      Nonempty.map (RawGraph.recurrentFieldEquiv G s ((connected_iff_reaches G).mpr hconn)) inferInstance
    Measure.map (fun η : RawGraph.RecurrentState G s => η.val.val) (sourceRecurrentLaw G s hconn) =
      Measure.map (fun h : {h : Burning.SourceHeights G s //
        Burning.noForbidden G (Finset.univ.erase s) h} => fun x => ((h.val x).val : ℤ))
        (FiniteAvalanches.uniformMeasure {h : Burning.SourceHeights G s //
          Burning.noForbidden G (Finset.univ.erase s) h}) := by
  letI : LinearOrder E := RawGraph.chosenEdgeOrder (E := E)
  letI := RawGraph.recurrentFintype G s ((connected_iff_reaches G).mpr hconn)
  letI := RawGraph.recurrentNonempty G s ((connected_iff_reaches G).mpr hconn)
  letI : Nonempty {h : Burning.SourceHeights G s // Burning.noForbidden G (Finset.univ.erase s) h} :=
    Nonempty.map (RawGraph.recurrentFieldEquiv G s ((connected_iff_reaches G).mpr hconn)) inferInstance
  letI : Nonempty (RawGraph.AllowedState G s) := Nonempty.map (sourceAllowedEquiv G s hconn) inferInstance
  have he : (fun η : RawGraph.RecurrentState G s => η.val.val) =
      (fun η : RawGraph.AllowedState G s => η.val.val) ∘ sourceAllowedEquiv G s hconn := rfl
  rw [he, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    source_recurrent_allowed_law G s hconn]
  exact RawGraph.raw_no_fsc_source_field_law G s hconn

theorem source_recurrent_encoding_value (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (η : RawGraph.RecurrentState G s) (x : Burning.SourceVertex s) :
    (((RawGraph.recurrentFieldEquiv G s ((connected_iff_reaches G).mpr hconn) η).val x).val : ℤ) =
      η.val.val x :=
  RawGraph.recurrent_encoding_value G s ((connected_iff_reaches G).mpr hconn) η x

theorem source_recurrent_encoding_unique (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (η : RawGraph.RecurrentState G s) (f : Burning.SourceHeights G s)
    (hf : ∀ x, ((f x).val : ℤ) = η.val.val x) :
    f = (RawGraph.recurrentFieldEquiv G s ((connected_iff_reaches G).mpr hconn) η).val :=
  RawGraph.recurrent_encoding_unique G s ((connected_iff_reaches G).mpr hconn) η f hf

end
end FiniteAvalanches.Paper.CurrentRawBurning
