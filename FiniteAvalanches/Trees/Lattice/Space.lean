import LatticeProb.Site
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The literal infinite lattice-edge space. A coordinate is one unordered
nearest-neighbor edge, and a field records precisely its presence. Graph and end
predicates use all original lattice vertices. No infinite probability law is chosen. -/
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb
open scoped Classical

/-- Each actual unordered nearest-neighbor lattice edge occurs once. -/
abbrev LatticeEdge := (lattice 2).edgeSet

/-- The product of two-point edge indicators, with its standard product structures. -/
abbrev EdgeField := LatticeEdge → Bool

/-- The selected graph on the entire original lattice vertex carrier. -/
def toGraph (ω : EdgeField) : SimpleGraph (Site 2) where
  Adj x y := ∃ h : (lattice 2).Adj x y, ω ⟨s(x, y), h⟩ = true
  symm := ⟨by
    rintro x y ⟨h, hω⟩
    refine ⟨h.symm, ?_⟩
    have he : (⟨s(y, x), h.symm⟩ : LatticeEdge) = ⟨s(x, y), h⟩ :=
      Subtype.ext Sym2.eq_swap
    rw [he]
    exact hω⟩
  loopless := ⟨fun x ⟨h, _⟩ => (lattice 2).loopless.irrefl x h⟩

theorem toGraph_le_lattice (ω : EdgeField) : toGraph ω ≤ lattice 2 :=
  fun _ _ h => h.choose

theorem toGraph_adj_iff (ω : EdgeField) {x y : Site 2} (h : (lattice 2).Adj x y) :
    (toGraph ω).Adj x y ↔ ω ⟨s(x, y), h⟩ = true := by
  constructor
  · rintro ⟨_, hω⟩
    exact hω
  · intro hω
    exact ⟨h, hω⟩

/-- A spanning tree uses every lattice vertex and has no cycle. -/
def IsTree (ω : EdgeField) : Prop := (toGraph ω).IsTree

/-- Exactly one graph end, using Mathlib's sections of the finite-complement
component inverse system. The nonempty clause excludes zero-ended graphs. -/
def OneEnded (ω : EdgeField) : Prop :=
  Nonempty (toGraph ω).end ∧ Subsingleton (toGraph ω).end

/-- Finite-coordinate cylinders in the actual unordered edge indicator space. -/
def cylinder (F : Finset LatticeEdge) (p : F → Bool) : Set EdgeField :=
  {ω | F.restrict ω = p}

theorem isClopen_cylinder (F : Finset LatticeEdge) (p : F → Bool) :
    IsClopen (cylinder F p) := by
  have hf : Continuous (F.restrict : EdgeField → F → Bool) :=
    continuous_pi (fun e => continuous_apply e.val)
  exact (isClopen_discrete {p}).preimage hf

theorem measurableSet_cylinder (F : Finset LatticeEdge) (p : F → Bool) :
    MeasurableSet (cylinder F p) := (isClopen_cylinder F p).isClosed.measurableSet

end FiniteAvalanches.Trees.Lattice
