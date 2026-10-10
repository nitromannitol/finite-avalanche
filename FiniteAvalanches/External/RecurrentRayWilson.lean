import FiniteAvalanches.Wilson.Lattice.RaySeeded

set_option autoImplicit false
open LatticeProb MeasureTheory
open scoped Classical
namespace FiniteAvalanches.External
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice
open TreeMeasurability11 FiniteAvalanches.Wilson.Lattice.RaySeeded
attribute [local instance] rayMeasurableSpace

/-- Recurrent ray-seeded Wilson sampling: the generic square-lattice corollary of
van Engelenburg–Hutchcroft, arXiv:2301.03875v1, §2.5 Lemma10, printed pp14–15,
using Lemma5 (pp9–10) and the registered actual UST one-ended support.
The seed has its actual UST-ray marginal independently of ordinary Wilson rows.
The one joint witness retains the literal seed-edge/branch-edge completion and
has the actual full seed/tree law. No manuscript conditional-contact identity,
finite marked set, moment estimate or numerical conclusion is trusted. -/
axiom square_lattice_ray_seeded_wilson :
∀ (o : Site 2) (order : ℕ → Site 2), Function.Surjective order →
  ∃ ν : ProbabilityMeasure ((SimpleRay × Rows) × EdgeField),
    (ν : Measure ((SimpleRay × Rows) × EdgeField)).map Prod.fst =
      (rayLaw o).prod wilsonRows ∧
    (∀ᵐ p ∂(ν : Measure ((SimpleRay × Rows) × EdgeField)),
      Completes p.1.1 order p.1.2 p.2) ∧
    (ν : Measure ((SimpleRay × Rows) × EdgeField)).map (fun p => (p.1.1, p.2)) =
      endedUST.map (fun T => (seed o T, T.val))

end FiniteAvalanches.External
