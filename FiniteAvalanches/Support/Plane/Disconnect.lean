import Mathlib.Topology.Path
import Mathlib.Analysis.Complex.Basic

/-!
# Separation by paths

Ported from Lattice-Probability `LatticeProb/Bonanno/LQGMetric/Topo/Disconnect.lean`
at commit `ba2b67f3`, adapted there from Leonardo Bonanno’s `lean-formalizations` at
commit `31e7483`.
-/

namespace LQGMetric

open Set

/-- Every path between the two sets meets the separating set. -/
def Disconnects (X E F : Set ℂ) : Prop :=
  ∀ (x y : ℂ) (γ : Path x y), x ∈ E → y ∈ F → (range γ ∩ X).Nonempty

end LQGMetric
