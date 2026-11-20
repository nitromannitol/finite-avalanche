/-
Copied from Leonardo Bonanno's lean-formalizations
(https://github.com/leobon12/lean-formalizations), module
`LQGMetric/Topo/Disconnect.lean`, commit 31e748330ee154d5f41537c4b01f71b8a5510c2d.
Changes: only the definition `Disconnects` is copied, with the imports it
needs; comments rewritten.
-/
import Mathlib.Topology.Path
import Mathlib.Analysis.Complex.Basic

/-!
# Separation by paths
-/

namespace LQGMetric

open Set

/-- Every path between the two sets meets the separating set. -/
def Disconnects (X E F : Set ℂ) : Prop :=
  ∀ (x y : ℂ) (γ : Path x y), x ∈ E → y ∈ F → (range γ ∩ X).Nonempty

end LQGMetric
