/-
Copied from Leonardo Bonanno's lean-formalizations
(https://github.com/leobon12/lean-formalizations), module
`LQGMetric/Topo/Disconnect.lean`, commit 31e748330ee154d5f41537c4b01f71b8a5510c2d.
Changes: only the definition `Disconnects` is copied; the rest of the module
(`ContMetric.aroundDist` and the `Disconnects` lemmas) is omitted, the imports are reduced
to the two it needs, the two `set_option` lines (this project sets both options in its
lakefile) are removed, and `open Set Metric` becomes `open Set`; the module docstring and
the docstring of `Disconnects` are rewritten.
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
