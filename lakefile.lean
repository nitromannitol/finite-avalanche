import Lake
open Lake DSL

package finiteAvalanches where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability" @
  "30752e06f26692a2a44bcbf629db9d8d187c5e68"

@[default_target]
lean_lib FiniteAvalanches where
  globs := #[.andSubmodules `FiniteAvalanches]

@[default_target]
lean_lib FiniteAvalanchesFrozen where
  globs := #[
    .one `FiniteAvalanchesFrozen.ElectricalArcMomentV6,
    .one `FiniteAvalanchesFrozen.ElectricalPairContactV2,
    .one `FiniteAvalanchesFrozen.ElectricalReferenceMomentV4,
    .one `FiniteAvalanchesFrozen.ElectricalSplitEstimateV2,
    .one `FiniteAvalanchesFrozen.ForestReciprocalCofiniteV4,
    .one `FiniteAvalanchesFrozen.JointCofiniteV4,
    .one `FiniteAvalanchesFrozen.MainOriginV3,
    .one `FiniteAvalanchesFrozen.Needle107V4,
    .one `FiniteAvalanchesFrozen.TreeContinuity
  ]

@[default_target]
lean_lib FiniteAvalanchesProofs where
  globs := #[.submodules `FiniteAvalanchesProofs]

-- Comparator modules are explicit targets and remain outside production defaults.
lean_lib FiniteAvalanchesAudit where
  globs := #[
    .one `FiniteAvalanchesAudit.MainOrigin.Challenge,
    .one `FiniteAvalanchesAudit.MainOrigin.Solution
  ]
