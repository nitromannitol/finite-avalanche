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
  "8557b91360e23d51d779a05d8313974b403658b2"

@[default_target]
lean_lib FiniteAvalanches where
  globs := #[.andSubmodules `FiniteAvalanches]

@[default_target]
lean_lib ActualS7Consumer where
  globs := #[
    .one `ActualS7Consumer
  ]

@[default_target]
lean_lib Checks where
  globs := #[
    .one `Checks.AdditiveApplications
  ]

@[default_target]
lean_lib CurrentMain where
  globs := #[
    .one `CurrentMain.Limsup
  ]

@[default_target]
lean_lib CurrentMean where
  globs := #[
    .one `CurrentMean.GuardedAveraging,
    .one `CurrentMean.Supplier
  ]

@[default_target]
lean_lib CurrentOriginalBoundary where
  globs := #[
    .one `CurrentOriginalBoundary
  ]

@[default_target]
lean_lib CurrentRegisteredPast where
  globs := #[
    .one `CurrentRegisteredPast.FullFiniteLimsupReduction,
    .one `CurrentRegisteredPast.FullIntegerMainConsumer,
    .one `CurrentRegisteredPast.MainApplications,
    .one `CurrentRegisteredPast.MeanMain,
    .one `CurrentRegisteredPast.Origin
  ]

@[default_target]
lean_lib CurrentRootConsumers where
  globs := #[
    .one `CurrentRootConsumers.PastTail
  ]

@[default_target]
lean_lib CurrentS7LovaszApplication where
  globs := #[
    .one `CurrentS7LovaszApplication
  ]

@[default_target]
lean_lib CurrentSource where
  globs := #[
    .one `CurrentSource.CornerCharging,
    .one `CurrentSource.CurrentSplitAssembly,
    .one `CurrentSource.FullIntegerLaw,
    .one `CurrentSource.FullIntegerRadius,
    .one `CurrentSource.GaugedMinimumSquares,
    .one `CurrentSource.HeightGauge,
    .one `CurrentSource.HeightGreen,
    .one `CurrentSource.MinimumCornerTransfer,
    .one `CurrentSource.MinimumFaceCorners,
    .one `CurrentSource.MinimumTrialCharacterization,
    .one `CurrentSource.OriginalBalanceLovasz,
    .one `CurrentSource.PhysicalHeightCanonical,
    .one `CurrentSource.PhysicalTerminalHeight,
    .one `CurrentSource.RawFullRadius,
    .one `CurrentSource.RawFullStabilization,
    .one `CurrentSource.RawSourceLaw,
    .one `CurrentSource.ReferenceMomentCurrent,
    .one `CurrentSource.RegularCornerTransfer,
    .one `CurrentSource.SharpCornerPhysical,
    .one `CurrentSource.SignedMinimumSquares,
    .one `CurrentSource.SplitCurrentScalar,
    .one `CurrentSource.SplitWeightedEnergy,
    .one `CurrentSource.TerminalCornerPlacement,
    .one `CurrentSource.TerminalCorners,
    .one `CurrentSource.WholeMinimumTrial
  ]

@[default_target]
lean_lib DualCurrentIntegration where
  globs := #[
    .one `DualCurrentIntegration
  ]

@[default_target]
lean_lib FiniteAvalanchesCurrent where
  globs := #[
    .one `FiniteAvalanchesCurrent.ArcMomentExpectations,
    .one `FiniteAvalanchesCurrent.SplitEstimateExpectations,
    .one `FiniteAvalanchesCurrent.BoundaryMeanApplication,
    .one `FiniteAvalanchesCurrent.ArcMomentV7,
    .one `FiniteAvalanchesCurrent.ForestReciprocalV5,
    .one `FiniteAvalanchesCurrent.GlobalMonotonicity,
    .one `FiniteAvalanchesCurrent.HeldBurningV1,
    .one `FiniteAvalanchesCurrent.InverseWavesV1,
    .one `FiniteAvalanchesCurrent.OutflowV1,
    .one `FiniteAvalanchesCurrent.RegisteredPast.Consumers.Main,
    .one `FiniteAvalanchesCurrent.RegisteredPast.Consumers.Reduction,
    .one `FiniteAvalanchesCurrent.RegisteredPast.Main,
    .one `FiniteAvalanchesCurrent.RegisteredPast.Reduction,
    .one `FiniteAvalanchesCurrent.SplitEstimateV1
  ]

@[default_target]
lean_lib FiniteAvalanchesCurrentRegisteredPastSelectedMain where
  globs := #[
    .one `FiniteAvalanchesCurrentRegisteredPastSelectedMain
  ]

@[default_target]
lean_lib FiniteAvalanchesFrozen where
  globs := #[
    .one `FiniteAvalanchesFrozen.NeedlePathV5
  ]

@[default_target]
lean_lib FiniteAvalanchesProofs where
  globs := #[
    .one `FiniteAvalanchesProofs.NeedlePathV5
  ]

@[default_target]
lean_lib LovaszQuarterTurn where
  globs := #[
    .one `LovaszQuarterTurn
  ]

@[default_target]
lean_lib OriginalGreenNormalization where
  globs := #[
    .one `OriginalGreenNormalization
  ]

@[default_target]
lean_lib OriginalGreenSquares where
  globs := #[
    .one `OriginalGreenSquares
  ]

@[default_target]
lean_lib OriginalGreenTiling where
  globs := #[
    .one `OriginalGreenTiling
  ]

@[default_target]
lean_lib OriginalStreamApplication where
  globs := #[
    .one `OriginalStreamApplication
  ]

@[default_target]
lean_lib OriginalStreamExistence where
  globs := #[
    .one `OriginalStreamExistence
  ]

@[default_target]
lean_lib PhysicalStreamCuts where
  globs := #[
    .one `PhysicalStreamCuts
  ]

@[default_target]
lean_lib PhysicalStreamExistence where
  globs := #[
    .one `PhysicalStreamExistence
  ]

@[default_target]
lean_lib PhysicalVoltageCuts where
  globs := #[
    .one `PhysicalVoltageCuts
  ]

@[default_target]
lean_lib PrimitiveHeightGreen where
  globs := #[
    .one `PrimitiveHeightGreen
  ]

@[default_target]
lean_lib PrimitiveLovaszSquareCoordinates where
  globs := #[
    .one `PrimitiveLovaszSquareCoordinates
  ]

@[default_target]
lean_lib TreeFlowIntegration where
  globs := #[
    .one `TreeFlowIntegration
  ]

lean_lib PublicVerification where
  globs := #[.one `PublicVerification.Axioms]

lean_lib FiniteAvalanchesAudit where
  globs := #[.one `FiniteAvalanchesAudit.MainOrigin.Challenge, .one `FiniteAvalanchesAudit.MainOrigin.Solution]
