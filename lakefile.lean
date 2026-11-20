import Lake
open Lake DSL

package gerstenhaber

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "07977d2921637684e9ecdf70fc1927570233637d"

lean_lib Challenge

@[default_target] lean_lib Solution

lean_lib G3Development where
  srcDir := "src"
  roots := #[
    `ActorIndex, `ActualBadTransfer, `ActualClosedJet,
    `ActualEnds, `ActualMinimalEnds, `ActualPairParameters,
    `ActualSixJet, `AffineNormalization, `AffinePoleResidue,
    `AnyMinors, `BlockIndex, `BoxWords,
    `CharZeroMatrices, `ConcretePole, `ConjugateActor,
    `CoordinateChart, `DVRJetTransfer, `DVRMinors,
    `DVRScalar, `DescendedWords, `DividedTail,
    `EndCoordinateCriterion, `ExactJet, `FiniteList,
    `FullG3, `GKGraphActor, `GKGraphCoordinates,
    `GKGraphCore, `GKGraphDimension, `GKGraphIntegral,
    `GKGraphInversePoint, `GKGraphMinor, `GKGraphOpen,
    `GKGraphShifted, `GKGraphSpecialize, `GKGraphTransport,
    `GKRationalAdjunction, `GKRationalResidual, `GaugeParameters,
    `Gerstenhaber.CanonicalExtension.FrobeniusIsotropy, `Gerstenhaber.CanonicalExtension.KernelDuality, `Gerstenhaber.CanonicalExtension.ParentDuality,
    `Gerstenhaber.CanonicalExtension.PositiveDual, `Gerstenhaber.DP2.LinearColumn, `Gerstenhaber.DP2.LinearRow.MonicFrobenius,
    `Gerstenhaber.DP2.LinearRow.ProjectiveSyzygy, `Gerstenhaber.DP2.LinearRow.RelativeDuality, `Gerstenhaber.DP2.PrimitiveColumn,
    `Gerstenhaber.DP2.UnitNormal, `Gerstenhaber.FourBlocks.HeadBounds.HeadModule, `Gerstenhaber.FourBlocks.LiteralFrame,
    `Gerstenhaber.FourBlocks.MinimalSource.ActualBudget, `Gerstenhaber.FourBlocks.MinimalSource.AnnihilatorFibers, `Gerstenhaber.FourBlocks.MinimalSource.BlockClosure,
    `Gerstenhaber.FourBlocks.MinimalSource.CyclicOperator, `Gerstenhaber.FourBlocks.MinimalSource.CyclicParent, `Gerstenhaber.FourBlocks.MinimalSource.Duality,
    `Gerstenhaber.FourBlocks.MinimalSource.KernelHeadDuality, `Gerstenhaber.FourBlocks.MinimalSource.MaximalCyclic, `Gerstenhaber.FourBlocks.MinimalSource.MinimalCounterexample,
    `Gerstenhaber.FourBlocks.MinimalSource.NilThreeSource, `Gerstenhaber.FourBlocks.MinimalSource.NilpotentAugmentation, `Gerstenhaber.FourBlocks.MinimalSource.NilpotentResidue,
    `Gerstenhaber.FourBlocks.MinimalSource.Pencil, `Gerstenhaber.FourBlocks.MinimalSource.RestrictedBudget, `Gerstenhaber.FourBlocks.MinimalSource.SocleAction,
    `Gerstenhaber.FourBlocks.MinimalSource.SocleTensor, `Gerstenhaber.FourBlocks.MinimalSource.ThreeGeneratorSafety, `Gerstenhaber.FourBlocks.PrimaryDecomposition.Invariant,
    `Gerstenhaber.FourBlocks.PrimaryDecomposition.JointSpaces, `Gerstenhaber.FourBlocks.PrimaryDecomposition.Transfer, `Gerstenhaber.FourBlocks.RankSpecialization,
    `Gerstenhaber.FourBlocks.SmallHeads.RelationError, `Gerstenhaber.IdealQuotient.QuotientIdeal, `GraphLifts,
    `GraphToFamily, `GroundLength, `HeadPresentation,
    `HeightContract, `HypersurfaceTrdeg, `InitialMinimum,
    `IntrinsicDVR, `JetBaseChange, `JetCoefficient,
    `JetOrder, `JordanActualMatrix, `JordanBudget,
    `JordanDimension, `JordanGroupSites, `JordanGroupedModel,
    `JordanKernel, `JordanLiteralParameters, `JordanLower,
    `JordanMatrix, `JordanMultiplicity, `JordanNilTest,
    `JordanOrbitCore, `JordanPID, `JordanPrimitive,
    `JordanStrings, `JordanTrueNullity, `LeastPresentedEnds,
    `LocalJetIso, `MatrixGauge, `MatrixOfLinearModel,
    `MinimalCover, `MinimalPrimary, `NativePoleEnds,
    `NativeSeries, `NilOperator, `OrbitGauge,
    `OriginAction, `OriginActor, `OriginalGraph,
    `OriginalPole, `PairFromModels, `PairOrbit,
    `PoleCenter, `PoleClosedJets, `PoleCoordinates,
    `PoleGlobalWitness, `PoleJets, `PolePrime,
    `PolynomialPowerJet, `PrecisionRepair, `PresentedWidth,
    `RationalGauge, `RealCenters, `RegularEnds,
    `ResidueDimension, `ScalarMatrixActor, `SourceEndFrames,
    `SquareCover, `StrictEndCoordinates, `TripleFamily,
    `TrueGraphPole, `TrueMinorTransfer, `WitnessBudget
  ]
