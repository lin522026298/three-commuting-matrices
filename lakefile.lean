import Lake
open Lake DSL

package gerstenhaber

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "07977d2921637684e9ecdf70fc1927570233637d"

lean_lib Challenge

lean_lib Solution

lean_lib G3Development where
  srcDir := "src"
  roots := #[
    `ActorIndex, `ActualBadTransfer, `ActualClosedJet, `ActualEnds,
    `ActualMinimalEnds, `ActualPairParameters, `ActualSixJet, `AffineNormalization,
    `AffinePoleResidue, `AnyMinors, `BlockIndex, `BoxWords,
    `CharZeroMatrices, `ConcretePole, `ConjugateActor, `CoordinateChart,
    `DVRJetTransfer, `DVRMinors, `DVRScalar, `DescendedWords,
    `DividedTail, `EndCoordinateCriterion, `ExactJet, `FiniteList,
    `FullG3, `GKGraphActor, `GKGraphCoordinates, `GKGraphCore,
    `GKGraphDimension, `GKGraphIntegral, `GKGraphInversePoint, `GKGraphMinor,
    `GKGraphOpen, `GKGraphShifted, `GKGraphSpecialize, `GKGraphTransport,
    `GKRationalAdjunction, `GKRationalResidual, `GaugeParameters, `Gerstenhaber,
    `GraphLifts, `GraphToFamily, `GroundLength, `HeadPresentation,
    `HeightContract, `HypersurfaceTrdeg, `InitialMinimum, `IntrinsicDVR,
    `JetBaseChange, `JetCoefficient, `JetOrder, `JordanActualMatrix,
    `JordanBudget, `JordanDimension, `JordanGroupSites, `JordanGroupedModel,
    `JordanKernel, `JordanLiteralParameters, `JordanLower, `JordanMatrix,
    `JordanMultiplicity, `JordanNilTest, `JordanOrbitCore, `JordanPID,
    `JordanPrimitive, `JordanStrings, `JordanTrueNullity, `LeastPresentedEnds,
    `LocalJetIso, `MatrixGauge, `MatrixOfLinearModel, `MinimalCover,
    `MinimalPrimary, `NativePoleEnds, `NativeSeries, `NilOperator,
    `OrbitGauge, `OriginAction, `OriginActor, `OriginalGraph,
    `OriginalPole, `PairFromModels, `PairOrbit, `PoleCenter,
    `PoleClosedJets, `PoleCoordinates, `PoleGlobalWitness, `PoleJets,
    `PolePrime, `PolynomialPowerJet, `PrecisionRepair, `PresentedWidth,
    `RationalGauge, `RealCenters, `RegularEnds, `ResidueDimension,
    `ScalarMatrixActor, `SourceEndFrames, `SquareCover, `StrictEndCoordinates,
    `TripleFamily, `TrueGraphPole, `TrueMinorTransfer, `WitnessBudget
  ]
