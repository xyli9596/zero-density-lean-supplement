import V10.AffineScalarZeroCount
import V10.AnalyticZeroMeasure
import V10.AnalyticZeroMeasureCompact
import V10.AnalyticZeroMeasureCount
import V10.AtomicCountIntegral
import V10.BoundedCoefficientZeroCount
import V10.CoefficientIntegralZeroBound
import V10.CoefficientWeight
import V10.CompactLipschitzLimit
import V10.CompanionObservation
import V10.CompanionRoots
import V10.CompanionScalarWindow
import V10.CompanionShortFlow
import V10.ContinuousFrequency
import V10.ContinuousMeasureTests
import V10.CountingStability
import V10.CriticalDirections
import V10.DomainDivisorCount
import V10.ERealPlurisubharmonic
import V10.ExceptionalCone
import V10.ExponentialScales
import V10.ExponentialType
import V10.ExposedFrequencyVertices
import V10.ExteriorSectorCount
import V10.FixedBranchCoefficients
import V10.GaussianProfile
import V10.GenericCoefficientZeroBound
import V10.GlobalFrequencies
import V10.HarmonicL1Compactness
import V10.HarmonicWeakLaplacian
import V10.HingeLaplacian
import V10.HolomorphicProjectionAverage
import V10.HolomorphicProjectionSeries
import V10.HomogeneousSubharmonicConvex
import V10.LocalPortmanteau
import V10.LocalRootSupport
import V10.LocalSupportFace
import V10.LogHomogeneousPluriSeries
import V10.LogHomogeneousSeries
import V10.LogLaplacian
import V10.LogLaplacianLocal
import V10.LogPoincareLelong
import V10.PeriodicVanishing
import V10.PerronConclusion
import V10.PerronDichotomy
import V10.PerronDichotomyBasis
import V10.PerronDichotomyCoordinates
import V10.PerronGeneral
import V10.PerronLogLipschitz
import V10.PerronNonvanishing
import V10.PerronRadial
import V10.PerronSector
import V10.PerronSlowRates
import V10.PerronSlowSubspace
import V10.PerronSpectral
import V10.PerronSpectralAdapted
import V10.PerronSpectralEnergy
import V10.PerronSpectralJordan
import V10.PerronStableDimension
import V10.PerronStableFlow
import V10.PerronStableFlowConverse
import V10.PerronStableFlowGlobal
import V10.PerronStableFlowODE
import V10.PerronStableFlowUniqueness
import V10.PerronStableSpace
import V10.PerronStableSubspace
import V10.PerronStableSubspaceCoordinates
import V10.PerronStableSubspaceForcing
import V10.PerronStableSubspaceGraph
import V10.PerronStableSubspaceJordan
import V10.PerronStableSubspaceMultiplicity
import V10.PerronStableSubspaceOperator
import V10.PerronStableTail
import V10.PerronStableTrajectory
import V10.PerronVectorLimit
import V10.PerronVectorSubharmonic
import V10.PerturbationGrowth
import V10.PerturbationSectorDecay
import V10.PerturbationWeight
import V10.PerturbationZeroBound
import V10.PluriPotentialIntegral
import V10.PluriPotentialSeries
import V10.PolygonEdgeNormals
import V10.PolygonRayLocalization
import V10.PolygonSupportLaplacian
import V10.ProjectionAffineWindow
import V10.ProjectionAverageDeficit
import V10.ProjectionDeficitGaussian
import V10.ProjectionExceptionalCone
import V10.ProjectionGaussian
import V10.ProjectionGaussianFamily
import V10.ProjectionGaussianLoss
import V10.ProjectionGaussianReal
import V10.ProjectionGaussianSupport
import V10.ProjectionLemma43
import V10.ProjectionPhysicalWindows
import V10.ProjectionPlurisubharmonic
import V10.ProjectionRowFamily
import V10.ProjectionSampledPhysicalWindows
import V10.ProjectionSeries
import V10.ProjectionWindowCompactLoss
import V10.ProjectionWindowLoss
import V10.ProjectionWindowPotential
import V10.ProjectionWindowSubsequence
import V10.ProjectionWindowTransport
import V10.ProjectionWindowWeights
import V10.RadialCutoffGeometry
import V10.RadialTransfer
import V10.RayMeasureGeometry
import V10.RotatedHingeLaplacian
import V10.SamplingScale
import V10.ScalarAnalytic
import V10.ScalarCauchyNoncollapse
import V10.ScalarCoefficientLimits
import V10.ScalarCompactnessActual
import V10.ScalarCompactnessAssembly
import V10.ScalarCompactnessDivisor
import V10.ScalarCompactnessInputs
import V10.ScalarCompactnessJensen
import V10.ScalarCompactnessL1Bounds
import V10.ScalarCompactnessLogPotential
import V10.ScalarCompactnessMovingCenter
import V10.ScalarCompactnessRemainder
import V10.ScalarCompanionODE
import V10.ScalarIndicator
import V10.ScalarIndicatorLimit
import V10.ScalarL1Convergence
import V10.ScalarL1GlobalLimit
import V10.ScalarL1Hartogs
import V10.ScalarL1Identification
import V10.ScalarL1IdentificationAverage
import V10.ScalarL1LocalLimit
import V10.ScalarL1LocalToGlobal
import V10.ScalarLocalRootSelection
import V10.ScalarLogSubmean
import V10.ScalarPolygonIndicator
import V10.ScalarSectorCounting
import V10.ScalarWeakLaplacian
import V10.ScalarZeroMeasureCompact
import V10.ScalarZeroMeasureLimit
import V10.ScalarZeroMeasureSets
import V10.ScaledDivisorCount
import V10.SectorScalarCount
import V10.SectorScaledNeighborhood
import V10.SelectedVertices
import V10.ShrinkingTubes
import V10.SmoothMeasureMass
import V10.SmoothTestApproximation
import V10.SmoothTestLocalization
import V10.SubharmonicHartogs
import V10.SubharmonicLimit
import V10.SubharmonicLocal
import V10.UnitDiskWeightBound
import V10.ZeroMeasureTestConvergence
import ZeroDensity.Audit
import Lean.Util.CollectAxioms

/-! Kernel dependency audit of all proved project declarations.
No claim is made that an unproved target definition is a theorem.
-/
open Lean Elab Command

run_cmd do
  let env <- getEnv
  let mut legacy : Nat := 0
  let mut added : Nat := 0
  for (name, info) in env.constants.toList do
    if (`ZeroDensity).isPrefixOf name || (`V10).isPrefixOf name then
      match info with
      | .thmInfo _ =>
        let axioms <- collectAxioms name
        for ax in axioms do
          unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
            throwError "Forbidden axiom {ax} in {name}"
        if (`V10).isPrefixOf name then
          added := added + 1
        else
          legacy := legacy + 1
      | _ => pure ()
  logInfo m!"PROJECT_AXIOM_AUDIT legacy={legacy} v10={added}: only propext, Classical.choice, Quot.sound."

#print axioms V10.FixedBranchCoefficients.lemma_2_1
#print axioms V10.DomainDivisorCount.radial_transfer_open_domain
#print axioms V10.ContinuousFrequency.compact_frequency_analytic_input
#print axioms V10.GaussianProfile.map_source_eq_product
#print axioms V10.PeriodicVanishing.residueFiniteSpace_eq_integer
#print axioms V10.ShrinkingTubes.exists_shrinking_tube_littleO
#print axioms V10.SamplingScale.summable_reciprocal_phaseScale
#print axioms V10.SelectedVertices.conjugate_selected_are_exact_vertices

#print axioms V10.PerronGeneral.perron_growth_exponent

#print axioms V10.PerronSector.lemma_2_2

#print axioms V10.PerronSlowSubspace.lemma_3_6

#print axioms V10.PerronSlowSubspace.lemma_3_6_initial_values

#print axioms V10.SubharmonicHartogs.analytic_norm_compact_upper

#print axioms V10.PerronVectorSubharmonic.actual_indicator_subharmonic

#print axioms V10.ScalarIndicatorLimit.lemma_3_2
#print axioms V10.ScalarLocalRootSelection.lemma_3_3
#print axioms V10.LogPoincareLelong.analytic_log_laplacian
#print axioms V10.ProjectionGaussianLoss.integral_abs_normalized_log

#print axioms V10.ExposedFrequencyVertices.corollary_3_8

#print axioms V10.ScalarZeroMeasureCompact.sector_scalar_zero_measure_tendsto_test

#print axioms V10.HolomorphicProjectionSeries.constructed_potential

#print axioms V10.ContinuousMeasureTests.continuous_test_tendsto_of_smooth

#print axioms V10.ProjectionAffineWindow.averagedLogProjection_window_smul

#print axioms V10.ScalarSectorCounting.proposition_3_1
#print axioms V10.ScalarSectorCounting.proposition_3_1_littleO
#print axioms V10.PolygonSupportLaplacian.polygon_support_laplacian
#print axioms V10.CoefficientIntegralZeroBound.lemma_4_1
#print axioms V10.GenericCoefficientZeroBound.exists_uniform_zero_bounds
#print axioms V10.ProjectionLemma43.lemma_4_3
#print axioms V10.ProjectionSampledPhysicalWindows.sampled_physical_window_projection
#print axioms V10.PerturbationGrowth.finite_family_growth
#print axioms V10.PerturbationWeight.disk_mass_littleO
#print axioms V10.PerturbationZeroBound.perturbed_integral_zero_bound
#print axioms V10.PerturbationSectorDecay.finite_family_sector_decay
#print axioms V10.PerturbationSectorDecay.normalized_tendsto_zero
