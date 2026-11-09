import ZeroDensity.Perron
import ZeroDensity.ScalarLimit
import ZeroDensity.SectorCount
import ZeroDensity.RadiusComparison
import ZeroDensity.CountingTransfer
import ZeroDensity.ConformalMultiplicity
import ZeroDensity.CandidateFamily
import ZeroDensity.SectorBounds
import ZeroDensity.ConvergenceExponent
import ZeroDensity.Statement
import ZeroDensity.CoefficientData
import ZeroDensity.MaximalCoefficientData
import ZeroDensity.ScaledEquation
import ZeroDensity.ExactChange
import ZeroDensity.PhaseCoefficientLimits
import ZeroDensity.PhaseDerivativeBounds
import ZeroDensity.FrequencyDecay
import ZeroDensity.PolynomialLimits
import ZeroDensity.NormalizedCoefficientLimits
import ZeroDensity.LocalRootSelection
import ZeroDensity.ConvexSelection
import ZeroDensity.CharacteristicEquation
import ZeroDensity.InverseGeometry
import ZeroDensity.SectorGeometry
import ZeroDensity.SectorDivisorCount
import ZeroDensity.SupportingGeometry
import ZeroDensity.MainTheorem
import ZeroDensity.BranchCoefficientLimits
import ZeroDensity.PolygonFaces
import ZeroDensity.AngularFaceJumps
import ZeroDensity.PerronEstimates
import ZeroDensity.PerronPerturbation
import ZeroDensity.LogZeroGerm
import ZeroDensity.L1TestPairing
import ZeroDensity.PlanarLogIntegrability
import ZeroDensity.AnalyticLogIntegrability
import ZeroDensity.LogKernelBoundary
import ZeroDensity.InverseBranchFoundations
import ZeroDensity.PrimitiveIntegrationByParts
import ZeroDensity.SectorLogarithm
import ZeroDensity.ZeroBetaInverse
import ZeroDensity.PhasePrimitiveRemainder
import ZeroDensity.LogarithmicInversion
import ZeroDensity.PositiveBetaInverse
import ZeroDensity.PhaseInverse
import Lean.Util.CollectAxioms

/-! Audit every proved declaration in the extension, including imported
dependencies. Passing this audit does not prove the unproved target proposition. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`ZeroDensity).isPrefixOf name then
      match info with
      | .thmInfo _ =>
        let axioms ← collectAxioms name
        for ax in axioms do
          unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
            throwError "Forbidden axiom {ax} in {name}"
        checked := checked + 1
      | _ => pure ()
  logInfo m!"Audited {checked} proved ZeroDensity declarations; only standard axioms."

#check ZeroDensity.Statement.Theorem11Target
#check ZeroDensity.MainTheorem.Theorem31Target
#print axioms ZeroDensity.NormalizedCoefficientLimits.phaseCoefficient_actual_uniform
#print axioms ZeroDensity.BranchCoefficientLimits.branch_coefficient_analytic
#print axioms ZeroDensity.BranchCoefficientLimits.branch_coefficient_uniform
#print axioms ZeroDensity.SectorGeometry.closure_sector_subset
#print axioms ZeroDensity.SectorDivisorCount.phaseCount_inner_split
#print axioms ZeroDensity.Statement.corollary_1_2_from_counting_law
#print axioms ZeroDensity.CountingTransfer.transferred_main_law
#print axioms ZeroDensity.ConvergenceExponent.infiniteExponent_of_positive_exp_count

#print axioms ZeroDensity.AngularFaceJumps.derivative_jump_eq_faceLength
#print axioms ZeroDensity.ZeroBetaInverse.inverse_uniform_closed
#print axioms ZeroDensity.AnalyticLogIntegrability.locallyIntegrableOn_log_norm
#print axioms ZeroDensity.L1TestPairing.weakLaplacianPairing_tendsto_on_compact
#print axioms ZeroDensity.LogKernelBoundary.inverse_circle_charge

#print axioms ZeroDensity.PhasePrimitiveRemainder.primitive_ratio_limit
#print axioms ZeroDensity.PositiveBetaInverse.tail_log_equation
#print axioms ZeroDensity.PositiveBetaInverse.inverse_uniform_closed
#print axioms ZeroDensity.PhaseInverse.inverse_radius_uniform_closed
#print axioms ZeroDensity.BranchCoefficientLimits.branch_coefficient_actual_uniform
