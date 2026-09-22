import AKAO32LiteralSameCorrectedP
import SCS44OriginalSourceConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualOriginalThirdSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarBulk Grad.SourceCollarRestriction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarFlux Grad.BoundaryTrace Grad.SourceCollar
open Grad.AnnularGeneralSourceRegularity Grad.AnnularCurrentLow Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularStrongOrbit Grad.AnnularSourceGraph Grad.AnnularForwardDatum Grad.AnnularRestriction
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryLift

theorem corePolarValue_polar_shift {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (polar axial : ℝ) :
    corePolarValue parameters field radius nonnegative bounded (polar+2*Real.pi,axial) =
      corePolarValue parameters field radius nonnegative bounded (polar,axial) := by
  exact congrArg (fun point => sourceCoreValue field point axial)
    (divisionPolarPoint_periodic radius nonnegative bounded polar)

theorem corePolarValue_axial_shift {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (polar axial : ℝ) :
    corePolarValue parameters field radius nonnegative bounded (polar,axial+2*Real.pi) =
      corePolarValue parameters field radius nonnegative bounded (polar,axial) := by
  simp only [corePolarValue,sourceCoreValue_eq_originalPhysicalEvaluationLift]
  change (originalPhysicalClosedJet parameters field).value (_,((axial+2*Real.pi : ℝ) : CellCircle)) =
    (originalPhysicalClosedJet parameters field).value (_,(axial : CellCircle))
  rw [AddCircle.coe_add_period]

theorem removePolarMean_periodic {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (polar : ∀ axial,Function.Periodic (fun angle => field (angle,axial)) (2*Real.pi))
    (axial : ∀ angle,Function.Periodic (fun coordinate => field (angle,coordinate)) (2*Real.pi)) :
    (∀ coordinate,Function.Periodic (fun angle => removePolarMean field (angle,coordinate)) (2*Real.pi)) ∧
    (∀ angle,Function.Periodic (fun coordinate => removePolarMean field (angle,coordinate)) (2*Real.pi)) := by
  constructor
  · intro coordinate angle
    simp only [removePolarMean,polar coordinate angle]
  · intro angle coordinate
    simp only [removePolarMean,axial angle coordinate,funext (fun theta => axial theta coordinate)]

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (source : SmoothQuotient parameters) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)

include small in
theorem physicalKappaDeviation_axial_shift (component : Fin 3) (polar axial : ℝ) :
    physicalKappaDeviation parameters length epsilon field radius nonnegative bounded component (polar,axial+2*Real.pi) =
      physicalKappaDeviation parameters length epsilon field radius nonnegative bounded component (polar,axial) := by
  rw [physicalKappaDeviation_eq_tsum parameters length rho epsilon field small,
    physicalKappaDeviation_eq_tsum parameters length rho epsilon field small]
  apply tsum_congr
  intro mode
  simp only [← cellCharacter_coe,AddCircle.coe_add_period]

theorem physicalDividedSources_axial_shift (component : Fin 3) (polar axial : ℝ) :
    physicalDividedSources parameters length source radius nonnegative bounded component (polar,axial+2*Real.pi) =
      physicalDividedSources parameters length source radius nonnegative bounded component (polar,axial) := by
  fin_cases component <;> simp [physicalDividedSources,
    corePolarValue_axial_shift parameters _ radius nonnegative bounded polar axial]

include small in
theorem physicalCorrection_axial_periodic (polar : ℝ) :
    Function.Periodic (fun axial => physicalCorrection parameters length epsilon field source radius nonnegative bounded (polar,axial)) (2*Real.pi) := by
  intro axial
  simp only [physicalCorrection,physicalKappaDeviation_axial_shift parameters length rho epsilon field small radius nonnegative bounded,
    physicalDividedSources_axial_shift parameters length source radius nonnegative bounded]

include small in
/-- Both original integer Fourier circles of the literal full G3 are retained. -/
theorem physicalG3_periodic :
    (∀ axial,Function.Periodic (fun polar => physicalG3 parameters length epsilon field source radius nonnegative bounded (polar,axial)) (2*Real.pi)) ∧
    (∀ polar,Function.Periodic (fun axial => physicalG3 parameters length epsilon field source radius nonnegative bounded (polar,axial)) (2*Real.pi)) := by
  have projected := removePolarMean_periodic
    (physicalCorrection parameters length epsilon field source radius nonnegative bounded)
    (physicalCorrection_polar_periodic parameters length rho epsilon field small source radius nonnegative bounded)
    (physicalCorrection_axial_periodic parameters length rho epsilon field small source radius nonnegative bounded)
  constructor
  · intro axial polar
    simp only [physicalG3,corePolarValue_polar_shift parameters _ radius nonnegative bounded polar axial,projected.1 axial polar]
  · intro polar axial
    simp only [physicalG3,corePolarValue_axial_shift parameters _ radius nonnegative bounded polar axial,projected.2 polar axial]

end Grad.ActualOriginalThirdSource
