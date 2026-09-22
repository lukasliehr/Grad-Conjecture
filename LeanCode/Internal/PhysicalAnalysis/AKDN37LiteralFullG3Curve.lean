import AKDN36LiteralDividedSourceCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.AnnularWeightedSmoothness Grad.AnnularSmoothCore Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.ExhaustionSourceAllocation
open Grad.AnnularStrongData

/-- The actual G3 row transport changes only its physical row witness. -/
theorem actualOriginalG3RadialCurves_formula (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (power : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    (actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat).curve power radius =
      (actualFullG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat (by norm_num : 3≤6)).curve power radius := by
  let first := actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat
  let second := actualFullG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat (by norm_num : 3≤6)
  have same : ∀ᵐ point ∂volume.restrict (Icc lower 1), ∀ mode,
      originalRowCoefficient parameters 0 lower
        (originalAngularDecode lower (actualOriginalG3Row parameters length rho epsilon field small lower positive bounded.le 0 source)) point mode =
      originalRowCoefficient parameters 0 lower
        (fullG3Row (power := 0) parameters length rho epsilon field small lower positive bounded.le (by norm_num : 3≤6)
          (quotientEta parameters 6 source)) point mode := by
    rw [(actualOriginalG3Row_decode parameters length rho epsilon field small lower positive bounded.le 0 source).1]
    have inputs := originalFlatSource_division_inputs parameters (by norm_num : 3≤6) source flat
    filter_upwards [g3Rows_actual_coefficients parameters length rho epsilon field small
        (by norm_num : 0+4≤6) lower positive bounded.le (quotientEta parameters 6 source) inputs.1 inputs.2,
      fullG3Row_actual_coefficient parameters length rho epsilon field small (by norm_num : 3≤6)
        (quotientEta parameters 6 source) (power := 0) (by norm_num) lower positive bounded.le inputs.1 inputs.2,
      ae_restrict_mem measurableSet_Icc] with point value full member
    intro mode
    exact (value member mode).1.trans (full member mode).symm
  apply collarCurve_eq_of_ae lower bounded (first.curve power) (second.curve power)
    (first.smooth power).continuousOn (second.smooth power).continuousOn ?_ inside
  filter_upwards [first.same power,second.same power,same] with point firstSame secondSame rows
  apply lp.ext
  funext mode
  rw [firstSame mode,secondSame mode,rows mode]

/-- Literal full source formula before cancelling the radial division. -/
theorem actualFullG3RadialCurves_formula {grade : ℕ}
    (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (large : 3≤grade)
    (power : ℕ) (radius : ℝ) :
    let divided := fun component => (actualDividedSourceRadialCurves parameters length lower positive bounded large source flat component).curve power radius
    let action := fun component => radialConjugatedAction parameters lower positive bounded.le
      (actualSourceKappaKernel parameters length rho epsilon field small component) power 0 radius
    (actualFullG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat large).curve power radius =
      (length : ℂ)⁻¹ • cartesianWeightedRadialCurve parameters lower positive bounded (source 2) power 0 radius+
        hilbertMeanFree parameters (((action 0 (divided 0)+action 1 (divided 1))-action 2 (divided 2))-divided 1) := by
  dsimp only
  change (length : ℂ)⁻¹ • (actualRestrictedCoreRadialCurves (grade := grade) parameters lower positive bounded (source 2)).curve power radius+_ = _
  rw [actualRestrictedCoreRadialCurves_formula]
  rfl

end Grad.OriginalCartesianTameEstimate
