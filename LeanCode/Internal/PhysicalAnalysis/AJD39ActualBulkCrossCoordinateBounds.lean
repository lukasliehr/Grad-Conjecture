import AJD28ActualCoefficientCoordinateBounds
import AJD30UniformOperatorOperations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy
open Grad.AnnularCrossMaps Grad.AnnularVariational Grad.AnnularLowCompletion

attribute [local instance] crossHighNormed crossHighSeminormed crossHighComplexNormed crossHighComplexModule
  crossHighRealNormed crossHighRealModule
local instance lowHighBulkOperatorNormed (lower L : ℝ) (positive : 0 < lower) :
    NormedAddCommGroup (lowEnergyGraph lower L positive →L[ℂ] AnnularBulk lower) := inferInstance
local instance lowHighBulkOperatorRealNormed (lower L : ℝ) (positive : 0 < lower) :
    NormedSpace ℝ (lowEnergyGraph lower L positive →L[ℂ] AnnularBulk lower) := ContinuousLinearMap.toNormedSpace
local instance highLowBulkOperatorNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedAddCommGroup (CrossHighSpace lower L positive lengthPositive →L[ℂ] LowEnergyBulk lower) := inferInstance
local instance highLowBulkOperatorRealNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CrossHighSpace lower L positive lengthPositive →L[ℂ] LowEnergyBulk lower) := ContinuousLinearMap.toNormedSpace

variable (parameters : PhaseParameters) (L compact : ℝ)

/-- The literal BF16 three high bulk rows, with their original normalized
low input, have genuine pure-coordinate one-high bounds. -/
theorem lowToHighBulkOrbit_uniformCoordinateBound (row : Fin 3) :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        lowToHighBulkOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.lengthPositive context.state row) := by
  have inputBound (context : CoupledCoordinateContext parameters L compact) :
      ‖(lowNormalizedSevenInput parameters context.lower L context.lengthPositive context.positive).comp (lowStoredCoordinate context.lower L context.positive 0)‖ ≤ 7 + 2 * |L| := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro field
    have input := lowNormalizedSevenInput_bound parameters context.lower L context.lengthPositive context.positive (lowStoredCoordinate context.lower L context.positive 0 field)
    have coordinate := lowStoredCoordinate_bound context.lower L context.positive 0 field
    have coefficient : 7 + 2 * L ≤ 7 + 2 * |L| := by linarith [le_abs_self L]
    exact input.trans (mul_le_mul coefficient coordinate (norm_nonneg _) (by positivity))
  have mapped := (actualLowRowOrbit_uniformCoordinateBound parameters L compact row).precomposeComplex
    (fun context => actualLowRowOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state row)
    (fun context => (lowNormalizedSevenInput parameters context.lower L context.lengthPositive context.positive).comp (lowStoredCoordinate context.lower L context.positive 0))
    (7 + 2 * |L|) (by positivity) inputBound
  apply mapped.postcomposeComplex
    (fun context => complexOperatorComposition_contDiff _ _
      (actualLowRowOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state row) contDiff_const)
    (fun context => crossHighRestriction context.lower) 1 (by norm_num)
  intro context
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro field
  exact (crossHighRestrictionValue_bound context.lower field).trans_eq (one_mul _).symm

/-- The literal BF18 low bulk row includes all three normalized physical
outputs and the original W/Domega high input. -/
theorem highToLowBulkOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        highToLowBulkOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.lengthPositive context.state) := by
  have first := (actualLowRowOrbit_uniformCoordinateBound parameters L compact 0).postcomposeComplex
    (fun context => actualLowRowOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 0)
    (fun context => lowFirstOutput parameters context.lower L) (|lowBalanceConstant L parameters.gamma| + 2) (by positivity)
    (fun context => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun field =>
      (lowFirstOutput_bound parameters context.lower L field).trans
        (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (lowBalanceConstant L parameters.gamma)]) (norm_nonneg field))))
  have second := (actualLowRowOrbit_uniformCoordinateBound parameters L compact 1).postcomposeComplex
    (fun context => actualLowRowOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 1)
    (fun context => lowCellOutput context.lower L context.positive) 1 (by norm_num)
    (fun context => ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun field =>
      (lowCellOutput_bound context.lower L context.positive field).trans_eq (one_mul _).symm))
  have third := (actualLowRowOrbit_uniformCoordinateBound parameters L compact 2).postcomposeComplex
    (fun context => actualLowRowOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 2)
    (fun context => lowAngularOutput context.lower L context.positive) 2 (by norm_num)
    (fun context => ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (lowAngularOutput_bound context.lower L context.positive))
  have firstSmooth (context : CoupledCoordinateContext parameters L compact) :
      ContDiff ℝ ∞ (fun tau => (lowFirstOutput parameters context.lower L).comp
        (Grad.AnnularLowOrbit.actualLowRowOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 0 tau)) :=
    complexOperatorComposition_contDiff _ _ contDiff_const
      (actualLowRowOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 0)
  have secondSmooth (context : CoupledCoordinateContext parameters L compact) :
      ContDiff ℝ ∞ (fun tau => (lowCellOutput context.lower L context.positive).comp
        (Grad.AnnularLowOrbit.actualLowRowOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 1 tau)) :=
    complexOperatorComposition_contDiff _ _ contDiff_const
      (actualLowRowOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 1)
  have thirdSmooth (context : CoupledCoordinateContext parameters L compact) :
      ContDiff ℝ ∞ (fun tau => (lowAngularOutput context.lower L context.positive).comp
        (Grad.AnnularLowOrbit.actualLowRowOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 2 tau)) :=
    complexOperatorComposition_contDiff _ _ contDiff_const
      (actualLowRowOrbit_contDiff parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 2)
  have combined := (first.add second firstSmooth secondSmooth).add third (fun context => (firstSmooth context).add (secondSmooth context)) thirdSmooth
  apply combined.precomposeComplex
    (fun context => ((firstSmooth context).add (secondSmooth context)).add (thirdSmooth context))
    (fun context => highCrossSevenInput context.lower L context.positive context.lengthPositive) (4 + 2 * |L|) (by positivity)
  intro context
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (highCrossSevenInput_bound context.lower L context.positive context.lengthPositive)
end Grad.AnnularCrossOrbit
