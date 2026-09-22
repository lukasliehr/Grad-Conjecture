import AJB2SameNormalizedLowGeneratorOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction

/-- Fixed physical input/output assembly is a bounded complex-linear map
on the actual completed row operators. This is internal to the orbit block. -/
def actualLowRowAssembly (lower : ℝ) (output : DivisionRow 1 lower →L[ℂ] LowEnergyBulk lower)
    (input : LowEnergyBulk lower →L[ℂ] DivisionRow 7 lower) :
    (DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower) →L[ℂ] (LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower) :=
  ({ toFun := fun row => output.comp (row.comp input)
     map_add' := by
       intro first second
       apply ContinuousLinearMap.ext
       intro field
       exact output.map_add _ _
     map_smul' := by
       intro scalar row
       apply ContinuousLinearMap.ext
       intro field
       exact output.map_smul scalar _ } :
      (DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower) →ₗ[ℂ] (LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower)).mkContinuous
    (‖output‖ * ‖input‖) (fun row => by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro field
      change ‖output (row (input field))‖ ≤ _
      calc
        _ ≤ ‖output‖ * ‖row (input field)‖ := output.le_opNorm _
        _ ≤ ‖output‖ * (‖row‖ * ‖input field‖) :=
          mul_le_mul_of_nonneg_left (row.le_opNorm _) (norm_nonneg output)
        _ ≤ ‖output‖ * (‖row‖ * (‖input‖ * ‖field‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (input.le_opNorm field) (norm_nonneg row)) (norm_nonneg output)
        _ = _ := by ring)

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
  (state : RetainedInverseState parameters length compact)

def actualLowRowDifferential (output : DivisionRow 1 lower →L[ℂ] LowEnergyBulk lower)
    (row : Fin 3) (tau : OrbitParameter) :
    OrbitParameter →L[ℝ] (LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower) :=
  ((actualLowRowAssembly lower output (lowNormalizedSevenInput parameters lower length lengthPositive positive)).restrictScalars ℝ).comp
    (orbitDifferential (actualLowRowOrbitJet parameters length compact lower positive bounded state row tau 1 0)
      (actualLowRowOrbitJet parameters length compact lower positive bounded state row tau 0 1))

theorem actualLowRowAssembly_hasFDerivAt (output : DivisionRow 1 lower →L[ℂ] LowEnergyBulk lower)
    (row : Fin 3) (tau : OrbitParameter) :
    HasFDerivAt (fun sigma => actualLowRowAssembly lower output
        (lowNormalizedSevenInput parameters lower length lengthPositive positive)
        (actualLowRowOrbit parameters length compact lower positive bounded state row sigma))
      (actualLowRowDifferential parameters length compact lower lengthPositive positive bounded state output row tau) tau :=
  (((actualLowRowAssembly lower output (lowNormalizedSevenInput parameters lower length lengthPositive positive)).restrictScalars ℝ).hasFDerivAt).comp tau
    (actualLowRowOrbit_hasFDerivAt parameters length compact lower positive bounded state row tau)

def actualLowGeneratorDifferential (tau : OrbitParameter) :
    OrbitParameter →L[ℝ] (LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower) :=
  actualLowRowDifferential parameters length compact lower lengthPositive positive bounded state
      (lowFirstOutput parameters lower length) 0 tau +
    actualLowRowDifferential parameters length compact lower lengthPositive positive bounded state
      (lowCellOutput lower length positive) 1 tau +
    actualLowRowDifferential parameters length compact lower lengthPositive positive bounded state
      (lowAngularOutput lower length positive) 2 tau

/-- Genuine operator-norm Frechet derivative of the SAME normalized low
current generator orbit, retaining its exact fixed radial and phase diagonal. -/
theorem actualLowGeneratorOrbit_hasFDerivAt (tau : OrbitParameter) :
    HasFDerivAt (actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded state)
      (actualLowGeneratorDifferential parameters length compact lower lengthPositive positive bounded state tau) tau := by
  have first := actualLowRowAssembly_hasFDerivAt parameters length compact lower lengthPositive positive bounded state
    (lowFirstOutput parameters lower length) 0 tau
  have second := actualLowRowAssembly_hasFDerivAt parameters length compact lower lengthPositive positive bounded state
    (lowCellOutput lower length positive) 1 tau
  have third := actualLowRowAssembly_hasFDerivAt parameters length compact lower lengthPositive positive bounded state
    (lowAngularOutput lower length positive) 2 tau
  have same : actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded state =
      (fun sigma => lowCommonDiagonal parameters length lower lengthPositive positive +
        (actualLowRowAssembly lower (lowFirstOutput parameters lower length)
          (lowNormalizedSevenInput parameters lower length lengthPositive positive)
          (actualLowRowOrbit parameters length compact lower positive bounded state 0 sigma) +
        actualLowRowAssembly lower (lowCellOutput lower length positive)
          (lowNormalizedSevenInput parameters lower length lengthPositive positive)
          (actualLowRowOrbit parameters length compact lower positive bounded state 1 sigma) +
        actualLowRowAssembly lower (lowAngularOutput lower length positive)
          (lowNormalizedSevenInput parameters lower length lengthPositive positive)
          (actualLowRowOrbit parameters length compact lower positive bounded state 2 sigma))) := by
    funext sigma
    apply ContinuousLinearMap.ext
    intro field
    rfl
  rw [same]
  exact ((first.add second).add third).const_add (lowCommonDiagonal parameters length lower lengthPositive positive)

end Grad.AnnularLowOrbit
