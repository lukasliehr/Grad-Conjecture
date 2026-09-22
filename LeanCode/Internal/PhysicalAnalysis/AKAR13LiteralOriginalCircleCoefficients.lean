import AKAR12OriginalA4CircleTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.PhaseAlgebra Grad.BoundaryLift Grad.OriginalFlatAxisDecay

variable {dimension : ℕ}

def originalCircleCellValue (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (radius : RadialPoint) (rotated : Bool) (cell : ℤ) (angle : ℝ) : ComplexEuclidean dimension :=
  let point := polarClosedPoint radius.val angle radius.property.1 radius.property.2
  if rotated then originalRotationAt parameters cell point field
  else completedOriginalCell parameters (by omega) cell field point

theorem originalFlatCircleCell_weight (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (radius : RadialPoint) (rotated : Bool) (cell : ℤ) (angle : ℝ) :
    originalFlatCircleCell parameters field flat radius rotated cell angle =
      (lambdaCircleWeight parameters radius.val (0,cell) : ℂ) • originalCircleCellValue parameters field radius rotated cell angle := by
  cases rotated
  · change (cellFrequency cell : ℂ) • completedWeightedCell parameters (by omega) cell field
      (polarClosedPoint radius.val angle radius.property.1 radius.property.2) = _
    rw [completedWeightedCell,ContinuousLinearMap.comp_apply,originalWeightAction_apply,← Complex.coe_smul]
    change (cellFrequency cell : ℂ) • ((cartesianWeight parameters cell (polarPlane (radius.val,angle)) : ℂ) • _) = _
    rw [cartesianWeight_polar parameters cell radius.val angle radius.property.1,smul_smul]
    unfold lambdaCircleWeight originalCircleCellValue
    push_cast
    rw [mul_comm]
  · change (cellFrequency cell : ℂ) • (cartesianWeight parameters cell (polarPlane (radius.val,angle)) •
      originalRotationAt parameters cell (polarClosedPoint radius.val angle radius.property.1 radius.property.2) field) = _
    rw [← Complex.coe_smul]
    rw [cartesianWeight_polar parameters cell radius.val angle radius.property.1,smul_smul]
    unfold lambdaCircleWeight originalCircleCellValue
    push_cast
    rw [mul_comm]
    rfl

/-- Literal unweighted Fourier coefficient after decoding the same Wλ trace. -/
theorem originalA4CircleTrace_originalCoefficient (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (radius : RadialPoint) (rotated : Bool) (mode : ℤ × ℤ) :
    lambdaCircleCoefficient parameters radius.val (originalA4CircleTrace parameters field flat radius rotated) mode =
      angularCoefficient (originalCircleCellValue parameters field radius rotated mode.2) mode.1 := by
  rw [lambdaCircleCoefficient,originalA4CircleTrace_coefficient]
  have weighted : originalFlatCircleCell parameters field flat radius rotated mode.2 =
      (lambdaCircleWeight parameters radius.val mode : ℂ) • originalCircleCellValue parameters field radius rotated mode.2 :=
    funext (fun angle => originalFlatCircleCell_weight parameters field flat radius rotated mode.2 angle)
  rw [weighted,angularCoefficient_smul_continuous,smul_smul,inv_mul_cancel₀
    (Complex.ofReal_ne_zero.mpr (lambdaCircleWeight_positive parameters radius.val mode).ne'),one_smul]

end Grad.OriginalKernelRetainedDecay
