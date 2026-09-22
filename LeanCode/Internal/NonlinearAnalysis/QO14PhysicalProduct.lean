import QO13PhysicalValues

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

def physicalBilinear {inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension)) :
    ComplexEuclidean inputDimension →L[ℂ]
      ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean outputDimension :=
  (continuousMultilinearCurryFin1 ℂ (ComplexEuclidean inputDimension)
    (ComplexEuclidean outputDimension)).toContinuousLinearEquiv.toContinuousLinearMap.comp multiplication.curryLeft

theorem physicalBilinear_apply {inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (first second : ComplexEuclidean inputDimension) :
    physicalBilinear multiplication first second = multiplication ![first, second] := by
  change multiplication (Fin.cons first (Fin.snoc 0 second)) = multiplication ![first, second]
  congr 1
  funext index
  fin_cases index <;> rfl

/-- The original coefficient convolution is exactly the pointwise physical
bilinear product after Fourier synthesis. -/
theorem coreValue_pairProduct {inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (first second : ACore parameters inputDimension) (point : ClosedDisk) (angle : ℝ) :
    coreValue (pairProductLinear parameters multiplication first second) point angle =
      multiplication ![coreValue first point angle, coreValue second point angle] := by
  let bilinear := physicalBilinear multiplication
  have coefficientNorms : Summable (fun cell => ‖bilinear ((first.val cell).value point)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun cell => bilinear.le_opNorm ((first.val cell).value point))
      ((Gauges.originalValueNorm_summable parameters first point).mul_left ‖bilinear‖)
  have convolution := Gauges.operatorVectorConvolution_fourier
    (fun cell => bilinear ((first.val cell).value point))
    (fun cell => (second.val cell).value point) coefficientNorms
    (Gauges.originalValueNorm_summable parameters second point) angle
  have phase : Grad.GaugeCoefficients.Algebra.fourierPhase = axialPhase := by
    funext cell angle
    exact ((axialPhase_eq_character cell angle).trans (cellCharacter_coe cell angle)).symm
  rw [phase] at convolution
  have coefficientSum : (∑' cell, axialPhase cell angle • bilinear ((first.val cell).value point)) =
      bilinear (coreValue first point angle) := by
    unfold coreValue
    simp_rw [← map_smul]
    exact (bilinear.map_tsum (coreValue_summable first point angle)).symm
  rw [coefficientSum] at convolution
  have source (cell : ℤ) :
      ((pairProductLinear parameters multiplication first second).val cell).value point =
      ∑' shift, multiplication ![(first.val shift).value point, (second.val (cell - shift)).value point] := by
    rw [pairProductLinear_apply]
    exact (actualMultilinearProduct_isActual parameters multiplication ![first, second] cell point).trans
      (productCoefficientValue_pair multiplication first second cell point)
  unfold coreValue
  simp_rw [source]
  simpa only [bilinear, physicalBilinear_apply, coreValue] using convolution

theorem coreValue_dotOperation (first second : ACore parameters 3)
    (point : ClosedDisk) (angle : ℝ) :
    coreValue (dotOperation parameters first second) point angle 0 =
      Grad.NonlinearQuotient.complexDot (coreValue first point angle) (coreValue second point angle) := by
  change coreValue (pairProductLinear parameters physicalDotProduct first second) point angle 0 = _
  rw [coreValue_pairProduct, physicalDotProduct_value]

end Grad.NonlinearRange
