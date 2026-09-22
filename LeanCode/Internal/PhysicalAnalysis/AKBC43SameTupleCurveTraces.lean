import AKBC42SameActualPressureTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.AnnularSmoothCore

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)
    (same : tuple.val slot=curves.fullField bounded) (radius : Icc lower (1 : ℝ))

include bounded same

theorem tupleNegativeTrace_sameCurves :
    tupleNegativeTrace parameters lower positive tuple slot radius=originalCurveNegativeTrace curves radius := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [tupleNegativeTrace_coefficient,originalCurveNegativeTrace_coefficient curves bounded radius,same]
  rw [originalPhysicalCoefficient,curves.fullField_coefficient bounded radius.val radius.property mode,
    curves.fullField_doubleCoefficient bounded radius.val radius.property mode]

theorem tupleDifferentiatedTrace_sameRotation :
    tupleDifferentiatedTrace parameters lower positive tuple slot false radius=originalCurveNegativeRotation curves radius := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [tupleDifferentiatedTrace_coefficient,originalCurveNegativeRotation_derivative curves bounded radius mode,
    originalCurveNegativeTrace_coefficient curves bounded radius,same]
  rw [originalPhysicalCoefficient,curves.fullField_coefficient bounded radius.val radius.property mode,
    curves.fullField_doubleCoefficient bounded radius.val radius.property mode]
  rfl

theorem tupleDifferentiatedTrace_sameAxial :
    tupleDifferentiatedTrace parameters lower positive tuple slot true radius=originalCurveNegativeAxial curves radius := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [tupleDifferentiatedTrace_coefficient,originalCurveNegativeAxial_coefficient curves bounded radius mode,
    originalCurveNegativeTrace_coefficient curves bounded radius,same]
  rw [originalPhysicalCoefficient,curves.fullField_coefficient bounded radius.val radius.property mode,
    curves.fullField_doubleCoefficient bounded radius.val radius.property mode]
  rfl

omit bounded same in
theorem tupleNegativeTrace_zero (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)
    (zero : tuple.val slot=0) (radius : Icc lower (1 : ℝ)) :
    tupleNegativeTrace parameters lower positive tuple slot radius=0 := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [tupleNegativeTrace_coefficient,zero]
  simp only [originalPhysicalCoefficient,Pi.zero_apply,Grad.BoundaryTrace.angularCoefficient_zero]
  exact (negativeTraceCoefficientCLM (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 mode).map_zero.symm

omit bounded same in
theorem tupleDifferentiatedTrace_zero (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)
    (zero : tuple.val slot=0) (axis : Bool) (radius : Icc lower (1 : ℝ)) :
    tupleDifferentiatedTrace parameters lower positive tuple slot axis radius=0 := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [tupleDifferentiatedTrace_coefficient,zero]
  simp only [originalPhysicalCoefficient,Pi.zero_apply,Grad.BoundaryTrace.angularCoefficient_zero,smul_zero]
  exact (negativeTraceCoefficientCLM (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 mode).map_zero.symm

end Grad.OriginalKernelCovariantRecovery
