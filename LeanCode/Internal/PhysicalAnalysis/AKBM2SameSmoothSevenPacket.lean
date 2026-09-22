import AKBM1SameSmoothAngularAxialCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelCovariantRecovery Grad.AnnularPhysicalReconstruction

/-- Matrix insertion preserves the literal negative Fourier trace. -/
theorem originalCurveNegativeTrace_bulkUnit {source target : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0<lower} {row : DivisionRow source lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (output : Fin target) (input : Fin source)
    (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (curves.bulkUnit output input) radius=
      fullNegativeKernelAction _ 0 0 (constantMatrixKernel _ source target (matrixUnit output input))
        (originalCurveNegativeTrace curves radius) := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [constantMatrixKernel_action_coefficient]
  simp only [originalCurveNegativeTrace,bulkNegativeLift_coefficient]
  change (Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ •
    matrixUnit output input (curves.curve 0 radius.val mode)=
    matrixUnit output input ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ • curves.curve 0 radius.val mode)
  exact (map_smul (matrixUnit output input) _ _).symm

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {pressureRow xiRow : DivisionRow 1 lower}
    (pressure : SmoothLowPhysicalRow parameters lower positive pressureRow)
    (xi : SmoothLowPhysicalRow parameters lower positive xiRow) (bounded : lower<1)

def originalSmoothSevenCurves :=
  (((originalDifferentiatedCurves pressure bounded false).2.bulkUnit (0 : Fin 7) 0).add
    ((originalInverseRadiusCurves lower positive (originalDifferentiatedCurves xi bounded false).2).bulkUnit (1 : Fin 7) 0)).add
    (((originalDifferentiatedCurves xi bounded true).2.bulkUnit (2 : Fin 7) 0).add
      ((originalInverseRadiusCurves lower positive xi).bulkUnit (3 : Fin 7) 0))

theorem originalSmoothSevenCurves_negative (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (originalSmoothSevenCurves pressure xi bounded) radius=
      sevenSlotFlatten _ 0 0 (WithLp.toLp 2 ![originalCurveNegativeRotation pressure radius,
        (radius.val : ℂ)⁻¹ • originalCurveNegativeRotation xi radius,originalCurveNegativeAxial xi radius,
        (radius.val : ℂ)⁻¹ • originalCurveNegativeTrace xi radius,0,0,0]) := by
  rw [originalSmoothSevenCurves]
  simp only [originalCurveNegativeTrace_add,originalCurveNegativeTrace_bulkUnit,
    originalCurveNegativeTrace_inverseRadius,originalDifferentiatedCurves_negativeRotation,
    originalDifferentiatedCurves_negativeAxial]
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  simp only [negativeTraceCoefficient_add,constantMatrixKernel_action_coefficient]
  apply PiLp.ext
  intro slot
  rw [sevenSlotFlatten_coefficient]
  fin_cases slot <;> simp [matrixUnit_apply,operatorBasis,negativeTraceCoefficient]

end Grad.OriginalKernelHomogeneousGraph
