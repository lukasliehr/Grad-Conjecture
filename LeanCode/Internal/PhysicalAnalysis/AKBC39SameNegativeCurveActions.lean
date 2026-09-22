import AKBC38ActualHomogeneousNegativeThird

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2
open Grad.AnnularWeightedSmoothness Grad.PhaseAlgebra

theorem originalCurveNegativeTrace_ext {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {firstRow secondRow : DivisionRow dimension lower}
    (first : SmoothLowPhysicalRow parameters lower positive firstRow)
    (second : SmoothLowPhysicalRow parameters lower positive secondRow) (bounded : lower<1)
    (radius : Icc lower (1 : ℝ))
    (same : ∀ angles,first.fullField bounded (radius.val,angles)=second.fullField bounded (radius.val,angles)) :
    originalCurveNegativeTrace first radius=originalCurveNegativeTrace second radius := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [originalCurveNegativeTrace_coefficient first bounded radius,originalCurveNegativeTrace_coefficient second bounded radius]
  exact congrArg (fun source => doubleCoefficient source mode) (funext same)

theorem originalCurveNegativeTrace_action {input output : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius input output)
    (regular : RegularKernelFamily kernel) (smooth : SmoothConjugatedFamily parameters lower positive bounded.le kernel)
    {row : DivisionRow input lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (curves.action parameters lower positive bounded kernel regular smooth) radius=
      fullNegativeKernelAction _ 0 0 (kernel (tupleRadius lower positive radius)) (originalCurveNegativeTrace curves radius) := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [originalCurveNegativeTrace_coefficient _ bounded radius,
    SmoothLowPhysicalRow.fullField_doubleCoefficient _ bounded radius.val radius.property mode]
  apply curves.physicalCurve_action_eq_of_hasSum parameters lower positive bounded kernel regular smooth radius.val radius.property mode
  have action := fullNegativeKernelAction_coefficient_hasSum (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
    (kernel (tupleRadius lower positive radius)) (originalCurveNegativeTrace curves radius) mode
  apply action.congr_fun
  intro shift
  rw [originalCurveNegativeTrace_coefficient curves bounded radius,
    curves.fullField_doubleCoefficient bounded radius.val radius.property]
  have sameRadius : collarRadius lower positive bounded.le radius.val=tupleRadius lower positive radius :=
    Subtype.ext (collarRadius_literal lower positive bounded.le radius.val radius.property)
  rw [sameRadius]

theorem originalCurveNegativeTrace_add {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {firstRow secondRow : DivisionRow dimension lower}
    (first : SmoothLowPhysicalRow parameters lower positive firstRow)
    (second : SmoothLowPhysicalRow parameters lower positive secondRow) (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (first.add second) radius=originalCurveNegativeTrace first radius+originalCurveNegativeTrace second radius := by
  exact map_add (bulkNegativeLift parameters (tupleRadius lower positive radius) dimension) _ _

theorem originalCurveNegativeTrace_smul {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (radius : Icc lower (1 : ℝ)) (scalar : ℂ) :
    originalCurveNegativeTrace (curves.smul scalar) radius=scalar • originalCurveNegativeTrace curves radius := by
  exact map_smul (bulkNegativeLift parameters (tupleRadius lower positive radius) dimension) scalar _

theorem originalCurveNegativeTrace_meanFree {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace curves.meanFree radius=forceMeanFreeTrace _ 0 0 (originalCurveNegativeTrace curves radius) := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  simp only [originalCurveNegativeTrace,bulkNegativeLift_coefficient,forceMeanFreeTrace,
    angularMeanFreeKernel,scalarModeDiagonalKernel_action_coefficient]
  change (Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ •
    ((if mode.1=0 then (0 : ℂ) else 1) • curves.curve 0 radius.val mode)=
      (if mode.1=0 then (0 : ℂ) else 1) •
        ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ • curves.curve 0 radius.val mode)
  exact smul_comm _ _ _

end Grad.OriginalKernelCovariantRecovery
