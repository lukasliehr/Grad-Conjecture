import AKBI7ActualEulerFrameContractions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelGraphRestriction
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField Grad.SourceCollarFullSource
open Grad.BoundaryKernelAction Grad.ActualPolarEquations

theorem originalScalarTrace_scale {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {firstRow secondRow : DivisionRow 1 lower}
    (first : SmoothLowPhysicalRow parameters lower positive firstRow) (second : SmoothLowPhysicalRow parameters lower positive secondRow)
    (bounded : lower<1) (scalar : ℂ) (radius : Icc lower (1 : ℝ))
    (same : ∀ angles,scalar • first.fullField bounded (radius.val,angles)=second.fullField bounded (radius.val,angles)) :
    scalar • originalCurveNegativeTrace first radius=originalCurveNegativeTrace second radius := by
  rw [← originalCurveNegativeTrace_smul]
  apply originalCurveNegativeTrace_ext _ _ bounded radius
  intro angles
  rw [samePhysical_fullField_smul first bounded scalar radius.val radius.property angles]
  exact same angles

theorem originalCurveNegativeTrace_coordinate {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (coordinate : Fin 3) (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (curves.bulkUnit (0 : Fin 1) coordinate) radius=
      forceCoordinateTrace _ 0 0 coordinate (originalCurveNegativeTrace curves radius) := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [originalCurveNegativeTrace_coefficient _ bounded radius,originalCurveNegative_coordinate_coefficient curves bounded radius]
  congr 1
  funext angles
  rw [curves.fullField_bulkUnit bounded (0 : Fin 1) coordinate radius.val radius.property angles]

theorem originalCoreNegativeTrace_rotation (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (field : ACore parameters 1) (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeRotation (originalCoreLowCurves parameters lower positive bounded field) radius=
      originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded (rotationCore parameters field)) radius := by
  have original := originalCoreNegative_circle parameters lower positive bounded field radius
    (originalCoreLowCurves parameters lower positive bounded field)
    (originalCoreLowCurves_fullField parameters lower positive bounded field radius.val radius.property)
  have rotated := original.rotation (originalCurveNegativeRotation_derivative _ bounded radius)
    (originalCoreCircleTrace_rotation parameters field (tupleRadius lower positive radius))
  exact rotated.unique (originalCoreNegative_circle parameters lower positive bounded (rotationCore parameters field) radius
    (originalCoreLowCurves parameters lower positive bounded (rotationCore parameters field))
    (originalCoreLowCurves_fullField parameters lower positive bounded _ radius.val radius.property))

theorem originalCoreNegativeTrace_add (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (first second : ACore parameters 1) (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded (first+second)) radius=
      originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded first) radius+
      originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded second) radius := by
  rw [← originalCurveNegativeTrace_add]
  apply originalCurveNegativeTrace_ext _ _ bounded radius
  intro angles
  rw [SmoothLowPhysicalRow.fullField_add _ bounded _ radius.val radius.property angles,
    originalCoreLowCurves_fullField parameters lower positive bounded (first+second) radius.val radius.property angles,
    originalCoreLowCurves_fullField parameters lower positive bounded first radius.val radius.property angles,
    originalCoreLowCurves_fullField parameters lower positive bounded second radius.val radius.property angles]
  exact coreValue_add _ _ _ _

theorem originalCoreNegativeTrace_sub (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (first second : ACore parameters 1) (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded (first-second)) radius=
      originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded first) radius-
      originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded second) radius := by
  have original := originalCoreNegative_circle parameters lower positive bounded (first-second) radius _
    (originalCoreLowCurves_fullField parameters lower positive bounded (first-second) radius.val radius.property)
  rw [originalCoreCircleTrace_sub] at original
  exact original.unique ((originalCoreNegative_circle parameters lower positive bounded first radius _
    (originalCoreLowCurves_fullField parameters lower positive bounded first radius.val radius.property)).sub
    (originalCoreNegative_circle parameters lower positive bounded second radius _
      (originalCoreLowCurves_fullField parameters lower positive bounded second radius.val radius.property)))

theorem originalCoreNegativeTrace_meanFree (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (field : ACore parameters 1) (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded (removeAngularCore parameters field)) radius=
      forceMeanFreeTrace _ 0 0 (originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded field) radius) := by
  have original := originalCoreNegative_circle parameters lower positive bounded (removeAngularCore parameters field) radius _
    (originalCoreLowCurves_fullField parameters lower positive bounded (removeAngularCore parameters field) radius.val radius.property)
  rw [originalCoreCircleTrace_meanFree] at original
  exact original.unique ((originalCoreNegative_circle parameters lower positive bounded field radius _
    (originalCoreLowCurves_fullField parameters lower positive bounded field radius.val radius.property)).meanFree)

theorem originalScaledAngularDerivative_unique {parameters : PhaseParameters} {dimension : ℕ}
    {field derivative target slope : NegativeTrace parameters 0 0 dimension}
    (rotation : IsAngularDerivative parameters 0 0 field derivative)
    (targetRotation : IsAngularDerivative parameters 0 0 target slope)
    (scalar : ℂ) (same : scalar • field=target) : scalar • derivative=slope := by
  apply NegativeTrace.ext_coefficient parameters 0 0
  intro mode
  rw [negativeTraceCoefficient_smul,rotation mode,targetRotation mode,← same,negativeTraceCoefficient_smul]
  exact smul_comm _ _ _

end Grad.OriginalKernelHomogeneousGraph
