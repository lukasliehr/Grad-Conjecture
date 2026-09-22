import AKAO7SameSignedPolarCofactor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.ActualPolarEquations
open Grad.BoundaryKernelAction Grad.AnnularWeightedSmoothness Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualGaugeSigmaPrimitives

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (cofactorRow component : Fin 3)
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.cofactorDeviationComponent :
    SmoothLowPhysicalRow parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le
        (radialCofactorJetComponentKernel parameters length compact state cofactorRow component 0 0)
        (radialCofactorJetComponentKernel_regular parameters length compact state cofactorRow component 0 0) row) :=
  curves.action parameters lower positive bounded _
    (radialCofactorJetComponentKernel_regular parameters length compact state cofactorRow component 0 0)
    (actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded cofactorRow component 0 0)

/-- The SAME completed original cofactor deviation equals literal polar matrix multiplication. -/
theorem fullField_cofactorDeviationComponentProduct (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.cofactorDeviationComponent parameters length compact lower positive bounded state cofactorRow component).fullField bounded (radius,angles) =
      polarFamilyAngleEntry parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) cofactorRow component radius
        (positive.le.trans inside.1) inside.2 angles • curves.fullField bounded (radius,angles) := by
  let source := fun angles => curves.fullField bounded (radius,angles)
  have sourceContinuous : Continuous source := curves.fullField_continuous_angles bounded radius inside
  let coefficient := polarFamilyAngleEntry parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) cofactorRow component radius (positive.le.trans inside.1) inside.2
  have coefficientContinuous := polarFamilyAngleEntry_continuous parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) cofactorRow radius (positive.le.trans inside.1) inside.2 component
  have coefficientPeriodic := polarFamilyAngleEntry_periodic parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) cofactorRow radius (positive.le.trans inside.1) inside.2 component
  apply congrFun ((curves.cofactorDeviationComponent parameters length compact lower positive bounded state cofactorRow component).fullField_eq_of_doubleCoefficient
    bounded radius inside (fun angles => coefficient angles • source angles)
    (coefficientContinuous.smul sourceContinuous) ?_ ?_ ?_) angles
  · intro axial polar
    dsimp only [coefficient]
    rw [coefficientPeriodic (polar,axial) |>.1]
    rw [show source (polar+2*Real.pi,axial)=source (polar,axial) from curves.fullField_angular_shift bounded radius polar axial]
  · intro polar axial
    dsimp only [coefficient]
    rw [coefficientPeriodic (polar,axial) |>.2]
    rw [show source (polar,axial+2*Real.pi)=source (polar,axial) from curves.fullField_cell_shift bounded radius polar axial]
  · intro mode
    symm
    apply curves.physicalCurve_action_eq_of_hasSum parameters lower positive bounded
      (radialCofactorJetComponentKernel parameters length compact state cofactorRow component 0 0)
      (radialCofactorJetComponentKernel_regular parameters length compact state cofactorRow component 0 0)
      (actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded cofactorRow component 0 0) radius inside mode
    have series := polarScalar_product_hasSum parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) cofactorRow
      radius (positive.le.trans inside.1) inside.2 component source sourceContinuous mode
    apply series.congr_fun
    intro shift
    change radialCofactorJetScalar parameters length compact state cofactorRow component 0 0
      (collarRadius lower positive bounded.le radius) shift • curves.physicalCurve 0 radius (twoFrequencyTranslation shift mode) = _
    simp only [radialCofactorJetScalar,cofactorJetSequence_zero]
    rw [collarRadius_literal lower positive bounded.le radius inside,curves.fullField_doubleCoefficient bounded radius inside]
    rfl


end Grad.ActualPolarFlux
