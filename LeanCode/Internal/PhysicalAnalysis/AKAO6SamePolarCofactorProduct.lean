import AKAO5SmoothPhysicalActionAlgebra

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

theorem cofactorJetSequence_zero (sequence : ℤ × ℤ → ℂ) : cofactorJetSequence 0 sequence=sequence := by
  funext mode
  simp [cofactorJetSequence,cofactorJetMultiplier]

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (cofactorRow : Fin 3)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.cofactorDeviationRow :
    SmoothLowPhysicalRow parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le
        (radialCofactorJetRowKernel parameters length compact state cofactorRow 0 0)
        (radialCofactorJetRowKernel_regular parameters length compact state cofactorRow 0 0) row) :=
  curves.action parameters lower positive bounded _
    (radialCofactorJetRowKernel_regular parameters length compact state cofactorRow 0 0)
    (actualCofactorRow_conjugated_smooth parameters length compact state lower positive bounded cofactorRow 0 0)

/-- The SAME completed original cofactor deviation equals literal polar matrix multiplication. -/
theorem fullField_cofactorDeviationProduct (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.cofactorDeviationRow parameters length compact lower positive bounded state cofactorRow).fullField bounded (radius,angles) =
      polarFamilyRowProduct parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) cofactorRow radius
        (positive.le.trans inside.1) inside.2 (fun angles => curves.fullField bounded (radius,angles)) angles := by
  let source := fun angles => curves.fullField bounded (radius,angles)
  have sourceContinuous : Continuous source := curves.fullField_continuous_angles bounded radius inside
  apply congrFun ((curves.cofactorDeviationRow parameters length compact lower positive bounded state cofactorRow).fullField_eq_of_doubleCoefficient
    bounded radius inside
    (polarFamilyRowProduct parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) cofactorRow radius (positive.le.trans inside.1) inside.2 source)
    (polarFamilyRowProduct_continuous parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) cofactorRow
      radius (positive.le.trans inside.1) inside.2 source sourceContinuous) ?_ ?_ ?_) angles
  · intro axial polar
    unfold polarFamilyRowProduct
    apply Finset.sum_congr rfl
    intro component _
    rw [(polarFamilyAngleEntry_periodic parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) cofactorRow
      radius (positive.le.trans inside.1) inside.2 component (polar,axial)).1]
    rw [show source (polar+2*Real.pi,axial)=source (polar,axial) from curves.fullField_angular_shift bounded radius polar axial]
  · intro polar axial
    unfold polarFamilyRowProduct
    apply Finset.sum_congr rfl
    intro component _
    rw [(polarFamilyAngleEntry_periodic parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) cofactorRow
      radius (positive.le.trans inside.1) inside.2 component (polar,axial)).2]
    rw [show source (polar,axial+2*Real.pi)=source (polar,axial) from curves.fullField_cell_shift bounded radius polar axial]
  · intro mode
    symm
    apply curves.physicalCurve_action_eq_of_hasSum parameters lower positive bounded
      (radialCofactorJetRowKernel parameters length compact state cofactorRow 0 0)
      (radialCofactorJetRowKernel_regular parameters length compact state cofactorRow 0 0)
      (actualCofactorRow_conjugated_smooth parameters length compact state lower positive bounded cofactorRow 0 0) radius inside mode
    have series := polarFamilyRowProduct_hasSum parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field) (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) cofactorRow
      radius (positive.le.trans inside.1) inside.2 source sourceContinuous mode
    apply series.congr_fun
    intro shift
    change rowMultiplicationEntry 3
      (fun component => radialCofactorJetScalar parameters length compact state cofactorRow component 0 0
        (collarRadius lower positive bounded.le radius))
      shift (twoFrequencyTranslation shift mode) (curves.physicalCurve 0 radius (twoFrequencyTranslation shift mode)) = _
    simp only [radialCofactorJetScalar,cofactorJetSequence_zero]
    rw [collarRadius_literal lower positive bounded.le radius inside,curves.fullField_doubleCoefficient bounded radius inside]
    rfl


end Grad.ActualPolarFlux
