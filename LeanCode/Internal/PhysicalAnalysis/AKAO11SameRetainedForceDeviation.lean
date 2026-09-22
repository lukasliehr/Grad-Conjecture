import AKAO10LiteralSameBThree

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
    (state : RetainedInverseState parameters length compact)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

theorem retainedForceDeviation_smooth :
    SmoothConjugatedFamily parameters lower positive bounded.le
      (fun r => radialRetainedForceDeviationKernel parameters length compact state.val.val r) := by
  exact rowRadialJet_conjugated_smooth parameters 3 lower positive bounded
    (fun order radius column => polarEntryScalar parameters
      (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field)
      (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
      0 column order radius)
    (fun order radius column mode => polarEntryScalar_hasDerivAt parameters _ _ 0 column order radius mode)
    (fun order r column moment => polarEntryScalarMoment_summable parameters _ _ 0 column moment order r.val r.property.1 r.property.2)
    (fun order moment column => ⟨_, fun r => polarEntryScalarMoment_bound parameters _ _ 0 column moment order r.val r.property.1 r.property.2⟩) 0

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.retainedForceDeviation :
    SmoothLowPhysicalRow parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le
        (radialRetainedForceDeviationKernel parameters length compact state.val.val)
        (radialRetainedForceDeviationKernel_regular parameters length compact state.val) row) :=
  curves.action parameters lower positive bounded _
    (radialRetainedForceDeviationKernel_regular parameters length compact state.val)
    (retainedForceDeviation_smooth parameters length compact lower positive bounded state)

/-- The SAME completed original retained force deviation equals literal polar matrix multiplication. -/
theorem fullField_retainedForceDeviation (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.retainedForceDeviation parameters length compact lower positive bounded state).fullField bounded (radius,angles) =
      polarFamilyRowProduct parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) 0 radius
        (positive.le.trans inside.1) inside.2 (fun angles => curves.fullField bounded (radius,angles)) angles := by
  let source := fun angles => curves.fullField bounded (radius,angles)
  have sourceContinuous : Continuous source := curves.fullField_continuous_angles bounded radius inside
  apply congrFun ((curves.retainedForceDeviation parameters length compact lower positive bounded state).fullField_eq_of_doubleCoefficient
    bounded radius inside
    (polarFamilyRowProduct parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) 0 radius (positive.le.trans inside.1) inside.2 source)
    (polarFamilyRowProduct_continuous parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) 0
      radius (positive.le.trans inside.1) inside.2 source sourceContinuous) ?_ ?_ ?_) angles
  · intro axial polar
    unfold polarFamilyRowProduct
    apply Finset.sum_congr rfl
    intro component _
    rw [(polarFamilyAngleEntry_periodic parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) 0
      radius (positive.le.trans inside.1) inside.2 component (polar,axial)).1]
    rw [show source (polar+2*Real.pi,axial)=source (polar,axial) from curves.fullField_angular_shift bounded radius polar axial]
  · intro polar axial
    unfold polarFamilyRowProduct
    apply Finset.sum_congr rfl
    intro component _
    rw [(polarFamilyAngleEntry_periodic parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) 0
      radius (positive.le.trans inside.1) inside.2 component (polar,axial)).2]
    rw [show source (polar,axial+2*Real.pi)=source (polar,axial) from curves.fullField_cell_shift bounded radius polar axial]
  · intro mode
    symm
    apply curves.physicalCurve_action_eq_of_hasSum parameters lower positive bounded
      (radialRetainedForceDeviationKernel parameters length compact state.val.val)
      (radialRetainedForceDeviationKernel_regular parameters length compact state.val)
      (retainedForceDeviation_smooth parameters length compact lower positive bounded state) radius inside mode
    have series := polarFamilyRowProduct_hasSum parameters (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low) 0
      radius (positive.le.trans inside.1) inside.2 source sourceContinuous mode
    apply series.congr_fun
    intro shift
    change rowMultiplicationEntry 3
      (fun component => radialRetainedForceBaseCoefficient parameters length compact state.val.val
        (collarRadius lower positive bounded.le radius) component)
      shift (twoFrequencyTranslation shift mode) (curves.physicalCurve 0 radius (twoFrequencyTranslation shift mode)) = _
    simp only [radialRetainedForceBaseCoefficient]
    rw [collarRadius_literal lower positive bounded.le radius inside,curves.fullField_doubleCoefficient bounded radius inside]


end Grad.ActualPolarFlux
