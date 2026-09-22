import AKAJ2ActualForceProductConvolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualForceMatrixFidelity
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.ActualPolarEquations
open Grad.BoundaryKernelAction Grad.AnnularWeightedSmoothness Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : AnnularReconstructionState parameters length compact) (kind : Fin 2)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Exact physical matrix fidelity for the SAME completed original force row. -/
theorem fullField_forceMatrixProduct (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (physicalForceCurves parameters length compact lower positive bounded state kind curves).fullField bounded (radius,angles) =
      forceMatrixProduct parameters length state.val.data.epsilon state.val.data.field kind radius
        (positive.le.trans inside.1) inside.2 (fun angles => curves.fullField bounded (radius,angles)) angles := by
  let source := fun angles => curves.fullField bounded (radius,angles)
  have sourceContinuous : Continuous source := curves.fullField_continuous_angles bounded radius inside
  apply congrFun ((physicalForceCurves parameters length compact lower positive bounded state kind curves).fullField_eq_of_doubleCoefficient
    bounded radius inside
    (forceMatrixProduct parameters length state.val.data.epsilon state.val.data.field kind radius (positive.le.trans inside.1) inside.2 source)
    (forceMatrixProduct_continuous parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low kind
      radius (positive.le.trans inside.1) inside.2 source sourceContinuous) ?_ ?_ ?_) angles
  · intro axial polar
    unfold forceMatrixProduct
    apply Finset.sum_congr rfl
    intro component _
    rw [(forceAngleEntry_periodic parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low kind
      radius (positive.le.trans inside.1) inside.2 component (polar,axial)).1]
    rw [show source (polar+2*Real.pi,axial)=source (polar,axial) from curves.fullField_angular_shift bounded radius polar axial]
  · intro polar axial
    unfold forceMatrixProduct
    apply Finset.sum_congr rfl
    intro component _
    rw [(forceAngleEntry_periodic parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low kind
      radius (positive.le.trans inside.1) inside.2 component (polar,axial)).2]
    rw [show source (polar,axial+2*Real.pi)=source (polar,axial) from curves.fullField_cell_shift bounded radius polar axial]
  · intro mode
    symm
    apply curves.physicalCurve_action_eq_of_hasSum parameters lower positive bounded
      (fun radius => radialForceKernel parameters length compact state.val radius kind 0)
      (radialForceKernel_regular parameters length compact state.val kind 0)
      (radialForceKernel_conjugated_smooth parameters length compact state.val lower positive bounded kind 0) radius inside mode
    have series := forceMatrixProduct_hasSum parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low kind
      radius (positive.le.trans inside.1) inside.2 source sourceContinuous mode
    apply series.congr_fun
    intro shift
    change rowMultiplicationEntry 3
      (fun component => forceScalar parameters length state.val.data.rho state.val.data.epsilon state.val.data.field kind state.val.low component 0
        (collarRadius lower positive bounded.le radius).val)
      shift (twoFrequencyTranslation shift mode) (curves.physicalCurve 0 radius (twoFrequencyTranslation shift mode)) = _
    rw [collarRadius_literal lower positive bounded.le radius inside,curves.fullField_doubleCoefficient bounded radius inside]

/-- Both original factors and signs are inside forcePolarComponent:
kind0 uses +2 tangential, kind1 uses -2 toroidal. -/
theorem fullField_forceMatrixComponent (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (physicalForceCurves parameters length compact lower positive bounded state kind curves).fullField bounded (radius,angles) 0 =
      ∑ component : Fin 3,forcePolarComponent kind angles.1
        (originalForceMatrix parameters length state.val.data.epsilon state.val.data.field angles.2
          (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)) component *
        curves.fullField bounded (radius,angles) component := by
  rw [fullField_forceMatrixProduct parameters length compact lower positive bounded state kind curves radius inside angles]
  simp [forceMatrixProduct,forceAngleEntry,matrixUnit_apply,operatorBasis]

end Grad.ActualForceMatrixFidelity
