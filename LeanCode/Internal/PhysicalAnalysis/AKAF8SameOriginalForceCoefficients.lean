import AKAF7SamePhysicalFieldEquality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.AnnularPhysicalReconstruction Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.ActualSmoothPhysicalField Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.PhaseAlgebra
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness

/-- The seven physical input traces use exactly the SAME normalized
low-rho coefficients; no radial normalization is silently changed. -/
theorem sameSevenTrace_coefficient (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (row : DivisionRow 7 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ slot mode,
      negativeTraceCoefficient (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0 0
        (physicalBulkSevenTrace parameters lower positive (collarRadius lower positive bounded radius)
          (collectRadial lower row radius) slot) mode 0 =
      lowRhoPhysicalCoefficient parameters lower positive row radius mode slot := by
  filter_upwards [collectRadial_ae lower row,ae_restrict_mem measurableSet_Icc] with radius actual inside
  intro slot mode
  rw [physicalBulkSevenTrace_coefficient,actual mode,collarRadius_literal lower positive bounded radius inside]
  rfl

def fullPhysicalForceAction (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : AnnularReconstructionState parameters length compact) (kind : Fin 2) :
    DivisionRow 3 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters 0 lower positive bounded
    (fun radius => radialForceKernel parameters length compact state.val radius kind 0)
    (radialForceKernel_regular parameters length compact state.val kind 0)

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : AnnularReconstructionState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)

/-- The first original polar force row holds for the actual full physical
coefficients of the SAME reconstruction and prescribed full source. -/
theorem sharedFull_firstForce_physicalCoefficients :
    let covariant := sharedFullCovariant parameters length compact lower positive bounded.le lengthPositive state data solution
    let rotated := sharedFullRotatedCovariant parameters length compact lower positive bounded.le lengthPositive state data solution
    let seven := fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution
    let force := fullPhysicalForceAction parameters length compact lower positive bounded.le state 0 covariant
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      -lowRhoPhysicalCoefficient parameters lower positive rotated radius mode 1 -
        2 * lowRhoPhysicalCoefficient parameters lower positive covariant radius mode 0 +
        lowRhoPhysicalCoefficient parameters lower positive force radius mode 0 +
        lowRhoPhysicalCoefficient parameters lower positive seven radius mode 1 =
        lowRhoPhysicalCoefficient parameters lower positive seven radius mode 4 := by
  dsimp only
  let covariant := sharedFullCovariant parameters length compact lower positive bounded.le lengthPositive state data solution
  let force := fullPhysicalForceAction parameters length compact lower positive bounded.le state 0 covariant
  filter_upwards [sharedFull_originalSliceLaws parameters length compact lower positive bounded.le lengthPositive state data solution,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le covariant,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (sharedFullRotatedCovariant parameters length compact lower positive bounded.le lengthPositive state data solution),
    originalPhysicalSlice_coefficient parameters lower positive bounded.le force,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (fun radius => radialForceKernel parameters length compact state.val radius 0 0)
      (radialForceKernel_regular parameters length compact state.val 0 0) covariant,
    sameSevenTrace_coefficient parameters lower positive bounded.le
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)]
      with radius laws covariantSame rotatedSame forceSame actionSame inputSame
  intro mode
  dsimp only [force,fullPhysicalForceAction] at forceSame
  have law := congrArg (fun trace => negativeTraceCoefficient
    (radialKernelParameters parameters (collarRadius lower positive bounded.le radius)) 0 0 trace mode 0) laws.firstForce
  simp only [negativeTraceCoefficient_add,negativeTraceCoefficient_sub,negativeTraceCoefficient_neg,
    negativeTraceCoefficient_smul,PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,PiLp.smul_apply,smul_eq_mul,
    forceCoordinateTrace,coordinateProjectionKernel_action_coefficient] at law
  rw [← actionSame,forceSame mode,covariantSame mode,rotatedSame mode,inputSame 1 mode,inputSame 4 mode] at law
  exact law

/-- The third original polar force row holds for the actual full physical
coefficients of the SAME reconstruction and prescribed full source. -/
theorem sharedFull_thirdForce_physicalCoefficients :
    let covariant := sharedFullCovariant parameters length compact lower positive bounded.le lengthPositive state data solution
    let rotated := sharedFullRotatedCovariant parameters length compact lower positive bounded.le lengthPositive state data solution
    let seven := fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution
    let force := fullPhysicalForceAction parameters length compact lower positive bounded.le state 1 covariant
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive rotated radius mode 2 +
        (if mode.1 = 0 then 0 else lowRhoPhysicalCoefficient parameters lower positive force radius mode 0) -
        (length : ℂ)⁻¹ * lowRhoPhysicalCoefficient parameters lower positive seven radius mode 2 =
        lowRhoPhysicalCoefficient parameters lower positive seven radius mode 6 := by
  dsimp only
  let covariant := sharedFullCovariant parameters length compact lower positive bounded.le lengthPositive state data solution
  let force := fullPhysicalForceAction parameters length compact lower positive bounded.le state 1 covariant
  filter_upwards [sharedFull_originalSliceLaws parameters length compact lower positive bounded.le lengthPositive state data solution,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (sharedFullRotatedCovariant parameters length compact lower positive bounded.le lengthPositive state data solution),
    originalPhysicalSlice_coefficient parameters lower positive bounded.le force,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (fun radius => radialForceKernel parameters length compact state.val radius 1 0)
      (radialForceKernel_regular parameters length compact state.val 1 0) covariant,
    sameSevenTrace_coefficient parameters lower positive bounded.le
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)]
      with radius laws rotatedSame forceSame actionSame inputSame
  intro mode
  dsimp only [force,fullPhysicalForceAction] at forceSame
  have law := congrArg (fun trace => negativeTraceCoefficient
    (radialKernelParameters parameters (collarRadius lower positive bounded.le radius)) 0 0 trace mode 0) laws.thirdForce
  simp only [negativeTraceCoefficient_add,negativeTraceCoefficient_sub,
    negativeTraceCoefficient_smul,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    forceCoordinateTrace,coordinateProjectionKernel_action_coefficient,
    forceMeanFreeTrace,angularMeanFreeKernel,scalarModeDiagonalKernel_action_coefficient] at law
  rw [← actionSame,forceSame mode,rotatedSame mode,inputSame 2 mode,inputSame 6 mode] at law
  by_cases zero : mode.1 = 0 <;> simpa [zero,angularMeanFreeMultiplier,fullPhysicalForceAction,covariant] using law

end Grad.ActualPolarEquations
