import AKAC24LiteralMatrixProductConvolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra Grad.ActualPhysicalField
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.BoundaryKernelAction Grad.AnnularWeightedSmoothness Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2

 theorem SmoothLowPhysicalRow.physicalCurve_action_eq_of_hasSum {input output : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius input output)
    (regular : RegularKernelFamily kernel)
    (smoothKernel : SmoothConjugatedFamily parameters lower positive bounded.le kernel)
    {row : DivisionRow input lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) (value : ComplexEuclidean output)
    (actual : HasSum (fun shift => (kernel (collarRadius lower positive bounded.le radius)).entry
      shift (twoFrequencyTranslation shift mode) (curves.physicalCurve 0 radius (twoFrequencyTranslation shift mode))) value) :
    (curves.action parameters lower positive bounded kernel regular smoothKernel).physicalCurve 0 radius mode = value := by
  have literal := collarRadius_literal lower positive bounded.le radius inside
  have inputSame (query : ℤ × ℤ) : curves.curve 0 radius query =
      (Grad.AnnularVariational.annularFrequency query.1 query.2 ^ 0 : ℂ) •
        ((Real.exp (radialPhase parameters (collarRadius lower positive bounded.le radius).val query.2) : ℂ) •
          curves.physicalCurve 0 radius query) := by
    rw [pow_zero,one_smul,literal,curves.physicalCurve_coefficient bounded 0 radius inside query,
      Real.exp_neg,Complex.ofReal_inv,smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
  have result := conjugatedKernelAction_exactCoefficient parameters 0
    (collarRadius lower positive bounded.le radius) (kernel (collarRadius lower positive bounded.le radius))
    (curves.curve 0 radius) (fun query => curves.physicalCurve 0 radius query) inputSame mode value actual
  rw [(curves.action parameters lower positive bounded kernel regular smoothKernel).physicalCurve_coefficient bounded 0 radius inside mode]
  change (Real.exp (-radialPhase parameters radius mode.2) : ℂ) •
    conjugatedKernelAction parameters 0 0 (collarRadius lower positive bounded.le radius)
      (kernel (collarRadius lower positive bounded.le radius)) (curves.curve 0 radius) mode = value
  rw [result,pow_zero,one_smul,literal,Real.exp_neg,Complex.ofReal_inv,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]

variable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {row : DivisionRow input lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- The same completed matrix action agrees with literal full matrix
multiplication of the same reconstructed field, with no replacement representative. -/
theorem SmoothLowPhysicalRow.fullField_matrixAction (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (angles : ℝ × ℝ) :
    (curves.matrixAction parameters family coherent lower positive bounded).fullField bounded (radius,angles) =
      physicalMatrixProduct parameters family radius (positive.le.trans inside.1) inside.2
        (fun angles => curves.fullField bounded (radius,angles)) angles := by
  let source := fun angles => curves.fullField bounded (radius,angles)
  have sourceContinuous : Continuous source := curves.fullField_continuous_angles bounded radius inside
  apply congrFun ((curves.matrixAction parameters family coherent lower positive bounded).fullField_eq_of_doubleCoefficient
    bounded radius inside (physicalMatrixProduct parameters family radius (positive.le.trans inside.1) inside.2 source)
    (physicalMatrixProduct_continuous parameters family coherent radius _ _ source sourceContinuous) ?_ ?_ ?_) angles
  · intro axial polar
    unfold physicalMatrixProduct
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro column _
    rw [(physicalMatrixAngleEntry_periodic parameters family coherent row column radius _ _ (polar,axial)).1]
    rw [show source (polar+2*Real.pi,axial)=source (polar,axial) from curves.fullField_angular_shift bounded radius polar axial]
  · intro polar axial
    unfold physicalMatrixProduct
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro column _
    rw [(physicalMatrixAngleEntry_periodic parameters family coherent row column radius _ _ (polar,axial)).2]
    rw [show source (polar,axial+2*Real.pi)=source (polar,axial) from curves.fullField_cell_shift bounded radius polar axial]
  · intro mode
    symm
    apply curves.physicalCurve_action_eq_of_hasSum parameters lower positive bounded
      (originalMatrixRadialKernel parameters family coherent)
      (originalMatrixRadialKernel_regular parameters family coherent)
      (originalMatrixRadialKernel_conjugated_smooth parameters family coherent lower positive bounded) radius inside mode
    have series := physicalMatrixProduct_hasSum parameters family coherent radius
      (positive.le.trans inside.1) inside.2 source sourceContinuous mode
    apply series.congr_fun
    intro shift
    change matrixMultiplicationEntry input output
      (fun row column => physicalMatrixScalar parameters family coherent row column 0
        (collarRadius lower positive bounded.le radius).val) shift (twoFrequencyTranslation shift mode)
      (curves.physicalCurve 0 radius (twoFrequencyTranslation shift mode)) = _
    rw [collarRadius_literal lower positive bounded.le radius inside,
      curves.fullField_doubleCoefficient bounded radius inside]

 theorem physicalMatrixProduct_apply (radius : ℝ) (nonnegative : 0 ≤ radius) (radiusBounded : radius ≤ 1)
    (source : ℝ × ℝ → ComplexEuclidean input) (angles : ℝ × ℝ) :
    physicalMatrixProduct parameters family radius nonnegative radiusBounded source angles =
      WithLp.toLp 2 ((familyMatrix family 0 angles.2 (polarClosedPoint radius angles.1 nonnegative radiusBounded)).mulVec
        (source angles)) := by
  unfold physicalMatrixProduct
  rw [Finset.sum_comm]
  apply PiLp.ext
  intro component
  simp [physicalMatrixAngleEntry,matrixUnit_apply,operatorBasis,Matrix.mulVec,dotProduct]

end Grad.ActualSmoothPhysicalField
