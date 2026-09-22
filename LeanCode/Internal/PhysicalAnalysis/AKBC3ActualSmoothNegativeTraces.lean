import AKBC2SamePolarCovariant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.AnnularSmoothCore Grad.AnnularPhysicalReconstruction Grad.BoundaryKernelAction Grad.AnnularWeightedSmoothness

theorem originalFrequencyRatio_cancel {dimension : ℕ} (axis : Option Bool) (mode : ℤ × ℤ)
    (value : ComplexEuclidean dimension) :
    frequencyRatioSymbol axis mode • ((annularFrequency mode.1 mode.2 : ℂ) • value) = frequencyNumerator axis mode • value := by
  change (frequencyNumerator axis mode / (annularFrequency mode.1 mode.2 : ℂ)) • ((annularFrequency mode.1 mode.2 : ℂ) • value) = _
  rw [smul_smul,div_mul_cancel₀]
  exact Complex.ofReal_ne_zero.mpr (annularFrequency_pos mode).ne'

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : Icc lower (1 : ℝ))

def originalCurveNegativeTrace : NegativeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 dimension :=
  bulkNegativeLift parameters (tupleRadius lower positive radius) dimension (curves.curve 0 radius.val)

def originalCurveNegativeRotation : NegativeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 dimension :=
  bulkNegativeLift parameters (tupleRadius lower positive radius) dimension
    (hilbertFrequencyOperator parameters dimension (some false) (curves.curve 1 radius.val))

def originalCurveNegativeSecondRotation : NegativeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 dimension :=
  bulkNegativeLift parameters (tupleRadius lower positive radius) dimension
    (hilbertFrequencyOperator parameters dimension (some false)
      (hilbertFrequencyOperator parameters dimension (some false) (curves.curve 2 radius.val)))

theorem originalCurveNegativeTrace_coefficient (mode : ℤ × ℤ) :
    negativeTraceCoefficient _ 0 0 (originalCurveNegativeTrace curves radius) mode =
      doubleCoefficient (fun angles => curves.fullField bounded (radius.val,angles)) mode := by
  rw [originalCurveNegativeTrace,bulkNegativeLift_coefficient,curves.fullField_doubleCoefficient bounded radius.val radius.property mode,
    curves.physicalCurve_coefficient bounded 0 radius.val radius.property mode,Real.exp_neg,Complex.ofReal_inv]
  rfl

include bounded in
theorem originalCurveNegativeRotation_derivative :
    IsAngularDerivative _ 0 0 (originalCurveNegativeTrace curves radius) (originalCurveNegativeRotation curves radius) := by
  intro mode
  rw [originalCurveNegativeRotation,originalCurveNegativeTrace,bulkNegativeLift_coefficient,bulkNegativeLift_coefficient,
    hilbertFrequencyOperator_apply]
  have shift := curves.shift bounded 0 1 radius.val radius.property mode
  norm_num only [zero_add,pow_one] at shift
  rw [shift,originalFrequencyRatio_cancel]
  exact smul_comm _ _ _

include bounded in
theorem originalCurveNegativeSecondRotation_derivative :
    IsAngularDerivative _ 0 0 (originalCurveNegativeRotation curves radius) (originalCurveNegativeSecondRotation curves radius) := by
  intro mode
  rw [originalCurveNegativeSecondRotation,originalCurveNegativeRotation,bulkNegativeLift_coefficient,bulkNegativeLift_coefficient]
  simp only [hilbertFrequencyOperator_apply]
  have shift := curves.shift bounded 1 1 radius.val radius.property mode
  norm_num only [Nat.reduceAdd,pow_one] at shift
  rw [shift,originalFrequencyRatio_cancel,smul_comm (frequencyRatioSymbol (some false) mode)]
  exact smul_comm _ _ _

end Grad.OriginalKernelCovariantRecovery
