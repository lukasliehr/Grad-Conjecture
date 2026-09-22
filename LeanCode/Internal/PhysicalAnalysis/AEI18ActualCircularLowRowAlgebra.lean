import AEI17LiteralCircularCompletedAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

theorem lowMode_angular_nonzero (mode : LowAnnularMode) : mode.val.1 ≠ 0 := by
  intro zero
  have cases := mode.property
  rw [zero] at cases
  norm_num at cases

theorem lowCircularFirst_normalized (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (mode : LowAnnularMode) (radius : ℝ) (inside : lower ≤ radius)
    (first second : ComplexEuclidean 1) (kernelRadius : RadialPoint) :
    (lowAmplitude length parameters.gamma mode : ℂ) *
      ((lowCircularRowKernel parameters length 0 kernelRadius).entry (0, 0) mode.val
        (lowSevenInputSymbol parameters lower length positive mode radius first second)) 0 =
      ((-2 / radius / lowMu length radius mode.val.2 : ℝ) : ℂ) * first 0 -
        ((lowAmplitude length parameters.gamma mode * lowCircularB mode : ℝ) : ℂ) * second 0 := by
  change (lowAmplitude length parameters.gamma mode : ℂ) *
    ((circularNormalizedUnprojectedFirstRowKernel _ length).entry (0, 0) mode.val _) 0 = _
  rw [circularNormalizedUnprojectedFirstRowKernel_entry_zero]
  simp only [lowSevenInputSymbol_component, Fin.reduceEq, ite_true, ite_false]
  rw [lowInputRadiusCurve_actual parameters lower length positive mode radius inside]
  have mzero : (mode.val.1 : ℂ) ≠ 0 := by exact_mod_cast lowMode_angular_nonzero mode
  have rzero : (radius : ℂ) ≠ 0 := by exact_mod_cast (positive.trans_le inside).ne'
  have azero : (lowAmplitude length parameters.gamma mode : ℂ) ≠ 0 := by exact_mod_cast (lowAmplitude_pos length parameters.gamma mode).ne'
  have muzero : (lowMu length radius mode.val.2 : ℂ) ≠ 0 := by exact_mod_cast (lowMu_pos length radius mode.val.2 (positive.trans_le inside)).ne'
  simp only [angularDoubleInverseMultiplier, angularInverseMultiplier, if_neg (lowMode_angular_nonzero mode),
    lowCircularB, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_intCast, Complex.ofReal_ofNat,
    Complex.ofReal_neg, mul_zero, sub_zero]
  field_simp [mzero, rzero, azero, muzero, Complex.I_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem lowCircularSecond_normalized (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (mode : LowAnnularMode)
    (radius : ℝ) (inside : lower ≤ radius) (first second : ComplexEuclidean 1) (kernelRadius : RadialPoint) :
    (-Complex.I) * (((mode.val.2 : ℝ) / length / lowMu length radius mode.val.2 : ℝ) : ℂ) *
      ((lowCircularRowKernel parameters length 1 kernelRadius).entry (0, 0) mode.val
        (lowSevenInputSymbol parameters lower length positive mode radius first second)) 0 +
    (-Complex.I) * (((mode.val.1 : ℝ) * radius⁻¹ / lowMu length radius mode.val.2 : ℝ) : ℂ) *
      ((lowCircularRowKernel parameters length 2 kernelRadius).entry (0, 0) mode.val
        (lowSevenInputSymbol parameters lower length positive mode radius first second)) 0 =
      ((-lowCircularPotential length radius mode / (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2 ^ 2) : ℝ) : ℂ) * first 0 +
        ((2 / radius / lowMu length radius mode.val.2 : ℝ) : ℂ) * second 0 := by
  change (-Complex.I) * _ * ((circularNormalizedUnprojectedCKernel _ length).entry (0, 0) mode.val _) 0 +
    (-Complex.I) * _ * ((circularNormalizedPhysicalRVKernel _ length).entry (0, 0) mode.val _) 0 = _
  rw [circularNormalizedUnprojectedCKernel_entry_zero, circularNormalizedPhysicalRVKernel_entry_zero]
  simp only [lowSevenInputSymbol_component, Fin.reduceEq, ite_true, ite_false,
    angularMeanFreeMultiplier, if_neg (lowMode_angular_nonzero mode), one_mul, zero_add]
  rw [lowInputCellCurve_actual parameters lower length lengthPositive positive mode radius inside,
    lowInputAngularCurve_actual parameters lower length positive mode radius inside]
  have mzero : (mode.val.1 : ℂ) ≠ 0 := by exact_mod_cast lowMode_angular_nonzero mode
  have rzero : (radius : ℂ) ≠ 0 := by exact_mod_cast (positive.trans_le inside).ne'
  have lzero : (length : ℂ) ≠ 0 := by exact_mod_cast lengthPositive.ne'
  have azero : (lowAmplitude length parameters.gamma mode : ℂ) ≠ 0 := by exact_mod_cast (lowAmplitude_pos length parameters.gamma mode).ne'
  have muzero : (lowMu length radius mode.val.2 : ℂ) ≠ 0 := by exact_mod_cast (lowMu_pos length radius mode.val.2 (positive.trans_le inside)).ne'
  simp only [angularInverseMultiplier, if_neg (lowMode_angular_nonzero mode), lowCircularPotential]
  push_cast
  field_simp [mzero, rzero, lzero, azero, muzero, Complex.I_ne_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Grad.AnnularCurrentLow
