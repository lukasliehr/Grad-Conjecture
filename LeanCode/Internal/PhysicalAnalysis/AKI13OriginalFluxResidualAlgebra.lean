import AKI12ComputedFirstResidual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore

/-- Angular inversion of the original X equation gives exactly AH24's
pressure residual, including P b3 and the full mean-free Vb. -/
theorem originalFluxResidual_algebra (length radius : ℝ) (lengthNonzero : length ≠ 0)
    (radiusNonzero : radius ≠ 0) (mode : ℤ × ℤ) (x b v g : ComplexEuclidean 1)
    (meanFreeV : angularMeanFreeMultiplier mode • v = v) :
    angularInverseMultiplier mode • ((if mode.1 = 0 then (0 : ℂ) else 1) •
      ((-((radius : ℂ)⁻¹)) • x - (length : ℂ)⁻¹ •
          (frequencyNumerator (some true) mode • (frequencyNumerator (some false) mode • b)) -
        (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • ((radius : ℂ) • v)) +
        frequencyNumerator (some false) mode • g)) +
      (radius : ℂ)⁻¹ • (angularInverseMultiplier mode • x) +
      (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • (angularMeanFreeMultiplier mode • b)) + v =
      (if mode.1 = 0 then (0 : ℂ) else 1) • g := by
  by_cases zero : mode.1 = 0
  · have vZero : v = 0 := by simpa [angularMeanFreeMultiplier, zero] using meanFreeV.symm
    simp [angularInverseMultiplier, angularMeanFreeMultiplier, zero, vZero]
  · have angularNonzero : (mode.1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr zero
    have lengthComplex : (length : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr lengthNonzero
    have radiusComplex : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr radiusNonzero
    ext slot
    simp only [angularInverseMultiplier, angularMeanFreeMultiplier, if_neg zero, frequencyNumerator,
      one_smul, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, neg_mul]
    field_simp
    ring

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower) (radius : Icc lower (1 : ℝ))

theorem tupleVTrace_fixed (mode : ℤ × ℤ) :
    angularMeanFreeMultiplier mode •
      negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (tupleVTrace parameters length compact lower positive state tuple radius) mode =
      negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (tupleVTrace parameters length compact lower positive state tuple radius) mode := by
  by_cases zero : mode.1 = 0
  · have zeroMode : mode = (0, mode.2) := Prod.ext zero rfl
    rw [zeroMode, tupleVTrace_meanFree]
    simp
  · simp [angularMeanFreeMultiplier, zero]

theorem tuplePhysicalRowTrace_c_coefficient (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tuplePhysicalRowTrace parameters length compact lower positive state tuple radius 1) mode =
    frequencyNumerator (some false) mode •
      negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (tupleBThreeTrace parameters length compact lower positive state tuple radius) mode :=
  tuplePhysicalRowTrace_c_derivative parameters length compact lower positive state tuple radius mode

theorem tuplePhysicalRowTrace_rV_coefficient (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tuplePhysicalRowTrace parameters length compact lower positive state tuple radius 2) mode =
    (radius.val : ℂ) • negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleVTrace parameters length compact lower positive state tuple radius) mode := by
  rw [tuplePhysicalRowTrace_rV, negativeTraceCoefficient_smul]

end Grad.AnnularOriginalSmoothCore
