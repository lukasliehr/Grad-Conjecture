import AKR21CoherentHilbertOriginalBulkStorage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (tuple : OriginalSmoothTuple parameters lower)

def tupleConjugatedF1Curve (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  tupleConjugatedDerivativeCurve parameters lower tuple 1 grade radius -
    hilbertMeanFree parameters (tupleConjugatedPhysicalRowCurve parameters length compact lower positive bounded state tuple 0 grade radius)

def tupleConjugatedG3Curve (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  ((tupleConjugatedDerivativeCurve parameters lower tuple 0 grade radius +
    (radius : ℂ)⁻¹ • tupleWeightedCurve parameters lower tuple 0 grade radius) +
    (length : ℂ)⁻¹ • physicalAngularPrimitive parameters (hilbertFrequencyOperator parameters 1 (some true)
      (tupleConjugatedPhysicalRowCurve parameters length compact lower positive bounded state tuple 1 (grade+1) radius))) +
    (radius : ℂ)⁻¹ • tupleConjugatedPhysicalRowCurve parameters length compact lower positive bounded state tuple 2 grade radius

theorem tupleConjugatedF1Curve_continuous (grade : ℕ) :
    ContinuousOn (tupleConjugatedF1Curve parameters length compact lower positive bounded state tuple grade) (Icc lower 1) :=
  (tupleConjugatedDerivativeCurve_continuous parameters lower bounded tuple 1 grade).sub
    ((hilbertMeanFree parameters).continuous.comp_continuousOn
      (tupleConjugatedPhysicalRowCurve_smooth parameters length compact lower positive bounded state tuple 0 grade).continuousOn)

theorem tupleConjugatedG3Curve_continuous (grade : ℕ) :
    ContinuousOn (tupleConjugatedG3Curve parameters length compact lower positive bounded state tuple grade) (Icc lower 1) := by
  have first := tupleConjugatedDerivativeCurve_continuous parameters lower bounded tuple 0 grade
  have second := (reciprocalRadius_smooth lower positive).continuousOn.smul
    (tupleWeightedCurve_smooth parameters lower tuple 0 grade).continuousOn
  have third := (continuousOn_const (c := (length : ℂ)⁻¹)).smul
    ((physicalAngularPrimitive parameters).continuous.comp_continuousOn
      ((hilbertFrequencyOperator parameters 1 (some true)).continuous.comp_continuousOn
        (tupleConjugatedPhysicalRowCurve_smooth parameters length compact lower positive bounded state tuple 1 (grade+1)).continuousOn))
  have fourth := (reciprocalRadius_smooth lower positive).continuousOn.smul
    (tupleConjugatedPhysicalRowCurve_smooth parameters length compact lower positive bounded state tuple 2 grade).continuousOn
  exact ((first.add second).add third).add fourth

theorem tupleConjugatedF1Curve_coefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    tupleConjugatedF1Curve parameters length compact lower positive bounded state tuple grade radius.val mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ) •
          originalTupleF1 parameters length compact lower positive state tuple radius mode) := by
  change tupleConjugatedDerivativeCurve parameters lower tuple 1 grade radius.val mode -
    (if mode.1 = 0 then (0 : ℂ) else 1) • tupleConjugatedPhysicalRowCurve parameters length compact lower positive bounded state tuple 0 grade radius.val mode = _
  rw [tupleConjugatedDerivativeCurve_coefficient parameters lower bounded tuple 1 grade radius.val radius.property mode,
    tupleConjugatedPhysicalRowCurve_coefficient,tuplePhysicalRowTrace_first]
  unfold originalTupleF1
  rw [smul_sub,smul_sub]
  congr 1
  exact (smul_comm _ _ _).trans (congrArg (fun v : ComplexEuclidean 1 =>
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • v) (smul_comm _ _ _))

theorem originalTupleG3_physicalRows (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    originalTupleG3 parameters length compact lower positive state tuple radius mode =
      ((derivWithin (fun location => originalPhysicalCoefficient (tuple.val 0) location mode) (Icc lower 1) radius.val +
        (radius.val : ℂ)⁻¹ • originalPhysicalCoefficient (tuple.val 0) radius.val mode) +
        (length : ℂ)⁻¹ • (angularInverseMultiplier mode • (frequencyNumerator (some true) mode •
          negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
            (tuplePhysicalRowTrace parameters length compact lower positive state tuple radius 1) mode))) +
        (radius.val : ℂ)⁻¹ • negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
          (tuplePhysicalRowTrace parameters length compact lower positive state tuple radius 2) mode := by
  have c := tuplePhysicalRowTrace_c_derivative parameters length compact lower positive state tuple radius mode
  have rv := tuplePhysicalRowTrace_rV parameters length compact lower positive state tuple radius
  unfold originalTupleG3
  rw [rv,negativeTraceCoefficient_smul,inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (positive.trans_le radius.property.1).ne')]
  congr 1
  congr 1
  rw [c]
  by_cases zero : mode.1 = 0
  · simp [angularInverseMultiplier,angularMeanFreeMultiplier,zero,frequencyNumerator]
  · simp only [angularInverseMultiplier,angularMeanFreeMultiplier,if_neg zero,one_smul,smul_smul]
    ext component
    simp only [PiLp.smul_apply,smul_eq_mul,frequencyNumerator]
    field_simp [mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero)]


theorem tupleConjugatedG3Curve_coefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    tupleConjugatedG3Curve parameters length compact lower positive bounded state tuple grade radius.val mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ) •
          originalTupleG3 parameters length compact lower positive state tuple radius mode) := by
  have axial : hilbertFrequencyOperator parameters 1 (some true)
      (tupleConjugatedPhysicalRowCurve parameters length compact lower positive bounded state tuple 1 (grade+1) radius.val) mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        (frequencyNumerator (some true) mode • ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ) •
          negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
            (tuplePhysicalRowTrace parameters length compact lower positive state tuple radius 1) mode)) := by
    rw [hilbertFrequencyOperator_apply,tupleConjugatedPhysicalRowCurve_coefficient]
    exact frequencyRatio_weighted (some true) mode grade _
  change ((tupleConjugatedDerivativeCurve parameters lower tuple 0 grade radius.val mode +
    (radius.val : ℂ)⁻¹ • tupleWeightedCurve parameters lower tuple 0 grade radius.val mode) +
    (length : ℂ)⁻¹ • physicalAngularPrimitive parameters _ mode) +
    (radius.val : ℂ)⁻¹ • tupleConjugatedPhysicalRowCurve parameters length compact lower positive bounded state tuple 2 grade radius.val mode = _
  rw [tupleConjugatedDerivativeCurve_coefficient parameters lower bounded tuple 0 grade radius.val radius.property mode,
    tupleWeightedCurve_coefficient parameters lower tuple 0 grade radius.val radius.property mode,
    physicalAngularPrimitive_apply,axial,tupleConjugatedPhysicalRowCurve_coefficient,
    originalTupleG3_physicalRows]
  ext component
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

end Grad.AnnularOriginalCoreRealization
