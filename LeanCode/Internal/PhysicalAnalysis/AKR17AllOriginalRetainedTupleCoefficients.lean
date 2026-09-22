import AKR16ExactOriginalRetainedLowFields

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

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (lengthPositive : 0 < length)

theorem tupleWeightedRetained_Xi (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive
      (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive) 0 radius mode =
      originalPhysicalCoefficient (tuple.val 1) radius.val mode := by
  by_cases high : 3 ≤ |mode.1|
  · exact tupleWeightedRetained_highXi parameters lower length positive bounded tuple ⟨mode,high⟩ lengthPositive radius
  by_cases low : |mode.1| = 1 ∨ |mode.1| = 2
  · simpa only [sameCoupledXiCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul] using
      tupleWeightedRetained_lowXi parameters lower length positive bounded tuple lengthPositive ⟨mode,low⟩ radius
  have zero : mode.1 = 0 := by apply abs_eq_zero.mp; have := abs_nonneg mode.1; omega
  have mean := tuple.property.2 1 (by decide) radius.val radius.property mode.2
  simpa only [sameCoupledXiCoefficient,dif_neg high,dif_neg low,← zero] using mean.symm

theorem tupleWeightedRetained_X (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
      (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive) 0 radius mode =
      (Complex.I * (mode.1 : ℂ)) • originalPhysicalCoefficient (tuple.val 0) radius.val mode := by
  by_cases high : 3 ≤ |mode.1|
  · exact tupleWeightedRetained_highX parameters lower length positive bounded tuple ⟨mode,high⟩ lengthPositive radius
  by_cases low : |mode.1| = 1 ∨ |mode.1| = 2
  · simpa only [sameCoupledXCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul] using
      tupleWeightedRetained_lowX parameters lower length positive bounded tuple lengthPositive ⟨mode,low⟩ radius
  have zero : mode.1 = 0 := by apply abs_eq_zero.mp; have := abs_nonneg mode.1; omega
  rw [sameCoupledXCoefficient,dif_neg high,dif_neg low]
  simp only [zero,Int.cast_zero,mul_zero,zero_smul]

theorem tupleWeightedRetained_pressure (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    originalPhysicalCoefficient (tuple.val 0) radius.val mode = angularInverseMultiplier mode •
      sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
        (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive) 0 radius mode := by
  rw [tupleWeightedRetained_X]
  by_cases zero : mode.1 = 0
  · have mean := tuple.property.2 0 (by decide) radius.val radius.property mode.2
    have exactMean : originalPhysicalCoefficient (tuple.val 0) radius.val mode = 0 := by simpa only [← zero] using mean
    simp only [exactMean,smul_zero]
  · rw [angularInverseMultiplier,if_neg zero,smul_smul,
      inv_mul_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero)),one_smul]

end Grad.AnnularOriginalCoreRealization
