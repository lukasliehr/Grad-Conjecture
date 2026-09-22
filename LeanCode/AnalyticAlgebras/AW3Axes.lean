import AW3Bounds

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers Grad.AnalyticWeights.Calculus
open scoped ContDiff BigOperators RealInnerProductSpace

namespace Grad.AnalyticWeights.Higher

theorem phaseDifference_hasFDerivAt (sigma gamma scale : ℝ) (output input : ℤ)
    (point : Spatial) :
    HasFDerivAt (phaseDifference sigma gamma scale output input)
      (phaseGradient gamma scale output point - phaseGradient gamma scale input point) point := by
  change HasFDerivAt
    (physicalPhase sigma gamma scale output - physicalPhase sigma gamma scale input) _ point
  exact (physicalPhase_hasFDerivAt sigma gamma scale output point).sub
    (physicalPhase_hasFDerivAt sigma gamma scale input point)

theorem weightRatio_hasFDerivAt (sigma gamma scale : ℝ) (output input : ℤ)
    (point : Spatial) :
    HasFDerivAt (weightRatio sigma gamma scale output input)
      (weightRatio sigma gamma scale output input point •
        (phaseGradient gamma scale output point - phaseGradient gamma scale input point)) point := by
  have exponential := (phaseDifference_hasFDerivAt sigma gamma scale output input point).exp
  have functionEquality : weightRatio sigma gamma scale output input =
      fun source => Real.exp (phaseDifference sigma gamma scale output input source) :=
    funext (weightRatio_exp sigma gamma scale output input)
  rw [functionEquality]
  exact exponential

theorem weightRatio_fderiv (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial) :
    fderiv ℝ (weightRatio sigma gamma scale output input) point =
      weightRatio sigma gamma scale output input point •
        (phaseGradient gamma scale output point - phaseGradient gamma scale input point) :=
  (weightRatio_hasFDerivAt sigma gamma scale output input point).fderiv

theorem phaseDifference_axis (sigma gamma scale : ℝ) (output input : ℤ)
    (first second : Spatial) :
    iteratedFDeriv ℝ 2 (phaseDifference sigma gamma scale output input) 0 ![first, second] =
      -gamma * scale ^ 2 *
        (Grad.CellWeights.cellWeight output ^ 2 - Grad.CellWeights.cellWeight input ^ 2) *
          inner ℝ first second := by
  change iteratedFDeriv ℝ 2
    (physicalPhase sigma gamma scale output - physicalPhase sigma gamma scale input) 0
      ![first, second] = _
  rw [iteratedFDeriv_sub_apply
    ((physicalPhase_contDiff sigma gamma scale output).of_le (by decide)).contDiffAt
    ((physicalPhase_contDiff sigma gamma scale input).of_le (by decide)).contDiffAt]
  simp only [sub_apply]
  rw [
    (Grad.AnalyticWeights.Calculus.axisGoal sigma gamma scale output).2.2.2 first second,
    (Grad.AnalyticWeights.Calculus.axisGoal sigma gamma scale input).2.2.2 first second]
  ring

theorem weightRatio_axis (sigma gamma scale : ℝ) (output input : ℤ)
    (first second : Spatial) :
    iteratedFDeriv ℝ 2 (weightRatio sigma gamma scale output input) 0 ![first, second] =
      weightRatio sigma gamma scale output input 0 *
        (-gamma * scale ^ 2 *
          (Grad.CellWeights.cellWeight output ^ 2 - Grad.CellWeights.cellWeight input ^ 2) *
            inner ℝ first second) := by
  rw [iteratedFDeriv_two_apply]
  have derivativeEquality :
      fderiv ℝ (weightRatio sigma gamma scale output input) = fun point =>
        weightRatio sigma gamma scale output input point •
          (phaseGradient gamma scale output point - phaseGradient gamma scale input point) :=
    funext (weightRatio_fderiv sigma gamma scale output input)
  rw [derivativeEquality]
  have productDerivative :=
    (weightRatio_hasFDerivAt sigma gamma scale output input 0).smul
      ((phaseGradient_hasFDerivAt gamma scale output 0).sub
        (phaseGradient_hasFDerivAt gamma scale input 0))
  have outputGradient : phaseGradient gamma scale output 0 = 0 := by
    rw [← physicalPhase_fderiv]
    exact physicalPhase_fderiv_axis sigma gamma scale output
  have inputGradient : phaseGradient gamma scale input 0 = 0 := by
    rw [← physicalPhase_fderiv]
    exact physicalPhase_fderiv_axis sigma gamma scale input
  have outputHessian : phaseHessian gamma scale output 0 first second =
      -gamma * scale ^ 2 * Grad.CellWeights.cellWeight output ^ 2 * inner ℝ first second := by
    rw [← physicalPhase_hessian]
    exact physicalPhase_hessian_axis sigma gamma scale output first second
  have inputHessian : phaseHessian gamma scale input 0 first second =
      -gamma * scale ^ 2 * Grad.CellWeights.cellWeight input ^ 2 * inner ℝ first second := by
    rw [← physicalPhase_hessian]
    exact physicalPhase_hessian_axis sigma gamma scale input first second
  change (fderiv ℝ
      (weightRatio sigma gamma scale output input •
        (phaseGradient gamma scale output - phaseGradient gamma scale input)) 0 first) second = _
  rw [productDerivative.fderiv]
  simp only [add_apply, smul_apply, sub_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [outputGradient, inputGradient]
  simp only [sub_self]
  rw [outputHessian, inputHessian]
  ring

theorem axisGoal : AxisGoal := by
  intro sigma gamma scale output input first second
  exact ⟨phaseDifference_axis sigma gamma scale output input first second,
    weightRatio_axis sigma gamma scale output input first second⟩

theorem zeroScaleGoal : ZeroScaleGoal := by
  intro sigma gamma rank positiveRank output input point
  have phaseConstant : phaseDifference sigma gamma 0 output input = fun _ : Spatial =>
      sigma * Grad.CellWeights.cellWeight output - sigma * Grad.CellWeights.cellWeight input := by
    funext source
    simp [phaseDifference, physicalPhase, Grad.AnalyticWeights.phase]
  have ratioConstant : weightRatio sigma gamma 0 output input = fun _ : Spatial =>
      Real.exp (sigma * Grad.CellWeights.cellWeight output -
        sigma * Grad.CellWeights.cellWeight input) := by
    funext source
    rw [weightRatio_exp]
    simp [phaseDifference, physicalPhase, Grad.AnalyticWeights.phase]
  have weightConstant : physicalWeight sigma gamma 0 output = fun _ : Spatial =>
      Real.exp (sigma * Grad.CellWeights.cellWeight output) := by
    funext source
    simp [physicalWeight, Grad.AnalyticWeights.weight, Grad.AnalyticWeights.phase]
  have inverseConstant : inverseWeight sigma gamma 0 output = fun _ : Spatial =>
      Real.exp (-sigma * Grad.CellWeights.cellWeight output) := by
    funext source
    rw [inverseWeight_exp]
    simp [physicalPhase, Grad.AnalyticWeights.phase]
  have rankNonzero : rank ≠ 0 := Nat.ne_of_gt positiveRank
  rw [phaseConstant, ratioConstant, weightConstant, inverseConstant,
    iteratedFDeriv_const_of_ne rankNonzero, iteratedFDeriv_const_of_ne rankNonzero,
    iteratedFDeriv_const_of_ne rankNonzero, iteratedFDeriv_const_of_ne rankNonzero]
  simp

end Grad.AnalyticWeights.Higher
