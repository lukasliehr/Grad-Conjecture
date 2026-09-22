import AW3Leibniz

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers Grad.AnalyticWeights.Calculus
open scoped ContDiff BigOperators

namespace Grad.AnalyticWeights.Higher

universe valueUniverse

theorem weightRatio_exp (sigma gamma scale : ℝ) (output input : ℤ) (point : Spatial) :
    weightRatio sigma gamma scale output input point =
      Real.exp (phaseDifference sigma gamma scale output input point) := by
  rw [weightRatio, physicalWeight_exp, inverseWeight_exp, ← Real.exp_add]
  rfl

theorem weightRatio_contDiff (sigma gamma scale : ℝ) (output input : ℤ) :
    ContDiff ℝ ∞ (weightRatio sigma gamma scale output input) :=
  ((Grad.AnalyticWeights.Calculus.smoothGoal sigma gamma scale output).2.1.mul
    (Grad.AnalyticWeights.Calculus.smoothGoal sigma gamma scale input).2.2)

theorem ratioGoal : RatioGoal := by
  intro sigma gamma scale output input point
  refine ⟨mul_pos (by rw [physicalWeight_exp]; exact Real.exp_pos _)
      (by rw [inverseWeight_exp]; exact Real.exp_pos _),
    weightRatio_exp sigma gamma scale output input point,
    weightRatio_contDiff sigma gamma scale output input, ?_, ?_⟩
  · intro orthogonal
    unfold weightRatio
    rw [(Grad.AnalyticWeights.Calculus.orthogonalGoal sigma gamma scale output orthogonal point).2.1,
      (Grad.AnalyticWeights.Calculus.orthogonalGoal sigma gamma scale input orthogonal point).2.2]
  · intro gammaNonnegative scaleNonnegative rateNonnegative
    change Grad.AnalyticWeights.weight sigma gamma (scale * ‖point‖) output *
        (Grad.AnalyticWeights.weight sigma gamma (scale * ‖point‖) input)⁻¹ ≤ _
    simpa only [div_eq_mul_inv] using Grad.AnalyticWeights.physical_weight_ratio sigma gamma scale
      output input point gammaNonnegative scaleNonnegative rateNonnegative

theorem diagonalFormula : DiagonalGoal.{valueUniverse} := by
  intro Value _ _ sigma gamma scale cell rank word function point functionSmooth
  let scalarAction : ℝ →L[ℝ] Value →L[ℝ] Value := ContinuousLinearMap.lsmul ℝ ℝ
  have inverseSmooth : ContDiffAt ℝ ∞ (inverseWeight sigma gamma scale cell) point :=
    (Grad.AnalyticWeights.Calculus.smoothGoal sigma gamma scale cell).2.2.contDiffAt
  have expansion := ordered_bilinear_at scalarAction
    (inverseWeight sigma gamma scale cell) function point inverseSmooth functionSmooth rank word
  change physicalWeight sigma gamma scale cell point •
      orderedDerivative rank word
        (fun source => scalarAction (inverseWeight sigma gamma scale cell source) (function source)) point = _
  rw [expansion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro selected _
  change physicalWeight sigma gamma scale cell point •
      (selectedDerivative word selected (inverseWeight sigma gamma scale cell) point •
        selectedDerivative word selectedᶜ function point) = _
  rw [smul_smul]

theorem coefficientBinaryFormula (inputDimension outputDimension : ℕ) (sigma gamma scale : ℝ)
    (output input : ℤ) (rank : ℕ) (word : Fin rank → Fin 2)
    (coefficient : Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (point : Spatial) (coefficientSmooth : ContDiffAt ℝ ∞ coefficient point) :
    orderedDerivative rank word (conjugatedCoefficient sigma gamma scale output input coefficient) point =
      ∑ selected : Finset (Fin rank),
        selectedDerivative word selected (weightRatio sigma gamma scale output input) point •
          selectedDerivative word selectedᶜ coefficient point := by
  let scalarAction : ℝ →L[ℝ]
      (PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) →L[ℝ]
        (PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) :=
    ContinuousLinearMap.lsmul ℝ ℝ
  have expansion := ordered_bilinear_at scalarAction
    (weightRatio sigma gamma scale output input) coefficient point
      (weightRatio_contDiff sigma gamma scale output input).contDiffAt coefficientSmooth rank word
  exact expansion

theorem coefficientTernaryFormula (inputDimension outputDimension : ℕ) (sigma gamma scale : ℝ)
    (output input : ℤ) (rank : ℕ) (word : Fin rank → Fin 2)
    (coefficient : Spatial → PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension)
    (function : Spatial → PhysicalValue inputDimension) (point : Spatial)
    (coefficientSmooth : ContDiffAt ℝ ∞ coefficient point)
    (functionSmooth : ContDiffAt ℝ ∞ function point) :
    orderedDerivative rank word (fun source =>
        conjugatedCoefficient sigma gamma scale output input coefficient source (function source)) point =
      ∑ allocation : Fin rank → Fin 3,
        selectedDerivative word (allocationFiber allocation 0)
            (weightRatio sigma gamma scale output input) point •
          ((selectedDerivative word (allocationFiber allocation 1) coefficient point)
            (selectedDerivative word (allocationFiber allocation 2) function point)) := by
  let scalarAction : ℝ →L[ℝ] PhysicalValue outputDimension →L[ℝ] PhysicalValue outputDimension :=
    ContinuousLinearMap.lsmul ℝ ℝ
  let complexApply :
      (PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) →L[ℂ]
        PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension :=
    (ContinuousLinearMap.apply ℂ (PhysicalValue outputDimension)).flip
  let realApply :
      (PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension) →L[ℝ]
        PhysicalValue inputDimension →L[ℝ] PhysicalValue outputDimension :=
    complexApply.bilinearRestrictScalars ℝ
  have expansion := ordered_trilinear_at scalarAction realApply
    (weightRatio sigma gamma scale output input) coefficient function point
      (weightRatio_contDiff sigma gamma scale output input).contDiffAt
      coefficientSmooth functionSmooth rank word
  exact expansion

theorem coefficientGoal : CoefficientGoal :=
  ⟨fun inputDimension outputDimension sigma gamma scale output input rank word coefficient point smooth =>
      coefficientBinaryFormula inputDimension outputDimension sigma gamma scale output input rank word
        coefficient point smooth,
    fun inputDimension outputDimension sigma gamma scale output input rank word coefficient function point
      coefficientSmooth functionSmooth =>
      coefficientTernaryFormula inputDimension outputDimension sigma gamma scale output input rank word
        coefficient function point coefficientSmooth functionSmooth⟩

end Grad.AnalyticWeights.Higher
