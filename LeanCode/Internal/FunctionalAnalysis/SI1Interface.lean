import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open MeasureTheory

namespace Grad.SchurKernel.Integral

def WeightedScalarGoal {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) : Prop :=
  ∀ (weight amplitude : Parameter → ℝ),
    (∀ᵐ parameter ∂measure, 0 ≤ weight parameter) →
    AEStronglyMeasurable amplitude measure → Integrable weight measure →
    Integrable (fun parameter => weight parameter * amplitude parameter ^ 2) measure →
    Integrable (fun parameter => weight parameter * amplitude parameter) measure ∧
      (∫ parameter, weight parameter * amplitude parameter ∂measure) ^ 2 ≤
        (∫ parameter, weight parameter ∂measure) *
          ∫ parameter, weight parameter * amplitude parameter ^ 2 ∂measure

def VectorRowGoal {Parameter Value : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
    (measure : Measure Parameter) : Prop :=
  ∀ (weight amplitude : Parameter → ℝ) (integrand : Parameter → Value),
    (∀ᵐ parameter ∂measure, 0 ≤ weight parameter) →
    AEStronglyMeasurable amplitude measure → Integrable weight measure →
    Integrable (fun parameter => weight parameter * amplitude parameter ^ 2) measure →
    AEStronglyMeasurable integrand measure →
    (∀ᵐ parameter ∂measure, ‖integrand parameter‖ ≤ weight parameter * amplitude parameter) →
    Integrable integrand measure ∧
      ‖∫ parameter, integrand parameter ∂measure‖ ^ 2 ≤
        (∫ parameter, weight parameter ∂measure) *
          ∫ parameter, weight parameter * amplitude parameter ^ 2 ∂measure

def CoefficientRowGoal {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) : Prop :=
  ∀ (inputDimension outputDimension : ℕ)
    (coefficient : Parameter → EuclideanSpace ℂ (Fin inputDimension) →L[ℂ]
      EuclideanSpace ℂ (Fin outputDimension))
    (field : Parameter → EuclideanSpace ℂ (Fin inputDimension)) (weight : Parameter → ℝ),
    (∀ᵐ parameter ∂measure, 0 ≤ weight parameter) →
    AEStronglyMeasurable coefficient measure → AEStronglyMeasurable field measure →
    Integrable weight measure →
    Integrable (fun parameter => weight parameter * ‖field parameter‖ ^ 2) measure →
    (∀ᵐ parameter ∂measure, ‖coefficient parameter‖ ≤ weight parameter) →
    Integrable (fun parameter => coefficient parameter (field parameter)) measure ∧
      ‖∫ parameter, coefficient parameter (field parameter) ∂measure‖ ^ 2 ≤
        (∫ parameter, weight parameter ∂measure) *
          ∫ parameter, weight parameter * ‖field parameter‖ ^ 2 ∂measure

end Grad.SchurKernel.Integral

#check MeasureTheory.memLp_two_iff_integrable_sq
#check MeasureTheory.MemLp.coeFn_toLp
#check MeasureTheory.MemLp.mul'
#check MeasureTheory.memLp_one_iff_integrable
#check MeasureTheory.L2.inner_def
#check Real.inner_apply
#check real_inner_mul_inner_self_le
#check Real.sq_sqrt
#check Real.mul_self_sqrt
#check Continuous.comp_aestronglyMeasurable
#check Continuous.comp_aestronglyMeasurable₂
#check MeasureTheory.Integrable.mono'
#check MeasureTheory.integral_mono_ae
#check MeasureTheory.norm_integral_le_integral_norm
#check ContinuousLinearMap.le_opNorm

section
variable {Parameter : Type*} [MeasurableSpace Parameter] (measure : Measure Parameter)
variable (first second : Parameter → ℝ) (firstLp : MemLp first 2 measure)
  (secondLp : MemLp second 2 measure)
#check (secondLp.mul' firstLp : MemLp (fun parameter => first parameter * second parameter) 1 measure)
#check (firstLp.toLp first : Lp ℝ 2 measure)
end
