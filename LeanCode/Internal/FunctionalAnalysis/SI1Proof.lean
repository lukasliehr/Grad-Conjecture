import SI1Interface
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

noncomputable section

open MeasureTheory

namespace Grad.SchurKernel.Integral

variable {Parameter : Type*} [MeasurableSpace Parameter]

theorem realLp_inner_eq_integral_mul {measure : Measure Parameter}
    (first second : Parameter → ℝ) (firstLp : MemLp first 2 measure)
    (secondLp : MemLp second 2 measure) :
    inner ℝ (firstLp.toLp first) (secondLp.toLp second) =
      ∫ parameter, first parameter * second parameter ∂measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [firstLp.coeFn_toLp, secondLp.coeFn_toLp]
    with parameter firstLaw secondLaw
  rw [Real.inner_apply, firstLaw, secondLaw]

theorem integral_mul_sq_le {measure : Measure Parameter}
    (first second : Parameter → ℝ) (firstLp : MemLp first 2 measure)
    (secondLp : MemLp second 2 measure) :
    (∫ parameter, first parameter * second parameter ∂measure) ^ 2 ≤
      (∫ parameter, first parameter ^ 2 ∂measure) *
        ∫ parameter, second parameter ^ 2 ∂measure := by
  have bound := real_inner_mul_inner_self_le (firstLp.toLp first) (secondLp.toLp second)
  rw [realLp_inner_eq_integral_mul first second firstLp secondLp,
    realLp_inner_eq_integral_mul first first firstLp firstLp,
    realLp_inner_eq_integral_mul second second secondLp secondLp] at bound
  simpa only [← pow_two] using bound

theorem weighted_scalar (measure : Measure Parameter) : WeightedScalarGoal measure := by
  intro weight amplitude weightNonnegative amplitudeMeasurable weightIntegrable squareIntegrable
  let rootWeight : Parameter → ℝ := fun parameter => Real.sqrt (weight parameter)
  let rootAmplitude : Parameter → ℝ := fun parameter => rootWeight parameter * amplitude parameter
  have rootMeasurable : AEStronglyMeasurable rootWeight measure :=
    Real.continuous_sqrt.comp_aestronglyMeasurable weightIntegrable.aestronglyMeasurable
  have rootSquare : (fun parameter => rootWeight parameter ^ 2) =ᵐ[measure] weight := by
    filter_upwards [weightNonnegative] with parameter nonnegative
    exact Real.sq_sqrt nonnegative
  have rootLp : MemLp rootWeight 2 measure :=
    (memLp_two_iff_integrable_sq rootMeasurable).mpr (weightIntegrable.congr rootSquare.symm)
  have weightedSquare : (fun parameter => rootAmplitude parameter ^ 2) =ᵐ[measure]
      fun parameter => weight parameter * amplitude parameter ^ 2 := by
    filter_upwards [rootSquare] with parameter squareLaw
    dsimp only [rootAmplitude]
    rw [mul_pow, squareLaw]
  have rootAmplitudeLp : MemLp rootAmplitude 2 measure :=
    (memLp_two_iff_integrable_sq (rootMeasurable.mul amplitudeMeasurable)).mpr
      (squareIntegrable.congr weightedSquare.symm)
  have productLaw : (fun parameter => rootWeight parameter * rootAmplitude parameter) =ᵐ[measure]
      fun parameter => weight parameter * amplitude parameter := by
    filter_upwards [weightNonnegative] with parameter nonnegative
    dsimp only [rootAmplitude, rootWeight]
    rw [← mul_assoc, Real.mul_self_sqrt nonnegative]
  have productIntegrable : Integrable (fun parameter => rootWeight parameter * rootAmplitude parameter)
      measure := memLp_one_iff_integrable.mp (rootAmplitudeLp.mul' rootLp)
  refine ⟨productIntegrable.congr productLaw, ?_⟩
  have bound := integral_mul_sq_le rootWeight rootAmplitude rootLp rootAmplitudeLp
  rwa [integral_congr_ae productLaw, integral_congr_ae rootSquare,
    integral_congr_ae weightedSquare] at bound

theorem vector_row {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    [CompleteSpace Value] (measure : Measure Parameter) : VectorRowGoal (Value := Value) measure := by
  intro weight amplitude integrand weightNonnegative amplitudeMeasurable weightIntegrable
    squareIntegrable integrandMeasurable domination
  obtain ⟨scalarIntegrable, scalarBound⟩ := weighted_scalar measure weight amplitude
    weightNonnegative amplitudeMeasurable weightIntegrable squareIntegrable
  have integrandIntegrable : Integrable integrand measure :=
    scalarIntegrable.mono' integrandMeasurable domination
  refine ⟨integrandIntegrable, ?_⟩
  have normBound : ‖∫ parameter, integrand parameter ∂measure‖ ≤
      ∫ parameter, weight parameter * amplitude parameter ∂measure :=
    (norm_integral_le_integral_norm integrand).trans
      (integral_mono_ae integrandIntegrable.norm scalarIntegrable domination)
  exact (pow_le_pow_left₀ (norm_nonneg _) normBound 2).trans scalarBound

theorem coefficient_row (measure : Measure Parameter) : CoefficientRowGoal measure := by
  intro inputDimension outputDimension coefficient field weight weightNonnegative
    coefficientMeasurable fieldMeasurable weightIntegrable squareIntegrable domination
  have evaluationMeasurable :
      AEStronglyMeasurable (fun parameter => coefficient parameter (field parameter)) measure :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (coefficientMeasurable.prodMk fieldMeasurable)
  apply vector_row measure weight (fun parameter => ‖field parameter‖)
    (fun parameter => coefficient parameter (field parameter)) weightNonnegative
    fieldMeasurable.norm weightIntegrable squareIntegrable evaluationMeasurable
  filter_upwards [domination] with parameter normDomination
  exact ((coefficient parameter).le_opNorm (field parameter)).trans
    (mul_le_mul_of_nonneg_right normDomination (norm_nonneg _))

end Grad.SchurKernel.Integral
