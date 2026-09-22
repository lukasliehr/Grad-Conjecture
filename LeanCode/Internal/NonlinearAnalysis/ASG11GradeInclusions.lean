import ASG10PhysicalEndpointTrace

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

def sourceGradeRatio (lowAngular lowCell highAngular highCell : ℕ) (mode : ℤ × ℤ) : ℝ :=
  splitTangentialWeight lowAngular lowCell mode / splitTangentialWeight highAngular highCell mode

theorem sourceGradeRatio_pos (lowAngular lowCell highAngular highCell : ℕ) (mode : ℤ × ℤ) :
    0 < sourceGradeRatio lowAngular lowCell highAngular highCell mode :=
  div_pos (splitTangentialWeight_pos _ _ _) (splitTangentialWeight_pos _ _ _)

theorem sourceGradeRatio_le_one (lowAngular lowCell highAngular highCell : ℕ)
    (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell) (mode : ℤ × ℤ) :
    sourceGradeRatio lowAngular lowCell highAngular highCell mode ≤ 1 := by
  apply (div_le_one (splitTangentialWeight_pos highAngular highCell mode)).2
  unfold splitTangentialWeight
  exact mul_le_mul (pow_le_pow_right₀ (by linarith [abs_nonneg (mode.1 : ℝ)]) angularLe)
    (pow_le_pow_right₀ (by linarith [abs_nonneg (mode.2 : ℝ)]) cellLe) (by positivity) (by positivity)

def sourceGradeFamily (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (lowAngular lowCell highAngular highCell : ℕ) (mode : ℤ × ℤ) : Value →L[ℝ] Value :=
  sourceGradeRatio lowAngular lowCell highAngular highCell mode • ContinuousLinearMap.id ℝ Value

theorem sourceGradeFamily_bound (Value : Type*) [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular)
    (cellLe : lowCell ≤ highCell) (mode : ℤ × ℤ) (value : Value) :
    ‖sourceGradeFamily Value lowAngular lowCell highAngular highCell mode value‖ ≤ 1 * ‖value‖ := by
  change ‖sourceGradeRatio lowAngular lowCell highAngular highCell mode • value‖ ≤ 1 * ‖value‖
  rw [norm_smul, Real.norm_of_nonneg (sourceGradeRatio_pos _ _ _ _ _).le]
  exact mul_le_mul_of_nonneg_right (sourceGradeRatio_le_one _ _ _ _ angularLe cellLe mode) (norm_nonneg _)

/-- Natural higher-grade inclusion, without a change of analytic width. -/
def annularSourceInclusion (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell) :
    AnnularSourceH1 parameters dimension lower highAngular highCell →L[ℝ]
      AnnularSourceH1 parameters dimension lower lowAngular lowCell :=
  lpTwoMap (sourceGradeFamily (WeightedRadialH1 dimension lower) lowAngular lowCell highAngular highCell)
    1 zero_le_one (sourceGradeFamily_bound _ _ _ _ _ angularLe cellLe)

theorem annularSourceInclusion_apply (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularSourceH1 parameters dimension lower highAngular highCell) (mode : ℤ × ℤ) :
    annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field mode =
      sourceGradeRatio lowAngular lowCell highAngular highCell mode • field mode := rfl

theorem annularSourceInclusion_bound (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularSourceH1 parameters dimension lower highAngular highCell) :
    ‖annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field‖ ≤ ‖field‖ := by
  unfold annularSourceInclusion
  simpa only [one_mul] using lpTwoMap_bound
    (sourceGradeFamily (WeightedRadialH1 dimension lower) lowAngular lowCell highAngular highCell)
    1 zero_le_one (sourceGradeFamily_bound _ _ _ _ _ angularLe cellLe) field

theorem annularSourceInclusion_injective (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell) :
    Function.Injective (annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe) := by
  intro first second same
  apply Subtype.ext
  funext mode
  have pointwise := congrArg (fun field : AnnularSourceH1 parameters dimension lower lowAngular lowCell => field mode) same
  rw [annularSourceInclusion_apply, annularSourceInclusion_apply] at pointwise
  exact (smul_right_injective _ (sourceGradeRatio_pos _ _ _ _ _).ne') pointwise

def annularEndpointInclusion (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell) :
    AnnularEndpointTrace parameters dimension radius highAngular highCell →L[ℝ]
      AnnularEndpointTrace parameters dimension radius lowAngular lowCell :=
  lpTwoMap (sourceGradeFamily (ComplexEuclidean dimension) lowAngular lowCell highAngular highCell)
    1 zero_le_one (sourceGradeFamily_bound _ _ _ _ _ angularLe cellLe)

theorem annularEndpointInclusion_apply (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularEndpointTrace parameters dimension radius highAngular highCell) (mode : ℤ × ℤ) :
    annularEndpointInclusion parameters dimension radius lowAngular lowCell highAngular highCell angularLe cellLe field mode =
      sourceGradeRatio lowAngular lowCell highAngular highCell mode • field mode := rfl

/-- Both endpoint traces commute with the natural inclusions. -/
theorem annularSourceInclusion_trace (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularSourceH1 parameters dimension lower highAngular highCell) :
    annularSourceTrace parameters dimension lower positive bounded lowAngular lowCell endpoint
      (annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) =
    annularEndpointInclusion parameters dimension (radialEndpointRadius lower endpoint)
      lowAngular lowCell highAngular highCell angularLe cellLe
      (annularSourceTrace parameters dimension lower positive bounded highAngular highCell endpoint field) := by
  apply Subtype.ext
  funext mode
  rw [annularSourceTrace_apply, annularSourceInclusion_apply, annularEndpointInclusion_apply,
    annularSourceTrace_apply, map_smul]

theorem sourceGradeRatio_mul_weight (parameters : PhaseParameters)
    (lowAngular lowCell highAngular highCell : ℕ) (mode : ℤ × ℤ) (radius : ℝ) :
    sourceGradeRatio lowAngular lowCell highAngular highCell mode *
      annularConjugatingWeight parameters highAngular highCell mode radius =
      annularConjugatingWeight parameters lowAngular lowCell mode radius := by
  unfold sourceGradeRatio annularConjugatingWeight
  rw [← mul_assoc, div_mul_cancel₀ _ (splitTangentialWeight_pos highAngular highCell mode).ne']

/-- The same physical C∞ source has compatible representatives at every grade. -/
theorem annularSourceInclusion_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) :
    annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe
      (physicalSourceCore parameters dimension lower highAngular highCell core) =
      physicalSourceCore parameters dimension lower lowAngular lowCell core := by
  apply Subtype.ext
  funext mode
  rw [annularSourceInclusion_apply, physicalSourceCore_apply, physicalSourceCore_apply, ← map_smul]
  congr 1
  apply smoothRadialCore_ext
  intro radius
  change sourceGradeRatio lowAngular lowCell highAngular highCell mode •
    (annularConjugatingWeight parameters highAngular highCell mode radius • (core mode).val.val.1 radius) =
      annularConjugatingWeight parameters lowAngular lowCell mode radius • (core mode).val.val.1 radius
  rw [smul_smul, sourceGradeRatio_mul_weight]

end Grad.AnnularSourceGraph
