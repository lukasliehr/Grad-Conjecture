import ASG13CompletedPhysicalNorm

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

def phaseConjugatedCore (parameters : PhaseParameters) {dimension : ℕ}
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) : SmoothRadialCore dimension :=
  smoothRadialFunctionCore (phaseConjugatedCurve parameters mode core)
    (phaseConjugatedCurve_smooth parameters mode core)

theorem annularNormalizeCore_eq_phaseCore (parameters : PhaseParameters) (dimension angular cell : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) :
    annularNormalizeCore parameters dimension angular cell mode core =
      splitTangentialWeight angular cell mode • phaseConjugatedCore parameters mode core := by
  apply smoothRadialCore_ext
  intro radius
  exact annularNormalizeCore_value parameters dimension angular cell mode core radius

theorem annularConjugatedMode_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    annularConjugatedMode parameters dimension lower positive bounded angular cell
      (physicalSourceCore parameters dimension lower angular cell core) mode =
      collarH1Core (ComplexEuclidean dimension) lower (phaseConjugatedCore parameters mode (core mode)).val := by
  unfold annularConjugatedMode
  rw [physicalSourceCore_apply, weightedToOrdinary_core, annularNormalizeCore_eq_phaseCore]
  change (splitTangentialWeight angular cell mode)⁻¹ •
    collarH1Core (ComplexEuclidean dimension) lower
      (splitTangentialWeight angular cell mode • (phaseConjugatedCore parameters mode (core mode)).val) = _
  rw [map_smul, smul_smul, inv_mul_cancel₀ (splitTangentialWeight_pos angular cell mode).ne', one_smul]

theorem annularSourceCoefficient_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      annularSourceCoefficient parameters dimension lower positive bounded angular cell
        (physicalSourceCore parameters dimension lower angular cell core) mode radius =
        (core mode).val.val.1 radius := by
  unfold annularSourceCoefficient annularConjugatedCoordinate
  rw [annularConjugatedMode_core, collarH1Coordinate_core_zero]
  filter_upwards [(collarContinuous_memLp (ComplexEuclidean dimension) lower
    (phaseConjugatedCore parameters mode (core mode)).val.val.1).coeFn_toLp] with radius representative
  change collarContinuousL2 (ComplexEuclidean dimension) lower
    (phaseConjugatedCore parameters mode (core mode)).val.val.1 radius = _ at representative
  rw [representative]
  change (Real.exp (radialPhase parameters radius mode.2))⁻¹ •
    (Real.exp (radialPhase parameters radius mode.2) • (core mode).val.val.1 radius) = _
  rw [smul_smul, inv_mul_cancel₀ (Real.exp_pos _).ne', one_smul]

/-- Both the conjugated value and its genuine radial derivative are the same
physical coefficients after passage to any lower polynomial grade. -/
theorem annularConjugatedMode_inclusion (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularSourceH1 parameters dimension lower highAngular highCell) (mode : ℤ × ℤ) :
    annularConjugatedMode parameters dimension lower positive bounded lowAngular lowCell
      (annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) mode =
      annularConjugatedMode parameters dimension lower positive bounded highAngular highCell field mode := by
  unfold annularConjugatedMode
  rw [annularSourceInclusion_apply, map_smul, smul_smul]
  congr 1
  unfold sourceGradeRatio
  field_simp [(splitTangentialWeight_pos lowAngular lowCell mode).ne',
    (splitTangentialWeight_pos highAngular highCell mode).ne']

theorem annularSourceCoefficient_inclusion (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularSourceH1 parameters dimension lower highAngular highCell) (mode : ℤ × ℤ) (radius : ℝ) :
    annularSourceCoefficient parameters dimension lower positive bounded lowAngular lowCell
      (annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) mode radius =
      annularSourceCoefficient parameters dimension lower positive bounded highAngular highCell field mode radius := by
  unfold annularSourceCoefficient annularConjugatedCoordinate
  rw [annularConjugatedMode_inclusion]

end Grad.AnnularSourceGraph
