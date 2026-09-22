import ASG42InsertedSourceEnergy

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

def totalEndpointWeight (parameters : PhaseParameters) (angular cell grade : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) : ℝ :=
  sourceInsertedWeight angular cell grade mode * Real.exp (radialPhase parameters radius mode.2)

theorem totalEndpointWeight_pos (parameters : PhaseParameters) (angular cell grade : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) : 0 < totalEndpointWeight parameters angular cell grade mode radius :=
  mul_pos (sourceInsertedWeight_pos angular cell grade mode) (Real.exp_pos _)

def totalEndpointCoefficient (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ)
    (angular cell grade : ℕ) (field : AnnularTotalEndpointTrace parameters dimension radius angular cell grade)
    (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  (totalEndpointWeight parameters angular cell grade mode radius)⁻¹ • field mode

theorem totalEndpointCoefficient_normalization (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ)
    (angular cell grade : ℕ) (field : AnnularTotalEndpointTrace parameters dimension radius angular cell grade)
    (mode : ℤ × ℤ) :
    totalEndpointWeight parameters angular cell grade mode radius •
      totalEndpointCoefficient parameters dimension radius angular cell grade field mode = field mode := by
  rw [totalEndpointCoefficient, smul_smul, mul_inv_cancel₀ (totalEndpointWeight_pos parameters angular cell grade mode radius).ne', one_smul]

theorem totalEndpointWeight_sq (parameters : PhaseParameters) (angular cell grade : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) :
    totalEndpointWeight parameters angular cell grade mode radius ^ 2 =
      Real.exp (2 * radialPhase parameters radius mode.2) * annularFrequency mode.1 mode.2 ^ (2 * grade) *
        (1 + |(mode.1 : ℝ)|) ^ (2 * angular) * (1 + |(mode.2 : ℝ)|) ^ (2 * cell) := by
  rw [totalEndpointWeight, mul_pow, sourceInsertedWeight_sq]
  rw [show 2 * radialPhase parameters radius mode.2 =
    radialPhase parameters radius mode.2 + radialPhase parameters radius mode.2 by ring, Real.exp_add]
  ring

theorem totalEndpointTrace_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ)
    (angular cell grade : ℕ) (field : AnnularTotalEndpointTrace parameters dimension radius angular cell grade) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      (Real.exp (2 * radialPhase parameters radius mode.2) * annularFrequency mode.1 mode.2 ^ (2 * grade) *
        (1 + |(mode.1 : ℝ)|) ^ (2 * angular) * (1 + |(mode.2 : ℝ)|) ^ (2 * cell)) *
      ‖totalEndpointCoefficient parameters dimension radius angular cell grade field mode‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at formula
  rw [formula]
  apply tsum_congr
  intro mode
  conv_lhs => rw [← totalEndpointCoefficient_normalization parameters dimension radius angular cell grade field mode]
  rw [norm_smul, Real.norm_of_nonneg (totalEndpointWeight_pos parameters angular cell grade mode radius).le,
    mul_pow, totalEndpointWeight_sq]

/-- Exact source trace at total grade t; the normalized map is unchanged,
and its physical interpretation uses nu^t W at the same endpoint. -/
def totalSourceTrace (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ) (endpoint : Fin 2) :
    AnnularTotalSourceH1 parameters dimension lower angular cell grade →L[ℝ]
      AnnularTotalEndpointTrace parameters dimension (radialEndpointRadius lower endpoint) angular cell grade :=
  annularSourceTrace parameters dimension lower positive bounded angular cell endpoint

theorem totalSourceTrace_bound (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ) (endpoint : Fin 2)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) :
    ‖totalSourceTrace parameters dimension lower positive bounded angular cell grade endpoint field‖ ≤
      sourceEndpointConstant lower * ‖field‖ :=
  annularSourceTrace_bound parameters dimension lower positive bounded angular cell endpoint field

theorem totalNormalizeCore_value (parameters : PhaseParameters) (dimension angular cell grade : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) (radius : ℝ) :
    (totalNormalizeCore parameters dimension angular cell grade mode core).val.val.1 radius =
      totalEndpointWeight parameters angular cell grade mode radius • core.val.val.1 radius := by
  change annularFrequency mode.1 mode.2 ^ grade •
    (annularConjugatingWeight parameters angular cell mode radius • core.val.val.1 radius) = _
  rw [smul_smul]
  unfold annularConjugatingWeight totalEndpointWeight sourceInsertedWeight
  rw [mul_assoc]

theorem totalSourceTrace_physical_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell grade : ℕ) (endpoint : Fin 2)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    totalEndpointCoefficient parameters dimension (radialEndpointRadius lower endpoint) angular cell grade
      (totalSourceTrace parameters dimension lower positive bounded angular cell grade endpoint
        (physicalTotalSourceCore parameters dimension lower angular cell grade core)) mode =
      (core mode).val.val.1 (radialEndpointRadius lower endpoint) := by
  rw [totalEndpointCoefficient, totalSourceTrace, annularSourceTrace_apply, physicalTotalSourceCore_apply,
    weightedRadialTrace_core, totalNormalizeCore_value, smul_smul,
    inv_mul_cancel₀ (totalEndpointWeight_pos parameters angular cell grade mode _).ne', one_smul]

end Grad.AnnularSourceGraph
