import ASG44InsertedContinuousRepresentative

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

private theorem endpointReal_smul (dimension : ℕ) (scalar : ℝ) (value : ComplexEuclidean dimension) :
    scalar • value = (scalar : ℂ) • value :=
  (IsScalarTower.algebraMap_smul ℂ scalar value).symm

def sourceAngularRatio (mode : ℤ × ℤ) : ℂ :=
  (Complex.I * (mode.1 : ℂ)) / ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ)

theorem sourceAngularRatio_bound (mode : ℤ × ℤ) : ‖sourceAngularRatio mode‖ ≤ 1 := by
  have positive : 0 < 1 + |(mode.1 : ℝ)| := by positivity
  rw [sourceAngularRatio, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg positive.le]
  have castNorm : ‖(mode.1 : ℂ)‖ = |(mode.1 : ℝ)| := by norm_cast
  rw [castNorm, div_le_one positive]
  linarith

/-- The actual angular Fourier generator maps j=1 endpoint sources to
j=0, preserving the same inserted total grade and original phase. -/
def totalEndpointAngular (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ) (cell grade : ℕ) :
    AnnularTotalEndpointTrace parameters dimension radius 1 cell grade →L[ℝ]
      AnnularTotalEndpointTrace parameters dimension radius 0 cell grade :=
  (sequenceMultiplier sourceAngularRatio 1 zero_le_one sourceAngularRatio_bound).restrictScalars ℝ

theorem totalEndpointAngular_bound (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ) (cell grade : ℕ)
    (field : AnnularTotalEndpointTrace parameters dimension radius 1 cell grade) :
    ‖totalEndpointAngular parameters dimension radius cell grade field‖ ≤ ‖field‖ := by
  change ‖sequenceMultiplierValue sourceAngularRatio 1 zero_le_one sourceAngularRatio_bound field‖ ≤ _
  exact (sequenceMultiplierValue_bound _ 1 zero_le_one sourceAngularRatio_bound field).trans_eq (one_mul _)

theorem totalEndpointWeight_angular_one (parameters : PhaseParameters) (cell grade : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) :
    totalEndpointWeight parameters 1 cell grade mode radius =
      (1 + |(mode.1 : ℝ)|) * totalEndpointWeight parameters 0 cell grade mode radius := by
  unfold totalEndpointWeight sourceInsertedWeight splitTangentialWeight
  simp only [pow_one, pow_zero, one_mul]
  ring

theorem totalEndpointAngular_coefficient (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ) (cell grade : ℕ)
    (field : AnnularTotalEndpointTrace parameters dimension radius 1 cell grade) (mode : ℤ × ℤ) :
    totalEndpointCoefficient parameters dimension radius 0 cell grade
      (totalEndpointAngular parameters dimension radius cell grade field) mode =
      (Complex.I * (mode.1 : ℂ)) • totalEndpointCoefficient parameters dimension radius 1 cell grade field mode := by
  have raw : totalEndpointAngular parameters dimension radius cell grade field mode =
      sourceAngularRatio mode • field mode := by
    have result := sequenceMultiplier_apply sourceAngularRatio 1 zero_le_one sourceAngularRatio_bound field mode
    simpa only [totalEndpointAngular, ContinuousLinearMap.coe_restrictScalars'] using result
  simp only [totalEndpointCoefficient, raw, endpointReal_smul, Complex.ofReal_inv]
  change (totalEndpointWeight parameters 0 cell grade mode radius : ℂ)⁻¹ •
      (sourceAngularRatio mode • field mode) =
    (Complex.I * (mode.1 : ℂ)) • ((totalEndpointWeight parameters 1 cell grade mode radius : ℂ)⁻¹ • field mode)
  rw [smul_smul, smul_smul, totalEndpointWeight_angular_one]
  congr 1
  simp only [sourceAngularRatio, Complex.ofReal_mul, mul_inv, div_eq_mul_inv]
  ring

/-- Exact RF0 source endpoint consumer, obtained from the j=1 source graph. -/
def sourceRotationTrace (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (cell grade : ℕ) (endpoint : Fin 2) :
    AnnularTotalSourceH1 parameters dimension lower 1 cell grade →L[ℝ]
      AnnularTotalEndpointTrace parameters dimension (radialEndpointRadius lower endpoint) 0 cell grade :=
  (totalEndpointAngular parameters dimension (radialEndpointRadius lower endpoint) cell grade).comp
    (totalSourceTrace parameters dimension lower positive bounded 1 cell grade endpoint)

theorem sourceRotationTrace_bound (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (cell grade : ℕ) (endpoint : Fin 2)
    (field : AnnularTotalSourceH1 parameters dimension lower 1 cell grade) :
    ‖sourceRotationTrace parameters dimension lower positive bounded cell grade endpoint field‖ ≤
      sourceEndpointConstant lower * ‖field‖ :=
  (totalEndpointAngular_bound parameters dimension (radialEndpointRadius lower endpoint) cell grade _).trans
    (totalSourceTrace_bound parameters dimension lower positive bounded 1 cell grade endpoint field)

theorem sourceRotationTrace_coefficient (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (cell grade : ℕ) (endpoint : Fin 2)
    (field : AnnularTotalSourceH1 parameters dimension lower 1 cell grade) (mode : ℤ × ℤ) :
    totalEndpointCoefficient parameters dimension (radialEndpointRadius lower endpoint) 0 cell grade
      (sourceRotationTrace parameters dimension lower positive bounded cell grade endpoint field) mode =
    (Complex.I * (mode.1 : ℂ)) • totalEndpointCoefficient parameters dimension (radialEndpointRadius lower endpoint) 1 cell grade
      (totalSourceTrace parameters dimension lower positive bounded 1 cell grade endpoint field) mode :=
  totalEndpointAngular_coefficient parameters dimension (radialEndpointRadius lower endpoint) cell grade _ mode

end Grad.AnnularSourceGraph
