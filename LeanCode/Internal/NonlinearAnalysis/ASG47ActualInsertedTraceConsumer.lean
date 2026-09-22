import ASG46InsertedPhysicalCore

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

/-- GRF10's actual endpoint operator is evaluation of the full continuous
Fourier representative at unchanged original phase and inserted total grade. -/
theorem actualGRF10_trace_eq_evaluation (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular grade : ℕ) (endpoint : Fin 2) :
    totalSourceTrace parameters dimension lower positive bounded angular 0 grade endpoint =
      (ContinuousMap.evalCLM ℝ
        ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩).comp
      (totalFourierSection parameters dimension lower positive bounded angular 0 grade) := by
  apply ContinuousLinearMap.ext
  intro field
  exact (totalFourierSection_endpoint parameters dimension lower positive bounded angular 0 grade field endpoint).symm

theorem actualGRF10_trace_opNorm (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular grade : ℕ) (endpoint : Fin 2) :
    ‖totalSourceTrace parameters dimension lower positive bounded angular 0 grade endpoint‖ ≤
      sourceEndpointConstant lower :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (totalSourceTrace_bound parameters dimension lower positive bounded angular 0 grade endpoint)

/-- Literal phase-conjugated evaluation law for arbitrary completed sources,
not only the dense core or separately attached endpoint coordinates. -/
theorem actualGRF10_physical_evaluation (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular grade : ℕ) (endpoint : Fin 2)
    (field : AnnularTotalSourceH1 parameters dimension lower angular 0 grade) (mode : ℤ × ℤ) :
    totalEndpointCoefficient parameters dimension (radialEndpointRadius lower endpoint) angular 0 grade
      (totalSourceTrace parameters dimension lower positive bounded angular 0 grade endpoint field) mode =
    (Real.exp (radialPhase parameters (radialEndpointRadius lower endpoint) mode.2))⁻¹ •
      totalConjugatedSection parameters dimension lower positive bounded angular 0 grade field mode
        ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩ := by
  rw [totalSourceTrace_representative, totalFourierSection_conjugated, smul_smul]
  congr 1
  unfold totalEndpointWeight
  field_simp [(sourceInsertedWeight_pos angular 0 grade mode).ne', (Real.exp_pos _).ne']

/-- Both source rows needed by physical reconstruction: F0 uses j=1, its
actual R trace uses j=0, and F2 uses j=0, all with the same inserted nu^t. -/
theorem actualSourcePair_endpoint_consumer (parameters : PhaseParameters) (forceDimension secondDimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ) (endpoint : Fin 2)
    (force : AnnularTotalSourceH1 parameters forceDimension lower 1 0 grade)
    (second : AnnularTotalSourceH1 parameters secondDimension lower 0 0 grade) :
    (‖totalSourceTrace parameters forceDimension lower positive bounded 1 0 grade endpoint force‖ ≤
      sourceEndpointConstant lower * ‖force‖) ∧
    (‖sourceRotationTrace parameters forceDimension lower positive bounded 0 grade endpoint force‖ ≤
      sourceEndpointConstant lower * ‖force‖) ∧
    (‖totalSourceTrace parameters secondDimension lower positive bounded 0 0 grade endpoint second‖ ≤
      sourceEndpointConstant lower * ‖second‖) ∧
    ∀ mode : ℤ × ℤ,
      totalEndpointCoefficient parameters forceDimension (radialEndpointRadius lower endpoint) 0 0 grade
        (sourceRotationTrace parameters forceDimension lower positive bounded 0 grade endpoint force) mode =
      (Complex.I * (mode.1 : ℂ)) •
        totalEndpointCoefficient parameters forceDimension (radialEndpointRadius lower endpoint) 1 0 grade
          (totalSourceTrace parameters forceDimension lower positive bounded 1 0 grade endpoint force) mode :=
  ⟨totalSourceTrace_bound parameters forceDimension lower positive bounded 1 0 grade endpoint force,
    sourceRotationTrace_bound parameters forceDimension lower positive bounded 0 grade endpoint force,
    totalSourceTrace_bound parameters secondDimension lower positive bounded 0 0 grade endpoint second,
    sourceRotationTrace_coefficient parameters forceDimension lower positive bounded 0 grade endpoint force⟩

end Grad.AnnularSourceGraph
