import ASG15LiteralCompletedEnergy

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

/-- Literal AH10 energy, with the original phase and the genuine weak
radial derivative of the conjugated physical coefficient. -/
def physicalSourceEnergy (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) : ℝ :=
  ∑' mode : ℤ × ℤ, splitTangentialWeight angular cell mode ^ 2 *
    (∫ radius in lower..1, radius *
      (‖Real.exp (radialPhase parameters radius mode.2) •
        annularSourceCoefficient parameters dimension lower positive bounded angular cell field mode radius‖ ^ 2 +
       ‖annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 1 radius‖ ^ 2))

/-- Literal AH11 endpoint energy in H_e^(j,s). -/
def physicalEndpointEnergy (parameters : PhaseParameters) (dimension : ℕ) (radius : ℝ)
    (angular cell : ℕ) (field : AnnularEndpointTrace parameters dimension radius angular cell) : ℝ :=
  ∑' mode : ℤ × ℤ,
    (Real.exp (2 * radialPhase parameters radius mode.2) *
      (1 + |(mode.1 : ℝ)|) ^ (2 * angular) * (1 + |(mode.2 : ℝ)|) ^ (2 * cell)) *
    ‖annularEndpointCoefficient parameters dimension radius angular cell field mode‖ ^ 2

/-- AH10 completion prerequisite: full complete Fourier graph, dense actual
physical C∞ core, faithful actual bulk, literal energy and genuine derivative.
No arbitrary weak-pair-to-completion converse is assumed or claimed. -/
theorem actualAH10_completion (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ) :
    DenseRange (physicalSourceCore parameters dimension lower angular cell) ∧
    Function.Injective (annularSourceCoordinate parameters dimension lower angular cell 0) ∧
    ∀ field : AnnularSourceH1 parameters dimension lower angular cell,
      ‖field‖ ^ 2 = physicalSourceEnergy parameters dimension lower positive bounded.le angular cell field ∧
      ∀ mode : ℤ × ℤ, CollarWeakDerivative lower
        (annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 0)
        (annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 1) := by
  refine ⟨physicalSourceCore_denseRange parameters dimension lower angular cell,
    annularSource_bulk_injective parameters dimension lower positive bounded.le angular cell, ?_⟩
  intro field
  exact ⟨annularSource_literal_norm_sq parameters dimension lower positive bounded.le angular cell field,
    annularConjugatedCoordinate_weak parameters dimension lower positive bounded.le angular cell field⟩

/-- AH11 at BOTH a and1. The same graph controls the exact physical endpoint
norm, with a constant independent of phase parameters and polynomial grades. -/
theorem actualAH11_both_endpoints (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    ∀ endpoint : Fin 2,
      ‖annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field‖ ≤
        sourceEndpointConstant lower * ‖field‖ ∧
      ‖annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field‖ ^ 2 =
        physicalEndpointEnergy parameters dimension (radialEndpointRadius lower endpoint) angular cell
          (annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field) := by
  intro endpoint
  exact ⟨annularSourceTrace_bound parameters dimension lower positive bounded angular cell endpoint field,
    annularEndpointTrace_norm_sq parameters dimension (radialEndpointRadius lower endpoint) angular cell _⟩

/-- The trace maps are the unique continuous extensions of literal physical
endpoint evaluation on the dense finite Fourier smooth radial core. -/
theorem actualAH11_physical_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) :
    ∀ (endpoint : Fin 2) (mode : ℤ × ℤ),
      annularEndpointCoefficient parameters dimension (radialEndpointRadius lower endpoint) angular cell
        (annularSourceTrace parameters dimension lower positive bounded angular cell endpoint
          (physicalSourceCore parameters dimension lower angular cell core)) mode =
        (core mode).val.val.1 (radialEndpointRadius lower endpoint) :=
  fun endpoint mode => annularSourceTrace_physical_core parameters dimension lower positive bounded angular cell endpoint core mode

/-- The exact source, derivative and both endpoint constructions commute
with the natural grade inclusions at unchanged analytic width. -/
theorem actualAH10_AH11_grade_compatibility (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularSourceH1 parameters dimension lower highAngular highCell) :
    (∀ mode : ℤ × ℤ,
      annularConjugatedMode parameters dimension lower positive bounded.le lowAngular lowCell
        (annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) mode =
      annularConjugatedMode parameters dimension lower positive bounded.le highAngular highCell field mode) ∧
    (∀ endpoint : Fin 2,
      annularSourceTrace parameters dimension lower positive bounded lowAngular lowCell endpoint
        (annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) =
      annularEndpointInclusion parameters dimension (radialEndpointRadius lower endpoint)
        lowAngular lowCell highAngular highCell angularLe cellLe
        (annularSourceTrace parameters dimension lower positive bounded highAngular highCell endpoint field)) :=
  ⟨fun mode => annularConjugatedMode_inclusion parameters dimension lower positive bounded.le
    lowAngular lowCell highAngular highCell angularLe cellLe field mode,
   fun endpoint => annularSourceInclusion_trace parameters dimension lower positive bounded endpoint
    lowAngular lowCell highAngular highCell angularLe cellLe field⟩

end Grad.AnnularSourceGraph
