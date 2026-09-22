import AKI16ActualOriginalSmoothTuple
import AHS16OriginalRadiusForceGaugeConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower) (radius : Icc lower (1 : ℝ))

theorem tupleNegativeTrace_meanFree (slot : Fin 4) (mean : slot ≠ 2) :
    IsAngularMeanFree (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleNegativeTrace parameters lower positive tuple slot radius) := by
  intro cell
  rw [tupleNegativeTrace_coefficient]
  exact tuple.property.2 slot mean radius.val radius.property cell

theorem tupleDifferentiatedTrace_meanFree (slot : Fin 4) (mean : slot ≠ 2) (axis : Bool) :
    IsAngularMeanFree (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleDifferentiatedTrace parameters lower positive tuple slot axis radius) := by
  intro cell
  rw [tupleDifferentiatedTrace_coefficient, tuple.property.2 slot mean radius.val radius.property cell, smul_zero]

theorem tupleSevenInput_sourceDerivative :
    IsAngularDerivative (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleSevenInput parameters lower positive tuple radius 4)
      (tupleSevenInput parameters lower positive tuple radius 5) := by
  intro mode
  change negativeTraceCoefficient _ 0 0 (tupleDifferentiatedTrace parameters lower positive tuple 2 false radius) mode = _
  rw [tupleDifferentiatedTrace_coefficient]
  change frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 2) radius.val mode =
    (Complex.I * (mode.1 : ℂ)) • negativeTraceCoefficient _ 0 0 (tupleNegativeTrace parameters lower positive tuple 2 radius) mode
  rw [tupleNegativeTrace_coefficient]
  rfl

theorem tupleSevenInput_pressureDerivative :
    IsAngularDerivative (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
      (tupleNegativeTrace parameters lower positive tuple 0 radius)
      (tupleSevenInput parameters lower positive tuple radius 0) := by
  intro mode
  change negativeTraceCoefficient _ 0 0 (tupleDifferentiatedTrace parameters lower positive tuple 0 false radius) mode = _
  rw [tupleDifferentiatedTrace_coefficient, tupleNegativeTrace_coefficient]
  rfl

/-- The tuple's p is exactly the original corrected physical flux of its
once-only AH20 covariant reconstruction. -/
theorem tupleCovariantTrace_correctedPressure :
    radialCorrectedFluxTrace parameters length compact state.val.val (tupleRadius lower positive radius) 0 0
      (tupleCovariantTrace parameters length compact lower positive state tuple radius)
      ((radius.val : ℂ)⁻¹ • tupleNegativeTrace parameters lower positive tuple 1 radius) =
      tupleNegativeTrace parameters lower positive tuple 0 radius :=
  radialCovariantKernel_correctedFlux_eq parameters length compact state.val.val (tupleRadius lower positive radius)
    state.val.property (positive.trans_le radius.property.1) 0 0
    (tupleSevenInput parameters lower positive tuple radius)
    (tupleNegativeTrace parameters lower positive tuple 0 radius)
    (tupleNegativeTrace_meanFree parameters lower positive tuple radius 0 (by decide))
    (tupleSevenInput_pressureDerivative parameters lower positive tuple radius)
    (tupleSevenInput_scalarDerivative parameters lower positive tuple radius)

theorem tupleCovariantTrace_gauges :
    radialPhysicalGaugeMeans parameters length compact state.val.val (tupleRadius lower positive radius) 0 0
      (tupleCovariantTrace parameters length compact lower positive state tuple radius) = 0 :=
  radialCovariantKernel_gauged parameters length compact state.val.val (tupleRadius lower positive radius)
    state.val.property (positive.trans_le radius.property.1) 0 0
    (tupleSevenInput parameters lower positive tuple radius)
    (tupleNegativeTrace_meanFree parameters lower positive tuple radius 1 (by decide))

/-- Both original algebraic force rows hold for arbitrary literal tuples;
no radial equation or prescribed F1/G3 is a hypothesis. -/
theorem tupleCovariantTrace_forceRows :
    (-forceCoordinateTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 1
        (tupleRotatedCovariantTrace parameters length compact lower positive state tuple radius) -
      (2 : ℂ) • forceCoordinateTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 0
        (tupleCovariantTrace parameters length compact lower positive state tuple radius) +
      fullNegativeKernelAction _ 0 0 (radialForceKernel parameters length compact state.val.val (tupleRadius lower positive radius) 0 0)
        (tupleCovariantTrace parameters length compact lower positive state tuple radius) +
      tupleNormalizedInput parameters lower positive tuple radius 1 = tupleNormalizedInput parameters lower positive tuple radius 4) ∧
    (forceCoordinateTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 2
        (tupleRotatedCovariantTrace parameters length compact lower positive state tuple radius) +
      forceMeanFreeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0
        (fullNegativeKernelAction _ 0 0 (radialForceKernel parameters length compact state.val.val (tupleRadius lower positive radius) 1 0)
          (tupleCovariantTrace parameters length compact lower positive state tuple radius)) -
      (length : ℂ)⁻¹ • tupleNormalizedInput parameters lower positive tuple radius 2 =
        tupleNormalizedInput parameters lower positive tuple radius 6) := by
  have force := radialNormalizedCovariant_force_rows parameters length compact state.val.val (tupleRadius lower positive radius)
    state.val.property 0 0 (tupleNormalizedInput parameters lower positive tuple radius)
    (tupleSevenInput_supported parameters lower positive tuple radius)
    (radialNormalizedSevenInput_derivative parameters (tupleRadius lower positive radius) 0 0
      (tupleSevenInput parameters lower positive tuple radius) (tupleSevenInput_scalarDerivative parameters lower positive tuple radius))
    (tupleSevenInput_sourceDerivative parameters lower positive tuple radius)
    (tupleDifferentiatedTrace_meanFree parameters lower positive tuple radius 1 (by decide) true)
    (tupleNegativeTrace_meanFree parameters lower positive tuple radius 3 (by decide))
  simpa only [tupleCovariantTrace, tupleRotatedCovariantTrace, radialCovariantKernel, radialRotatedCovariantKernel,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, radialSevenSlotKernel_action,
    tupleNormalizedInput] using force

end Grad.AnnularOriginalSmoothCore
