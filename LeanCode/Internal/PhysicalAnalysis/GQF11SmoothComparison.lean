import GQF10CircularCancellation

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

variable {L sigma gamma ell : ℝ}

theorem projected_add_difference {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (projection : E →ₗ[ℂ] F) (base error : E) :
    projection (base + (2 : ℂ) • error) - projection base = (2 : ℂ) • projection error := by
  rw [map_add, map_smul]
  abel

theorem projected_flux_difference {E F G : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
    (projection : F →ₗ[ℂ] G) (derivative : E →ₗ[ℂ] F) (base error : E) :
    projection (derivative (-base + error)) - -(projection (derivative base)) =
      projection (derivative error) := by
  rw [map_add, map_neg, map_add, map_neg]
  abel

theorem third_difference {E : Type*} [AddCommGroup E] [Module ℂ E] (base error : E) :
    base - (2 : ℂ) • error - base = (-2 : ℂ) • error := by module

theorem actualRows_difference (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (state : CompensatedData L sigma gamma ell) :
    actualRows admissible data coherent state - circularRows admissible state =
      errorRows admissible data coherent (compensatedReconstruct admissible state) := by
  apply Prod.ext
  · exact projected_add_difference (apSmoothQrad L sigma gamma ell)
      (circularForceInner admissible state)
      (apSmoothMultiplier admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1
        (compensatedReconstruct admissible state))
  · apply Prod.ext
    · exact projected_flux_difference (apSmoothRemoveMean L sigma gamma ell 1)
        (apSmoothDiv admissible) (compensatedReconstruct admissible state)
        (apSmoothMultiplier admissible data.fluxDeviation coherent.2.2.2.2.1
          (compensatedReconstruct admissible state))
    · exact third_difference (circularThird admissible state)
        (apSmoothRemoveMean L sigma gamma ell 1
          (apSmoothMultiplier admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2
            (compensatedReconstruct admissible state)))

theorem circularRows_backward (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) :
    circularRows admissible (compensatedBackward L sigma gamma ell state) = circularRows admissible state :=
  circularRows_complement_cancellation admissible state state.2

theorem circularRows_transfer (admissible : Admissible L sigma gamma ell)
    {gauge : CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge)
    (state : circularCompensatedCore admissible) :
    circularRows admissible (smooth.equivalence state).val = circularRows admissible state.val := by
  have inverse := congrArg (fun core : circularCompensatedCore admissible => core.val)
    (smooth.left_inverse state)
  have backward := (smooth.backward (smooth.equivalence state)).symm.trans inverse
  exact (circularRows_backward admissible (smooth.equivalence state).val).symm.trans
    (congrArg (circularRows admissible) backward)

/-- Exact AO28 after the actual compensated transfer. The circular
correction cancels before any estimate or completion is taken. -/
theorem smoothForwardComparison_difference (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (state : circularCompensatedCore admissible) :
    actualRows admissible data coherent (smooth.equivalence state).val - circularRows admissible state.val =
      errorRows admissible data coherent (compensatedReconstruct admissible (smooth.equivalence state).val) :=
  (congrArg (fun value : SmoothCapSource L sigma gamma ell =>
    actualRows admissible data coherent (smooth.equivalence state).val - value)
      (circularRows_transfer admissible smooth state).symm).trans
        (actualRows_difference admissible data coherent (smooth.equivalence state).val)

end Grad.GaugeCoefficients.Physical.Compensated
