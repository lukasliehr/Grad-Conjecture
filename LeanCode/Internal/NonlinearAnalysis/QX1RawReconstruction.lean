import QZ6Consumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.RawForward

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.QuotientProjection

/-- The literal N33 reconstruction. Raw rows are ordered H0,H1,H2,H3;
the quotient input is g+,g-,g3,h. This is multiplication, never division
by a spatial coordinate. No quotient norm is replaced by a raw row norm. -/
def rawReconstructionCore (parameters : PhaseParameters) :
    QuotientRows parameters →ₗ[ℂ] QuotientRows parameters :=
  LinearMap.pi ![(2 * Complex.I)⁻¹ •
      ((starZMulCore parameters).comp (LinearMap.proj 0) - (zMulCore parameters).comp (LinearMap.proj 1)),
    (1 / 2 : ℂ) •
      ((starZMulCore parameters).comp (LinearMap.proj 0) + (zMulCore parameters).comp (LinearMap.proj 1)),
    LinearMap.proj 3, (radiusSquaredCore parameters).comp (LinearMap.proj 2)]

theorem rawReconstructionCore_apply (parameters : PhaseParameters) (rows : QuotientRows parameters) :
    rawReconstructionCore parameters rows =
    ![(2 * Complex.I)⁻¹ • (starZMulCore parameters (rows 0) - zMulCore parameters (rows 1)),
      (1 / 2 : ℂ) • (starZMulCore parameters (rows 0) + zMulCore parameters (rows 1)),
      rows 3, radiusSquaredCore parameters (rows 2)] := by
  funext index
  fin_cases index <;> rfl

/-- The four original Cartesian raw equations, coefficient by coefficient.
Their fixed products are the actual Fourier products of closed smooth jets. -/
def originalRawRowsCore (parameters : PhaseParameters) (cellLength : ℝ)
    (state : QuotientState parameters) : QuotientRows parameters :=
  ![rotationCore parameters (statePotential state) -
      dotOperation parameters (rotationCore parameters (stateField state)) (rotationCore parameters (stateField state)) +
      radiusSquaredCore parameters (scalarConstantCore parameters 1),
    removeAngularCore parameters (eulerCore parameters (statePotential state) -
      dotOperation parameters (eulerCore parameters (stateField state)) (rotationCore parameters (stateField state))),
    removeAngularCore parameters (dotOperation parameters (rotationCore parameters (stateField state))
      (affineStateCore parameters cellLength state) - timeDerivativeCore parameters (statePotential state)),
    removeAngularCore parameters (determinantOperation parameters (eulerCore parameters (stateField state))
      (rotationCore parameters (stateField state)) (affineStateCore parameters cellLength state))]

end Grad.RawForward
