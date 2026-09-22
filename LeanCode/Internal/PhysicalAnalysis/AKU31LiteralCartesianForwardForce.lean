import AKU29LiteralEtaZeroForwardRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection

def physicalCartesianForceComponent {parameters : PhaseParameters} (direction : Fin 2)
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) : ACore parameters 1 :=
  partialCore parameters direction scalar -
    dotOperation parameters (partialCore parameters direction vector) (rotationCore parameters field) -
    dotOperation parameters (partialCore parameters direction field) (rotationCore parameters vector) +
    coordinateCore parameters direction (physicalVariationRadialCorrection field vector)

theorem physicalEtaZeroRows_cartesian_first (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1) :
    cartesianSpinFirst (physicalEtaZeroRows parameters length base vector scalar) =
      physicalCartesianForceComponent 0 base.2.1 vector scalar := by
  simp [cartesianSpinFirst,physicalEtaZeroRows,physicalCartesianForceComponent,
    partialPlusCore,partialMinusCore,zMulCore,starZMulCore,map_add,map_sub,map_smul]
  module

theorem physicalEtaZeroRows_cartesian_second (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1) :
    cartesianSpinSecond (physicalEtaZeroRows parameters length base vector scalar) =
      physicalCartesianForceComponent 1 base.2.1 vector scalar := by
  have factor : (-Complex.I / 2) * Complex.I = (1/2 : ℂ) := by
    linear_combination -(1/2 : ℂ) * Complex.I_sq
  simp [cartesianSpinSecond,physicalEtaZeroRows,physicalCartesianForceComponent,
    partialPlusCore,partialMinusCore,zMulCore,starZMulCore,map_add,map_sub,map_smul]
  simp only [smul_add,smul_sub,smul_smul,factor]
  module

/-- The complete Cartesian first row of the actual original derivative,
with its literal radial correction and no quotient or gauge substitution. -/
theorem quotientRowsDerivative_etaZero_cartesian (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1) :
    cartesianSourceVector (quotientRowsDerivative parameters length 1 base ![(0,vector,scalar)]) =
      vectorTuple (physicalCartesianForceComponent 0 base.2.1 vector scalar)
        (physicalCartesianForceComponent 1 base.2.1 vector scalar) := by
  rw [quotientRowsDerivative_etaZero,cartesianSourceVector,
    physicalEtaZeroRows_cartesian_first,physicalEtaZeroRows_cartesian_second]

/-- Scalar directions contribute exactly the literal gradient and the
negative cell derivative; no current coefficient occurs in this part. -/
theorem physicalEtaZeroRows_scalar_only (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (scalar : ACore parameters 1) :
    physicalEtaZeroRows parameters length base 0 scalar =
      ![partialPlusCore parameters scalar,partialMinusCore parameters scalar,0,
        -(removeAngularCore parameters (timeDerivativeCore parameters scalar))] := by
  funext row
  fin_cases row <;> simp [physicalEtaZeroRows,physicalVariationAffine,physicalVariationRadialCorrection]

end Grad.FinitePhysicalJetLift
