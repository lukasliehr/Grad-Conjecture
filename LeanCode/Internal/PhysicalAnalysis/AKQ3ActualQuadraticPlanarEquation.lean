import AKQ2FaithfulQuadraticClosedJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearQuotientBounds Grad.NonlinearRange

theorem quotientPartialJet_eq {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) :
    Grad.NonlinearQuotientBounds.partialJet direction field =
      Grad.GaugeCoefficients.Physical.Compensated.partialJet direction field := rfl

def quadraticPlanarJetLinear : QuadraticPlanarCoefficients →ₗ[ℂ] ClosedJet 2 where
  toFun := quadraticPlanarJet
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [quadraticPlanarJet_value,closedJet_value_add,ContinuousMap.add_apply,Pi.add_apply]
    module
  map_smul' scalar coefficients := by
    change quadraticPlanarJet (scalar • coefficients) = scalar • quadraticPlanarJet coefficients
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [quadraticPlanarJet_value,closedJet_value_smul,ContinuousMap.smul_apply,Pi.smul_apply]
    module

/-- The literal current leading planar row, on actual smooth closed jets. -/
def leadingPlanarJetOperator (field : ClosedJet 2) : ClosedJet 2 :=
  rotationJet field + valueMapJet quarterValueMap field

theorem quadraticPlanarJet_operator (coefficients : QuadraticPlanarCoefficients) :
    quadraticPlanarJet (quadraticPlanarOperator coefficients) = leadingPlanarJetOperator (quadraticPlanarJet coefficients) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [quadraticPlanarJet_value,leadingPlanarJetOperator,rotationJet,sub_eq_add_neg,quotientPartialJet_eq,
      closedJet_value_add,closedJet_value_neg,coordinateJet_value,quadraticPlanarJet_partial_value,valueMapJet_value,
      quadraticPlanarOperator,quadraticRotation,quadraticQuarterTurn,quarterValueMap,quarterValueLinear,
      Matrix.vecHead,Matrix.vecTail,Complex.real_smul] <;> ring

/-- T inverts the ACTUAL R+J row on every homogeneous quadratic planar field. -/
theorem leadingPlanarJetOperator_inverse (coefficients : QuadraticPlanarCoefficients) :
    leadingPlanarJetOperator (quadraticPlanarJet (quadraticPlanarInverse coefficients)) = quadraticPlanarJet coefficients :=
  (quadraticPlanarJet_operator (quadraticPlanarInverse coefficients)).symm.trans
    (congrArg quadraticPlanarJet (quadraticPlanarOperator_inverse coefficients))

/-- The solution of the literal quadratic row is unique within exactly that
finite polynomial space, by faithfulness of the genuine closed-jet realization. -/
theorem leadingPlanarJetOperator_injective_on_quadratics
    (first second : QuadraticPlanarCoefficients)
    (same : leadingPlanarJetOperator (quadraticPlanarJet first) =
      leadingPlanarJetOperator (quadraticPlanarJet second)) : first = second := by
  have coefficients := quadraticPlanarJet_injective
    ((quadraticPlanarJet_operator first).trans (same.trans (quadraticPlanarJet_operator second).symm))
  exact quadraticPlanarEquivalence.injective coefficients

end Grad.FinitePhysicalJetLift
