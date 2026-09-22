import AKU47LiteralCurrentForceJetMatch

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation

theorem secondAxisTrace_valueMap {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : ACore parameters input) (first second : Fin 2) :
    secondAxisTrace first second (valueMapCore parameters mapping field) =
      axisValueMap mapping (secondAxisTrace first second field) := by
  apply axisPhysicalValue_ext
  intro angle
  change axisPhysicalValue (traceFirst first (partialCore parameters second (valueMapCore parameters mapping field))) angle = _
  rw [traceFirst_physical,partialCore_valueMap,partialCore_valueMap,coreValue_valueMap,axisValueMap_physical]
  exact congrArg mapping (traceFirst_physical (partialCore parameters second field) first angle).symm

theorem secondTaylorAxis_valueMap {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : ACore parameters input) (index : Fin 3) :
    secondTaylorAxis (valueMapCore parameters mapping field) index =
      axisValueMap mapping (secondTaylorAxis field index) := by
  fin_cases index <;> simp [secondTaylorAxis,secondAxisTrace_valueMap,map_smul]

/-- Immediate consumer in the literal original quotient derivative, with
both physical force components and every original axis/cell coefficient. -/
theorem originalFiniteLift_derivative_force_quadratic (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) :
    secondTaylorAxis (cartesianSourceVector
      (quotientRowsDerivative parameters length 1 ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
        ![(0,originalFiniteLiftU parameters length rho epsilon field low source,
          originalFiniteLiftS parameters length rho epsilon field low source)])) =
      secondTaylorAxis (cartesianSourceVector source) := by
  rw [quotientRowsDerivative_etaZero_cartesian]
  have sourceTaylor : secondTaylorAxis (cartesianSourceVector source) = originalForce2Axis source := rfl
  rw [sourceTaylor]
  funext index
  apply Subtype.ext
  funext cell
  apply PiLp.ext
  intro direction
  have mapped := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters 1 => axis.val cell 0)
    (congrFun (originalFiniteLift_force_secondTaylor parameters length rho epsilon field low source direction) index)
  have recover := secondTaylorAxis_valueMap (componentValue 2 direction)
    (vectorTuple
      (physicalCartesianForceComponent 0 (planarReferenceCore parameters+field)
        (originalFiniteLiftU parameters length rho epsilon field low source)
        (originalFiniteLiftS parameters length rho epsilon field low source))
      (physicalCartesianForceComponent 1 (planarReferenceCore parameters+field)
        (originalFiniteLiftU parameters length rho epsilon field low source)
        (originalFiniteLiftS parameters length rho epsilon field low source))) index
  change secondTaylorAxis (componentCore 2 direction _) index = _ at recover
  rw [componentCore_vectorTuple] at recover
  have recovered := congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters 1 => axis.val cell 0) recover
  fin_cases direction <;>
    simpa only [axisValueMap_val,axisComponent,componentValue_apply] using recovered.symm.trans mapped

end Grad.FinitePhysicalJetLift
