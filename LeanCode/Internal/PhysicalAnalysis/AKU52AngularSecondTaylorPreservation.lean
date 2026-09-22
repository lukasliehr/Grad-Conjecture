import AKU49ActualAxialCorrectionOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear)
open Grad.RepresentedKernel.SpatialProduct Grad.GaugeCoefficients.Radial Grad.PDEBootstrap

theorem secondAxisTrace_symm {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (first second : Fin 2) :
    secondAxisTrace first second field = secondAxisTrace second first field :=
  traceFirst_partialCore_commute first second field

theorem secondAxisTrace_zero_of_secondTaylor_zero {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (zero : secondTaylorAxis field = 0) (first second : Fin 2) :
    secondAxisTrace first second field = 0 := by
  have firstZero : (1/2 : ℂ) • secondAxisTrace 0 0 field = 0 := congrFun zero 0
  have mixedZero : secondAxisTrace 0 1 field = 0 := congrFun zero 1
  have lastZero : (1/2 : ℂ) • secondAxisTrace 1 1 field = 0 := congrFun zero 2
  have scalar : (1/2 : ℂ) ≠ 0 := by norm_num
  fin_cases first <;> fin_cases second
  · exact (smul_eq_zero.mp firstZero).resolve_left scalar
  · exact mixedZero
  · rw [secondAxisTrace_symm]
    exact mixedZero
  · exact (smul_eq_zero.mp lastZero).resolve_left scalar

theorem secondAxisTrace_angular_zero_of_zero {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (zero : ∀ first second, secondAxisTrace first second field = 0)
    (first second : Fin 2) : secondAxisTrace first second (angularCore parameters 0 field) = 0 := by
  apply Subtype.ext
  funext cell
  have derivativeZero (word : CartesianWord 2) : closedDerivative (field.val cell) 2 word closedOrigin = 0 := by
    have traced := congrArg (fun data : Grad.AxisCore.AxisSmoothCore parameters dimension => data.val cell)
      (zero (word 0) (word 1))
    change (partialJetLinear dimension (word 0) (partialJetLinear dimension (word 1) (field.val cell))).value closedOrigin = 0 at traced
    simp only [Grad.GaugeCoefficients.Physical.Compensated.partialJetLinear_apply] at traced
    rw [doublePartial_eq_closedDerivative] at traced
    have words : ![word 0,word 1] = word := by funext index; fin_cases index <;> rfl
    rwa [words] at traced
  change (partialJetLinear dimension first (partialJetLinear dimension second (angularClosedJet 0 (field.val cell)))).value closedOrigin = 0
  simp only [Grad.GaugeCoefficients.Physical.Compensated.partialJetLinear_apply]
  rw [doublePartial_eq_closedDerivative,angularClosedJet_derivative]
  have integrandZero (angle : ℝ) :
      angularCharacter 0 angle • orthogonalDerivative (planeRotationEquiv angle) (field.val cell) 2 ![first,second] closedOrigin = 0 := by
    have origin : orthogonalClosedPoint (planeRotationEquiv angle) closedOrigin = closedOrigin :=
      orthogonalClosedPoint_rotation_origin angle
    change angularCharacter 0 angle • (∑ target : CartesianWord 2,
      chainFactor 2 (planeRotationEquiv angle) ![first,second] target •
        closedDerivative (field.val cell) 2 target
          (orthogonalClosedPoint (planeRotationEquiv angle) closedOrigin)) = 0
    simp only [origin,derivativeZero,smul_zero,Finset.sum_const_zero]
  simp only [integrandZero,MeasureTheory.integral_zero,smul_zero]

theorem secondTaylorAxis_angular_zero_of_zero {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (zero : secondTaylorAxis field = 0) :
    secondTaylorAxis (angularCore parameters 0 field) = 0 := by
  funext index
  fin_cases index <;> simp [secondTaylorAxis,secondAxisTrace_angular_zero_of_zero field
    (secondAxisTrace_zero_of_secondTaylor_zero field zero)]

/-- Angular removal preserves equality with an actual mean-free source
at the full original second Taylor jet. -/
theorem secondTaylorAxis_removeAngular_eq {parameters : PhaseParameters} {dimension : ℕ}
    (field source : ACore parameters dimension) (mean : angularCore parameters 0 source = 0)
    (same : secondTaylorAxis field = secondTaylorAxis source) :
    secondTaylorAxis (removeAngularCore parameters field) = secondTaylorAxis source := by
  have difference : secondTaylorAxis (field-source) = 0 := by rw [secondTaylorAxis_sub,same,sub_self]
  have projected := secondTaylorAxis_angular_zero_of_zero (field-source) difference
  rw [map_sub,mean,sub_zero] at projected
  change secondTaylorAxis (field-angularCore parameters 0 field) = _
  rw [secondTaylorAxis_sub,projected,sub_zero,same]

end Grad.FinitePhysicalJetLift
