import AKU9FixedAxisPolynomialCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.QuotientProjection

abbrev ScalarQuadraticAxisData (parameters : PhaseParameters) :=
  Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 1

def quadraticAxisCore {parameters : PhaseParameters} (data : ScalarQuadraticAxisData parameters) :
    ACore parameters 1 :=
  ∑ index, fixedAxisJetCore (quadraticScalarJet (Pi.single index 1)) (data index)

theorem quadraticAxisCore_val {parameters : PhaseParameters} (data : ScalarQuadraticAxisData parameters)
    (cell : ℤ) : (quadraticAxisCore data).val cell =
      quadraticScalarJet (fun index => (data index).val cell 0) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro component
  have componentZero : component = 0 := Subsingleton.elim _ _
  subst component
  change ((quadraticAxisCore data).val cell).value point 0 = _
  simp [quadraticAxisCore,Fin.sum_univ_three,fixedAxisJetCore_val,
    closedJet_value_add,closedJet_value_smul,quadraticScalarJet_value]
  ring

/-- Actual second Taylor coefficients are axis-core elements, obtained from
existing first trace and one Cartesian derivative at the original width. -/
def scalarSecondTaylorAxis {parameters : PhaseParameters} (field : ACore parameters 1) :
    ScalarQuadraticAxisData parameters :=
  ![(1/2 : ℂ) • traceFirst 0 (partialCore parameters 0 field),
    traceFirst 0 (partialCore parameters 1 field),
    (1/2 : ℂ) • traceFirst 1 (partialCore parameters 1 field)]

theorem scalarSecondTaylorAxis_val {parameters : PhaseParameters} (field : ACore parameters 1)
    (cell : ℤ) (index : Fin 3) :
    (scalarSecondTaylorAxis field index).val cell 0 = scalarSecondTaylorCoefficients (field.val cell) index := by
  have trace (first second : Fin 2) :
      (traceFirst first (partialCore parameters second field)).val cell 0 =
        (Grad.GaugeCoefficients.Physical.Compensated.partialJet first
          (Grad.GaugeCoefficients.Physical.Compensated.partialJet second (field.val cell))).value
            Grad.NonlinearDivision.closedOrigin 0 := by
    rw [traceFirst_val,originPartial_eq_closedDerivative]
    rfl
  fin_cases index
  · change (1/2 : ℂ) * (traceFirst 0 (partialCore parameters 0 field)).val cell 0 = _ / 2
    rw [trace]
    ring
  · exact trace 0 1
  · change (1/2 : ℂ) * (traceFirst 1 (partialCore parameters 1 field)).val cell 0 = _ / 2
    rw [trace]
    ring

def originalScalarHessianAxis {parameters : PhaseParameters} (source : SmoothQuotient parameters) :
    ScalarQuadraticAxisData parameters :=
  ![(1/2 : ℂ) • traceFirst 0 (cartesianSpinFirst source),
    traceFirst 1 (cartesianSpinFirst source),
    (1/2 : ℂ) • traceFirst 1 (cartesianSpinSecond source)]

theorem originalScalarHessianAxis_val {parameters : PhaseParameters} (source : SmoothQuotient parameters)
    (cell : ℤ) (index : Fin 3) :
    (originalScalarHessianAxis source index).val cell 0 = originalScalarSourceJetCoefficients source cell index := by
  have component (direction : Fin 2) :
      (traceFirst direction (cartesianSpinFirst source)).val cell 0 =
        originalSourceHessian source cell 0 direction := by
    have same := congrArg (fun core : ACore parameters 1 => core.val cell)
      (componentCore_vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source) 0)
    change valueMapJet (componentValue 2 0) ((cartesianSourceVector source).val cell) =
      (cartesianSpinFirst source).val cell at same
    rw [traceFirst_val,← same,valueMapJet_originPartial,componentValue_apply,
      originPartial_eq_closedDerivative]
    rfl
  have componentSecond (direction : Fin 2) :
      (traceFirst direction (cartesianSpinSecond source)).val cell 0 =
        originalSourceHessian source cell 1 direction := by
    have same := congrArg (fun core : ACore parameters 1 => core.val cell)
      (componentCore_vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source) 1)
    change valueMapJet (componentValue 2 1) ((cartesianSourceVector source).val cell) =
      (cartesianSpinSecond source).val cell at same
    rw [traceFirst_val,← same,valueMapJet_originPartial,componentValue_apply,
      originPartial_eq_closedDerivative]
    rfl
  fin_cases index
  · change (1/2 : ℂ) * (traceFirst 0 (cartesianSpinFirst source)).val cell 0 = _ / 2
    rw [component]
    ring
  · exact component 1
  · change (1/2 : ℂ) * (traceFirst 1 (cartesianSpinSecond source)).val cell 0 = _ / 2
    rw [componentSecond]
    ring

def originalS2Core {parameters : PhaseParameters} (source : SmoothQuotient parameters) : ACore parameters 1 :=
  quadraticAxisCore (originalScalarHessianAxis source)

theorem originalS2Core_val {parameters : PhaseParameters} (source : SmoothQuotient parameters) (cell : ℤ) :
    (originalS2Core source).val cell = quadraticScalarJet (originalScalarSourceJetCoefficients source cell) := by
  rw [originalS2Core,quadraticAxisCore_val]
  congr 1
  funext index
  exact originalScalarHessianAxis_val source cell index

theorem originalS2Core_mean_zero {parameters : PhaseParameters} (source : SmoothQuotient parameters)
    (flat : IsFlat source) : angularCore parameters 0 (originalS2Core source) = 0 := by
  apply Subtype.ext
  funext cell
  change angularClosedJet 0 ((originalS2Core source).val cell) = 0
  rw [originalS2Core_val]
  exact originalScalarSourceJet_mean_zero source flat cell

end Grad.FinitePhysicalJetLift
