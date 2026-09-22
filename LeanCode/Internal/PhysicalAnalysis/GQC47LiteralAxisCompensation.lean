import GQC42CompensatedTransfer

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

theorem partialJet_valueMap {input output : ℕ} (coordinate : Fin 2)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (field : ClosedJet input) :
    partialJet coordinate (valueMapJet mapping field) = valueMapJet mapping (partialJet coordinate field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value]
  exact congrFun (congrArg DFunLike.coe (valueMapJet_derivative mapping field (fun _ : Fin 1 => coordinate))) point

theorem partialJetLinear_apply {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) :
    partialJetLinear dimension coordinate field = partialJet coordinate field := rfl

theorem partialJet_gradient (coordinate : Fin 2) (field : ClosedJet 1) :
    partialJet coordinate (gradientJet field) =
      valueMapJet (matrixUnit (input := 1) (output := 2) 0 0) (partialJet coordinate (partialJet 0 field)) +
      valueMapJet (matrixUnit (input := 1) (output := 2) 1 0) (partialJet coordinate (partialJet 1 field)) := by
  change partialJetLinear 2 coordinate (_ + _) = _
  rw [map_add, partialJetLinear_apply, partialJetLinear_apply, partialJet_valueMap, partialJet_valueMap]

theorem covariantJet_partial_value (frequency : ℂ) (field : ClosedJet 1) (coordinate : Fin 2) (point : ClosedDisk) :
    (partialJet coordinate (covariantJet frequency field)).value point = WithLp.toLp 2 ![
      (partialJet coordinate (partialJet 0 field)).value point 0,
      (partialJet coordinate (partialJet 1 field)).value point 0,
      frequency * (partialJet coordinate field).value point 0] := by
  change (partialJetLinear 3 coordinate (valueMapJet planarInclusionMap (gradientJet field) +
    frequency • valueMapJet toroidalInclusionMap field)).value point = _
  rw [map_add, map_smul, partialJetLinear_apply, partialJetLinear_apply,
    partialJet_valueMap, partialJet_valueMap, partialJet_gradient]
  rw [closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul, ContinuousMap.smul_apply,
    valueMapJet_value, valueMapJet_value, closedJet_value_add, ContinuousMap.add_apply,
    valueMapJet_value, valueMapJet_value, matrixUnit_apply, matrixUnit_apply]
  apply PiLp.ext
  intro index
  fin_cases index <;> simp [planarInclusionMap, toroidalInclusionMap, operatorBasis]

def ClosedFirstJetZero {dimension : ℕ} (field : ClosedJet dimension) : Prop :=
  field.value closedOrigin = 0 ∧ ∀ coordinate, (partialJet coordinate field).value closedOrigin = 0

theorem apSmoothAxisFirstJetZero_closed {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (field : APSmooth L sigma gamma ell dimension) (flat : APSmoothAxisFirstJetZero admissible field) (cell : ℤ) :
    ClosedFirstJetZero (apSmoothJet admissible dimension cell field) := by
  refine ⟨flat.1 cell, ?_⟩
  intro coordinate
  exact (congrArg (fun jet : ClosedJet dimension => jet.value closedOrigin)
    (apSmoothPartial_jet admissible field coordinate cell)).symm.trans (flat.2 coordinate cell)

theorem covariantJet_axis_value (frequency : ℂ) (theta : ClosedJet 1) (flat : ClosedFirstJetZero theta) :
    (covariantJet frequency theta).value closedOrigin = 0 := by
  rw [covariantJet_value, flat.1, flat.2 0, flat.2 1]
  apply PiLp.ext
  intro index
  fin_cases index <;> simp

/-- Literal AN7 cancellation. The planar remainder has minus the scalar
Hessian, not zero derivative; the toroidal remainder has zero first jet. -/
theorem closedCompensated_axis (frequency : ℂ) (theta : ClosedJet 1) (remainder : ClosedJet 3)
    (thetaFlat : ClosedFirstJetZero theta) (covariantFlat : ClosedFirstJetZero (covariantJet frequency theta + remainder)) :
    remainder.value closedOrigin = 0 ∧
      (∀ coordinate, (partialJet coordinate remainder).value closedOrigin 0 =
        -((partialJet coordinate (partialJet 0 theta)).value closedOrigin 0)) ∧
      (∀ coordinate, (partialJet coordinate remainder).value closedOrigin 1 =
        -((partialJet coordinate (partialJet 1 theta)).value closedOrigin 0)) ∧
      ∀ coordinate, (partialJet coordinate remainder).value closedOrigin 2 = 0 := by
  have valueZero := covariantFlat.1
  rw [closedJet_value_add, ContinuousMap.add_apply, covariantJet_axis_value frequency theta thetaFlat, zero_add] at valueZero
  have derivativeSum (coordinate : Fin 2) :
      (partialJet coordinate remainder).value closedOrigin =
        -(partialJet coordinate (covariantJet frequency theta)).value closedOrigin := by
    have derivativeZero := covariantFlat.2 coordinate
    change (partialJetLinear 3 coordinate (_ + _)).value closedOrigin = 0 at derivativeZero
    rw [map_add, closedJet_value_add, ContinuousMap.add_apply] at derivativeZero
    exact eq_neg_of_add_eq_zero_right derivativeZero
  refine ⟨valueZero, ?_, ?_, ?_⟩
  · intro coordinate
    have identity := congrArg (fun value : ComplexEuclidean 3 => value 0) (derivativeSum coordinate)
    rw [covariantJet_partial_value] at identity
    exact identity
  · intro coordinate
    have identity := congrArg (fun value : ComplexEuclidean 3 => value 1) (derivativeSum coordinate)
    rw [covariantJet_partial_value] at identity
    exact identity
  · intro coordinate
    have identity := congrArg (fun value : ComplexEuclidean 3 => value 2) (derivativeSum coordinate)
    rw [covariantJet_partial_value, thetaFlat.2 coordinate] at identity
    simpa using identity

end Grad.GaugeCoefficients.Physical.Compensated
