import GQE1AngularMean

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

/-- The fixed reference covector (Yᵀ,0), without any physical frame replacement. -/
def radialRowJet : SmoothOperatorJet 3 1 :=
  operatorJetAdd (coordinateOperatorJet 0 (matrixUnit 0 0))
    (coordinateOperatorJet 1 (matrixUnit 0 1))

def tangentRowJet : SmoothOperatorJet 3 1 :=
  operatorJetAdd (coordinateOperatorJet 0 (matrixUnit 0 1))
    (coordinateOperatorJet 1 (-(matrixUnit 0 0)))

theorem radialRowJet_value (point : ClosedDisk) (value : ComplexEuclidean 3) :
    radialRowJet.value point value 0 = (point.val 0 : ℂ) * value 0 + (point.val 1 : ℂ) * value 1 := by
  change ((coordinateOperatorJet 0 (matrixUnit (input := 3) (output := 1) 0 0)).value point +
    (coordinateOperatorJet 1 (matrixUnit (input := 3) (output := 1) 0 1)).value point) value 0 = _
  simp [coordinateOperatorJet_value, matrixUnit_apply, operatorBasis]

theorem tangentRowJet_value (point : ClosedDisk) (value : ComplexEuclidean 3) :
    tangentRowJet.value point value 0 = storedTangentDot point value := by
  change ((coordinateOperatorJet 0 (matrixUnit (input := 3) (output := 1) 0 1)).value point +
    (coordinateOperatorJet 1 (-(matrixUnit (input := 3) (output := 1) 0 0))).value point) value 0 = _
  simp [coordinateOperatorJet_value, matrixUnit_apply, operatorBasis, storedTangentDot]
  ring

theorem scalarMean_value (field : ClosedJet 1) (point : ClosedDisk) :
    (angularClosedJet 0 field).value point 0 = closedAngularMean (fun other => field.value other 0) point := by
  rw [← closedAngularMean_jet]
  exact closedAngularMean_clm
    ((PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : ComplexEuclidean 1 →L[ℂ] ℂ).restrictScalars ℝ)
    field.value field.value.continuous point

theorem radialRowJet_complement_zero (field : ClosedJet 3) :
    apProductJet radialRowJet (fixedComplementJet field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (apProductJet radialRowJet (fixedComplementJet field)).value point 0 = 0
  rw [apProductJet_value, radialRowJet_value, fixedComplementJet_value,
    cartesianComplementValue_eq_polar field.value field.value.continuous]
  exact complementProfile_tangential _ _ point

theorem tangentRowJet_complement_radial (field : ClosedJet 3) :
    IsDiskRadial (fun point => (apProductJet tangentRowJet (fixedComplementJet field)).value point 0) := by
  have identity (point : ClosedDisk) :
      (apProductJet tangentRowJet (fixedComplementJet field)).value point 0 =
        radiusScalar point * ((radiusScalar point)⁻¹ *
          closedAngularMean (fun other => storedTangentDot other (field.value other)) point) := by
    rw [apProductJet_value, tangentRowJet_value, fixedComplementJet_value,
      cartesianComplementValue_eq_polar field.value field.value.continuous]
    exact storedTangentDot_profile _ _ point
  intro angle point
  dsimp only
  rw [identity, identity, radiusScalar_rotation angle point,
    closedAngularMean_rotation]

theorem tangentRowJet_complement_mean (field : ClosedJet 3) :
    angularClosedJet 0 (apProductJet tangentRowJet (fixedComplementJet field)) =
      apProductJet tangentRowJet (fixedComplementJet field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (angularClosedJet 0 (apProductJet tangentRowJet (fixedComplementJet field))).value point 0 =
    (apProductJet tangentRowJet (fixedComplementJet field)).value point 0
  rw [scalarMean_value]
  exact closedAngularMean_of_radial _ (tangentRowJet_complement_radial field) point

end Grad.GaugeCoefficients.Physical.Compensated
