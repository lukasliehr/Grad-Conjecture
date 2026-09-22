import GQC34APCovariant

noncomputable section

set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped Topology

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem closedAngularMean_rotation_scalar_zero (field : ClosedJet 1) (point : ClosedDisk) :
    closedAngularMean (fun other => (Grad.NonlinearRange.rotationJet field).value other 0) point = 0 := by
  let projection : ComplexEuclidean 1 →L[ℝ] ℂ :=
    (PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : ComplexEuclidean 1 →L[ℂ] ℂ).restrictScalars ℝ
  have identity := closedAngularMean_clm projection (Grad.NonlinearRange.rotationJet field).value
    (Grad.NonlinearRange.rotationJet field).value.continuous point
  rw [closedAngularMean_jet, angularClosedJet_rotation_zero] at identity
  exact identity.symm

theorem covariantJet_complement_zero (frequency : ℂ) (field : ClosedJet 1)
    (meanZero : angularClosedJet 0 field = 0) :
    fixedComplementJet (covariantJet frequency field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [fixedComplementJet_value, cartesianComplementValue_eq_polar _ (covariantJet frequency field).value.continuous]
  have tangent : closedAngularMean (fun other => storedTangentDot other ((covariantJet frequency field).value other)) point = 0 := by
    simp_rw [covariantJet_tangent]
    exact closedAngularMean_rotation_scalar_zero field point
  have axial : closedAngularMean (fun other => (covariantJet frequency field).value other 2) point = 0 := by
    let mapping : ComplexEuclidean 1 →L[ℝ] ℂ :=
      (frequency • (PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : ComplexEuclidean 1 →L[ℂ] ℂ)).restrictScalars ℝ
    have identity := closedAngularMean_clm mapping field.value field.value.continuous point
    rw [closedAngularMean_jet, meanZero] at identity
    simp_rw [covariantJet_value]
    simpa [mapping] using identity.symm
  change complementProfile
    (fun other => (radiusScalar other)⁻¹ * closedAngularMean
      (fun source => storedTangentDot source ((covariantJet frequency field).value source)) other)
    (fun other => closedAngularMean (fun source => (covariantJet frequency field).value source 2) other) point = 0
  rw [complementProfile, tangent, axial, mul_zero, zero_smul, zero_smul, zero_add]

def APSmoothMeanZero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) : Prop :=
  ∀ cell, angularClosedJet 0 (apSmoothJet admissible 1 cell field) = 0

theorem apSmoothCovariant_complement_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 1)
    (meanZero : APSmoothMeanZero admissible field) :
    apSmoothComplement L sigma gamma ell (apSmoothCovariant admissible field) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  rw [map_zero]
  exact (apSmoothComplement_jet admissible (apSmoothCovariant admissible field) cell).trans
    ((congrArg fixedComplementJet (apSmoothCovariant_jet admissible field cell)).trans
      (covariantJet_complement_zero _ _ (meanZero cell)))

theorem apSmoothCovariant_circle {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 1)
    (meanZero : APSmoothMeanZero admissible field) :
    apSmoothCircle L sigma gamma ell (apSmoothCovariant admissible field) = apSmoothCovariant admissible field := by
  change apSmoothCovariant admissible field -
    apSmoothComplement L sigma gamma ell (apSmoothCovariant admissible field) = _
  rw [apSmoothCovariant_complement_zero admissible field meanZero, sub_zero]

end Grad.GaugeCoefficients.Physical.Compensated
