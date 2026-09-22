import GQC38PhysicalAxisFourier

noncomputable section

set_option maxHeartbeats 1600000

open Set
open scoped Topology

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem planarDerivative_eq_zero_iff {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (first second : Value) : planarDerivative first second = 0 ↔ first = 0 ∧ second = 0 := by
  constructor
  · intro same
    have firstZero := congrArg (fun derivative : SpatialPlane →L[ℝ] Value => derivative (spatialBasis 0)) same
    have secondZero := congrArg (fun derivative : SpatialPlane →L[ℝ] Value => derivative (spatialBasis 1)) same
    rw [planarDerivative_basis, if_pos rfl, zero_apply] at firstZero
    rw [planarDerivative_basis, if_neg (by decide : (1 : Fin 2) ≠ 0), zero_apply] at secondZero
    exact ⟨firstZero, secondZero⟩
  · rintro ⟨rfl, rfl⟩
    ext direction
    simp only [planarDerivative_apply, smul_zero, add_zero, zero_apply]

def APSmoothPhysicalFirstJetZero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) : Prop :=
  ∀ angle, apSmoothPhysicalValue admissible dimension angle field closedOrigin = 0 ∧
    HasFDerivAt (closedFieldExtension (apSmoothPhysicalValue admissible dimension angle field))
      (0 : SpatialPlane →L[ℝ] ComplexEuclidean dimension) 0

theorem closedDifferential_origin {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field first second : C(ClosedDisk, Value))
    (derivative : HasFDerivAt (closedDiskLift field)
      (planarDerivative (closedDiskLift first 0) (closedDiskLift second 0)) 0) :
    HasFDerivAt (closedFieldExtension field) (planarDerivative (first closedOrigin) (second closedOrigin)) 0 := by
  have firstValue := closedLift_value first 0 (by simp [openUnitDisk])
  have secondValue := closedLift_value second 0 (by simp [openUnitDisk])
  rw [firstValue, secondValue] at derivative
  exact derivative

theorem apSmoothAxisFirstJetZero_iff_physical {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (field : APSmooth L sigma gamma ell dimension) :
    APSmoothAxisFirstJetZero admissible field ↔ APSmoothPhysicalFirstJetZero admissible field := by
  have originInside : (0 : SpatialPlane) ∈ openUnitDisk := by simp [openUnitDisk]
  constructor
  · rintro ⟨valueZero, derivativeZero⟩ angle
    refine ⟨(apSmoothPhysicalValue_pointwise_zero_iff admissible field closedOrigin).mpr valueZero angle, ?_⟩
    have actual := closedDifferential_origin _ _ _
      (apSmoothPhysicalValue_hasFDerivAt admissible angle field 0 originInside)
    have first := (apSmoothPhysicalValue_pointwise_zero_iff admissible
      (apSmoothPartial admissible dimension 0 field) closedOrigin).mpr (derivativeZero 0) angle
    have second := (apSmoothPhysicalValue_pointwise_zero_iff admissible
      (apSmoothPartial admissible dimension 1 field) closedOrigin).mpr (derivativeZero 1) angle
    exact (congrArg (fun derivative : SpatialPlane →L[ℝ] ComplexEuclidean dimension =>
      HasFDerivAt (closedFieldExtension (apSmoothPhysicalValue admissible dimension angle field)) derivative 0)
        ((planarDerivative_eq_zero_iff _ _).mpr ⟨first, second⟩)).mp actual
  · intro flat
    refine ⟨(apSmoothPhysicalValue_pointwise_zero_iff admissible field closedOrigin).mp
      (fun angle => (flat angle).1), ?_⟩
    intro coordinate
    apply (apSmoothPhysicalValue_pointwise_zero_iff admissible
      (apSmoothPartial admissible dimension coordinate field) closedOrigin).mp
    intro angle
    have actual := closedDifferential_origin _ _ _
      (apSmoothPhysicalValue_hasFDerivAt admissible angle field 0 originInside)
    have same := actual.unique (flat angle).2
    have components := (planarDerivative_eq_zero_iff _ _).mp same
    fin_cases coordinate
    · exact components.1
    · exact components.2

theorem apSmoothAxisFirstJetZero_iff_grade {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension grade : ℕ} (large : 2 ≤ grade)
    (field : APSmooth L sigma gamma ell dimension) :
    APSmoothAxisFirstJetZero admissible field ↔ APAxisFirstJetZero admissible large (field.val grade) := by
  rw [apSmoothAxisFirstJetZero_iff_physical]
  unfold APSmoothPhysicalFirstJetZero APAxisFirstJetZero
  simp only [apSmoothPhysicalValue_grade admissible large]

end Grad.GaugeCoefficients.Physical.Compensated
