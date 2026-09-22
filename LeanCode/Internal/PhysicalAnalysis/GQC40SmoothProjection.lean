import GQC35CircularGradient
import GQC39PhysicalFirstJet

noncomputable section

set_option maxHeartbeats 1600000

open Set
open scoped Topology

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem apSmoothCircle_idempotent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothCircle L sigma gamma ell (apSmoothCircle L sigma gamma ell field) = apSmoothCircle L sigma gamma ell field := by
  apply apSmoothGrade_injective admissible 3 0
  exact apCircleProjection_idempotent L sigma gamma ell 0 (field.val 0)

theorem apSmoothCircle_fixed_iff {L sigma gamma ell : ℝ} (field : APSmooth L sigma gamma ell 3) :
    apSmoothCircle L sigma gamma ell field = field ↔ apSmoothComplement L sigma gamma ell field = 0 := by
  change field - apSmoothComplement L sigma gamma ell field = field ↔ _
  exact sub_eq_self

theorem apCircleProjection_preserves_firstJet {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ} (large : 2 ≤ grade)
    (field : apGrade L sigma gamma ell 3 grade) (flat : APAxisFirstJetZero admissible large field) :
    APAxisFirstJetZero admissible large (apCircleProjection L sigma gamma ell grade field) := by
  intro angle
  apply (closedAxisFlat_iff_firstJet _).mp
  have original := (closedAxisFlat_iff_firstJet _).mpr (flat angle)
  change ClosedAxisFlat (apPhysicalValue admissible large angle (field - apComplement L sigma gamma ell grade field))
  rw [map_sub, apComplement_physical]
  exact original.sub original.complement

theorem apSmoothCircle_preserves_firstJet {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 3)
    (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apSmoothCircle L sigma gamma ell field) := by
  apply (apSmoothAxisFirstJetZero_iff_grade admissible (by omega : 2 ≤ 2) _).mpr
  exact apCircleProjection_preserves_firstJet admissible (by omega : 2 ≤ 2) (field.val 2)
    ((apSmoothAxisFirstJetZero_iff_grade admissible (by omega : 2 ≤ 2) field).mp flat)

section Current

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (laws : ∀ grade, ActualProjectionLaws admissible gauge grade)

include laws in
theorem apSmoothCurrent_circle_right (field : APSmooth L sigma gamma ell 3) :
    apSmoothCurrent admissible gauge coherent inverseCoherent (apSmoothCircle L sigma gamma ell field) =
      apSmoothCurrent admissible gauge coherent inverseCoherent field := by
  apply apSmoothGrade_injective admissible 3 0
  exact (laws 0).circleRight (field.val 0)

include laws in
theorem apSmoothCurrent_circle_left (field : APSmooth L sigma gamma ell 3) :
    apSmoothCircle L sigma gamma ell (apSmoothCurrent admissible gauge coherent inverseCoherent field) =
      apSmoothCircle L sigma gamma ell field := by
  apply apSmoothGrade_injective admissible 3 0
  exact (laws 0).circleLeft (field.val 0)

include laws in
theorem apSmoothCurrent_gauge_zero (field : APSmooth L sigma gamma ell 3) :
    apSmoothGauge admissible gauge coherent (apSmoothCurrent admissible gauge coherent inverseCoherent field) = 0 := by
  apply apSmoothGrade_injective admissible 3 0
  have member : apCurrentProjection admissible gauge 0 (field.val 0) ∈
      LinearMap.range (apCurrentProjection admissible gauge 0).toLinearMap := ⟨field.val 0, rfl⟩
  rw [(laws 0).range] at member
  exact member

theorem apSmoothCurrent_fixed (field : APSmooth L sigma gamma ell 3)
    (zero : apSmoothGauge admissible gauge coherent field = 0) :
    apSmoothCurrent admissible gauge coherent inverseCoherent field = field := by
  change field - apSmoothExtension admissible gauge coherent inverseCoherent
    (apSmoothGauge admissible gauge coherent field) = field
  rw [zero, map_zero, sub_zero]

include laws in
theorem apSmoothCurrent_removed_mem (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    apSmoothGrade L sigma gamma ell 3 grade
      (field - apSmoothCurrent admissible gauge coherent inverseCoherent field) ∈
        apComplementRange L sigma gamma ell grade := by
  rw [← (laws grade).kernel]
  change apCurrentProjection admissible gauge grade
    (field.val grade - apCurrentProjection admissible gauge grade (field.val grade)) = 0
  rw [map_sub, (laws grade).idempotent, sub_self]

theorem apSmoothCurrent_preserves_firstJet (field : APSmooth L sigma gamma ell 3)
    (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apSmoothCurrent admissible gauge coherent inverseCoherent field) := by
  apply (apSmoothAxisFirstJetZero_iff_grade admissible (by omega : 2 ≤ 2) _).mpr
  exact apCurrentProjection_preserves_firstJet admissible gauge (by omega : 2 ≤ 2) (field.val 2)
    ((apSmoothAxisFirstJetZero_iff_grade admissible (by omega : 2 ≤ 2) field).mp flat)

end Current

end Grad.GaugeCoefficients.Physical.Compensated
