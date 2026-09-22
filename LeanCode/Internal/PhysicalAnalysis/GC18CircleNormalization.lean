import GC18FourierContinuity

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearDivision

theorem radiusSquaredFamily_coherent {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) : FamilyCoherent (radiusSquaredFamily admissible) :=
  (tangentRow_coherent L sigma gamma ell).comp admissible (tangentColumn_coherent L sigma gamma ell)

theorem radiusSquaredFamily_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (radiusSquaredFamily admissible grade) angle point =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (PhysicalValue 1) := by
  apply operatorMatrix_injective
  rw [operatorMatrix_smul, operatorMatrix_one]
  exact radiusSquaredFamily_matrix admissible grade angle point

theorem radialRotatedPoint_norm (angle : ℝ) (point : ClosedDisk) :
    ‖(Grad.GaugeCoefficients.Radial.rotatedPoint angle point).val‖ = ‖point.val‖ :=
  planeRotation_norm angle point.val

theorem angularRadiusSquared_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily (radiusSquaredFamily admissible) grade) angle point =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (PhysicalValue 1) := by
  rw [angularFamily_physicalValue admissible _ (radiusSquaredFamily_coherent admissible)]
  simp_rw [radiusSquaredFamily_physicalValue admissible, radialRotatedPoint_norm]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const, sub_zero, one_smul]

/-- Circle normalization is proved from the actual completed IΔΠ operator,
including the axis by closed-disk continuity. It is not an assumed GC03 law. -/
theorem radialRadiusSquared_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (radialDivisionFamily admissible (radiusSquaredFamily admissible) grade) angle point =
      ContinuousLinearMap.id ℂ (PhysicalValue 1) := by
  apply continuous_closedDisk_eq_of_offAxis
    (fun point => coefficientPhysicalValue (radialDivisionFamily admissible (radiusSquaredFamily admissible) grade) angle point)
    (fun _ => ContinuousLinearMap.id ℂ (PhysicalValue 1))
    (coefficientPhysicalValue_continuous admissible _
      (radialDivisionFamily_coherent admissible _ (radiusSquaredFamily_coherent admissible)) grade angle)
    continuous_const ?_ point
  intro other offAxis
  have identity := radialDivisionFamily_physical_identity admissible (radiusSquaredFamily admissible)
    (radiusSquaredFamily_coherent admissible) grade angle other
  rw [angularRadiusSquared_physicalValue admissible, angularRadiusSquared_physicalValue admissible] at identity
  have originNorm : ‖closedOrigin.val‖ = 0 := norm_zero
  rw [originNorm, zero_pow (by decide : (2 : ℕ) ≠ 0), Complex.ofReal_zero,
    zero_smul ℂ (ContinuousLinearMap.id ℂ (PhysicalValue 1)), sub_zero] at identity
  have nonzero : ((‖other.val‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr offAxis))
  exact (smul_right_injective (OperatorValue 1 1) nonzero) identity.symm

end Grad.GaugeCoefficients.Physical.RadialLedger
