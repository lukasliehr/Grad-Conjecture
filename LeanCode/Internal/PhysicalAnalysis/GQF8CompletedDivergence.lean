import GQF6DivergenceGeometry
import GQF7ComplementAlgebra

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem apTestValue_basis {dimension : ℕ} (coordinate : Fin dimension)
    (value : ComplexEuclidean dimension) :
    apTestValue dimension 0 (operatorBasis coordinate) value = value coordinate := by
  simp [apTestValue, cellProjection, cellSingle, operatorBasis, PiLp.inner_apply]
  change ((lp.single (E := fun _ : ℤ => ComplexEuclidean dimension) 2 0 value) 0) coordinate = value coordinate
  simp

theorem apDiskPairing_coordinate {dimension : ℕ} (coordinate : Fin dimension)
    (field : ClosedJet dimension) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    apDiskPairing 1 0 (operatorBasis 0) test smooth compact
      (closedContinuousToDiskL2 (valueMapJet (matrixUnit 0 coordinate) field).value) =
    apDiskPairing dimension 0 (operatorBasis coordinate) test smooth compact
      (closedContinuousToDiskL2 field.value) := by
  rw [apDiskPairing_closed, apDiskPairing_closed]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
  rw [closedDiskLift, dif_pos (openDiskMembershipClosed point inside),
    closedDiskLift, dif_pos (openDiskMembershipClosed point inside),
    valueMapJet_value, apTestValue_basis, apTestValue_basis]
  congr 1
  simp [matrixUnit_apply, operatorBasis]

theorem fixedComplement_divergence_weak (field : ClosedJet 3)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk) :
    apDiskDerivativePairing 3 0 (operatorBasis 0) test smooth compact 1 (fun _ => 0)
      (closedContinuousToDiskL2 (fixedComplementJet field).value) +
    apDiskDerivativePairing 3 0 (operatorBasis 1) test smooth compact 1 (fun _ => 1)
      (closedContinuousToDiskL2 (fixedComplementJet field).value) = 0 := by
  have first := apClosedJet_weak (fixedComplementJet field) (fun _ : Fin 1 => (0 : Fin 2))
    0 (operatorBasis 0) test smooth compact supported
  have second := apClosedJet_weak (fixedComplementJet field) (fun _ : Fin 1 => (1 : Fin 2))
    0 (operatorBasis 1) test smooth compact supported
  have zero := congrArg (fun jet : ClosedJet 1 =>
    apDiskPairing 1 0 (operatorBasis 0) test smooth compact (closedContinuousToDiskL2 jet.value))
      (planarDivJet_complement_zero field)
  have zeroL2 : closedContinuousToDiskL2 (0 : C(ClosedDisk, ComplexEuclidean 1)) = 0 :=
    (closedValueL2Continuous 1).map_zero
  simp only [planarDivJet, closedJet_value_add, closedContinuousToDiskL2_add, map_add,
    apDiskPairing_coordinate, closedJet_value_zero, zeroL2, map_zero] at zero
  change apDiskPairing 3 0 (operatorBasis 0) test smooth compact
    (closedContinuousToDiskL2 (closedDerivative (fixedComplementJet field) 1 (fun _ => 0))) +
    apDiskPairing 3 0 (operatorBasis 1) test smooth compact
    (closedContinuousToDiskL2 (closedDerivative (fixedComplementJet field) 1 (fun _ => 1))) = 0 at zero
  rw [first, second] at zero
  simpa only [pow_one, neg_one_mul, ← neg_add, neg_eq_zero] using zero

theorem apComplement_divergence_weak (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : apGrade L sigma gamma ell 3 grade) :
    APPlanarDivergenceZero grade (apComplement L sigma gamma ell grade field) := by
  intro cell test smooth compact supported
  let pairing := apDiskDerivativePairing 3 0 (operatorBasis 0) test smooth compact 1 (fun _ => 0) +
    apDiskDerivativePairing 3 0 (operatorBasis 1) test smooth compact 1 (fun _ => 1)
  change pairing (apL2Trace L sigma gamma ell cell (apComplement L sigma gamma ell grade field)) = 0
  apply isClosed_property (apFiniteInto_denseRange (dimension := 3) (grade := grade) L sigma gamma ell)
    (isClosed_eq (pairing.continuous.comp
      ((apL2Trace L sigma gamma ell cell).continuous.comp (apComplement L sigma gamma ell grade).continuous))
      continuous_const) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apComplement_core, apL2Trace_core]
  exact fixedComplement_divergence_weak (core cell) test smooth compact supported

/-- Genuine divergence-free planar V at every original AP2 grade, including 0 and 1. -/
theorem actualComplementDivergence (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : apComplementRange L sigma gamma ell grade) :
    APPlanarDivergenceZero grade field.val := by
  have result := apComplement_divergence_weak L sigma gamma ell grade field.val
  rwa [(apComplementRange_mem_iff L sigma gamma ell grade field.val).mp field.property] at result

end Grad.GaugeCoefficients.Physical.Compensated
