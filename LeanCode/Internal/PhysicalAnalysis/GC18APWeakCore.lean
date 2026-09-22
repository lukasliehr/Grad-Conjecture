import GC18APWeakPairing
import GC18APIntegrationByParts

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct

theorem apClosedScalarDerivative {dimension rank : ℕ} (mapping : ComplexEuclidean dimension →L[ℂ] ℂ)
    (field : ClosedJet dimension) (word : CartesianWord rank) (point : ClosedDisk) :
    wordDerivative rank word (fun source => mapping (smoothClosedExtension field source)) point.val =
      mapping (closedDerivative field rank word point) := by
  change (iteratedFDeriv ℝ rank ((mapping.restrictScalars ℝ) ∘ smoothClosedExtension field) point.val)
    (fun position => spatialBasis (word position)) = _
  rw [(mapping.restrictScalars ℝ).iteratedFDeriv_comp_left (smoothClosedExtension_smooth field).contDiffAt
    (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤))]
  exact congrArg mapping (smoothClosedExtension_derivative field word point)

/-- Every genuine closed jet has the literal weak derivative relation in
the original disk L2 space; tests, not any stronger unknown norm, close it. -/
theorem apClosedJet_weak {dimension rank : ℕ} (field : ClosedJet dimension) (word : CartesianWord rank)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Grad.PDEBootstrap.Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (supported : tsupport test ⊆ openUnitDisk) :
    apDiskPairing dimension cell vector test smooth compact (closedContinuousToDiskL2 (closedDerivative field rank word)) =
      (-1 : ℂ) ^ rank * apDiskDerivativePairing dimension cell vector test smooth compact rank word (closedContinuousToDiskL2 field.value) := by
  rw [apDiskPairing_closed, apDiskDerivativePairing_closed]
  let function : Grad.PDEBootstrap.Spatial → ℂ := fun point => apTestValue dimension cell vector (smoothClosedExtension field point)
  have functionSmooth : ContDiff ℝ ∞ function :=
    ((apTestValue dimension cell vector).restrictScalars ℝ).contDiff.comp (smoothClosedExtension_smooth field)
  calc
    _ = ∫ point in openUnitDisk, test point • wordDerivative rank word function point := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
      rw [closedDiskLift, dif_pos (openDiskMembershipClosed point inside)]
      congr 1
      exact (apClosedScalarDerivative (apTestValue dimension cell vector) field word
        ⟨point, openDiskMembershipClosed point inside⟩).symm
    _ = (-1 : ℂ) ^ rank * ∫ point in openUnitDisk,
        Grad.WeakTesting.orderedTestDerivative rank word test point • function point :=
      orderedScalar_ibp openUnitDisk openUnitDisk_isOpen rank word test smooth compact supported function functionSmooth.contDiffOn
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
      rw [closedDiskLift, dif_pos (openDiskMembershipClosed point inside)]
      change _ = Grad.WeakTesting.orderedTestDerivative rank word test point •
        apTestValue dimension cell vector (field.value ⟨point, openDiskMembershipClosed point inside⟩)
      rw [show function point = apTestValue dimension cell vector (field.value ⟨point, openDiskMembershipClosed point inside⟩) by
        exact congrArg (apTestValue dimension cell vector)
          (smoothClosedExtension_value field ⟨point, openDiskMembershipClosed point inside⟩)]

end Grad.GaugeCoefficients.Physical.RadialLedger
