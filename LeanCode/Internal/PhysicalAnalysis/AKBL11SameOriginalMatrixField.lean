import AKBL10ActualMatrixFourierProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarCoefficients
open Grad.AnalyticWeights.Calculus

/-- The full integer-cell matrix kernel is exactly multiplication by its
original physical coefficient on the SAME phase-weighted Fourier field.
Only axial continuity almost everywhere is needed; no Cartesian H1 or
continuity at the axis is assumed, and no product-series premise remains. -/
theorem startupMatrix_originalField_ae {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (field : StartupL2 inputDimension)
    (raw : Spatial → ℝ → PhysicalValue inputDimension)
    (continuousRaw : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (raw point))
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ input : ℤ,
      field point input = physicalWeight sigma gamma ell input point • angularCoefficient (raw point) input) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ output : ℤ,
      originalMatrixKernel admissible family coherent field point output =
        physicalWeight sigma gamma ell output point • angularCoefficient
          (fun angle => closedDiskLift (coefficientPhysicalValue (family 0) angle) point (raw point angle)) output := by
  apply startupMatrix_weighted_same admissible family coherent field
    (fun input point => angularCoefficient (raw point) input)
    (fun output point => angularCoefficient
      (fun angle => closedDiskLift (coefficientPhysicalValue (family 0) angle) point (raw point angle)) output) same
  filter_upwards [continuousRaw,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point continuousPoint inside
  intro output
  simpa only [closedDiskLift,dif_pos (openDiskMembershipClosed point inside)] using
    startupMatrix_originalProduct_hasSum admissible (family 0)
      ⟨point,openDiskMembershipClosed point inside⟩ (raw point) continuousPoint output

end Grad.CartesianStartup
