import AKEG2PhysicalUnitNativeActions
import AKBT10SameWeightedNativeLedgerActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.PDEBootstrap Grad.CartesianStartup Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ActualCurrentPrimitives Grad.Constraints.Gauges Grad.BoundaryTrace
open Grad.AnalyticWeights.Calculus Grad.GaugeCoefficients.Physical Grad.SourceCollarCoefficients
open Grad.SourceCollar Grad.GaugeCoefficients.Physical.Frame Grad.ActualScaledNativeCoefficients

theorem nativeUnitMatrixRaw_value {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (raw : ℝ × Spatial → PhysicalValue input) (angle : ℝ) (point : ClosedDisk) :
    nativeScaledMatrixRaw 1 family raw (angle,point.val) =
      coefficientPhysicalValue (family 0) angle point (raw (angle,point.val)) := by
  rw [nativeScaledMatrixRaw_value (unitDiskAdmissible parameters)]
  have same : physicalScaledPoint 1 (unitDiskAdmissible parameters).2.2.2.1.le
      ((unitDiskAdmissible parameters).2.2.2.2.trans (min_le_left _ _)) point = point := by
    apply Subtype.ext
    exact one_smul ℝ point.val
  exact congrArg (fun location : ClosedDisk => coefficientPhysicalValue (family 0) angle location
    (raw (angle,point.val))) same

variable {parameters : PhaseParameters} {length radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (state : Grad.OriginalCoreRealization.OriginalUnitRankState parameters length radius)
    {covariant force cofactor : StartupL2 3} {raw : ℝ × Spatial → PhysicalValue 3}
    (covariantSame : StartupWeightedRep parameters.sigma0 parameters.gamma 1 covariant raw)
    (regular : StartupOrbitContinuous raw)

include covariantSame regular
/-- The actual scaled planar/third ledger kernels are the SAME completed
native force output, before taking either selected row. -/
theorem weighted_force_actions
    (forceSame : StartupWeightedRep parameters.sigma0 parameters.gamma 1 force
      (nativeScaledMatrixRaw 1 (forceMatrixFamily parameters length state.epsilon state.field) raw))
    (forceContinuous : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle =>
      nativeScaledMatrixRaw 1 (forceMatrixFamily parameters length state.epsilon state.field) raw (angle,point))) :
    originalMatrixKernel (unitDiskAdmissible parameters) state.data.rotatedPlanarProduct (state.coherent radiusNonnegative).2.2.2.2.2.2.2.1 covariant =
      originalValueKernel planarPartMap force ∧
    originalMatrixKernel (unitDiskAdmissible parameters) state.data.rotatedThirdProduct (state.coherent radiusNonnegative).2.2.2.2.2.2.2.2 covariant =
      originalValueKernel toroidalPartMap force := by
  constructor
  · apply (covariantSame.matrix (unitDiskAdmissible parameters) state.data.rotatedPlanarProduct (state.coherent radiusNonnegative).2.2.2.2.2.2.2.1 regular).ext
    apply (forceSame.value forceContinuous planarPartMap).congr_raw
    filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
    intro angle
    let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
    rw [startupRawMatrix_value _ _ angle closed,nativeUnitMatrixRaw_value _ _ angle closed]
    exact (state.planarForce_action 0 angle closed (raw (angle,point))).symm
  · apply (covariantSame.matrix (unitDiskAdmissible parameters) state.data.rotatedThirdProduct (state.coherent radiusNonnegative).2.2.2.2.2.2.2.2 regular).ext
    apply (forceSame.value forceContinuous toroidalPartMap).congr_raw
    filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
    intro angle
    let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
    rw [startupRawMatrix_value _ _ angle closed,nativeUnitMatrixRaw_value _ _ angle closed]
    exact (state.thirdForce_action 0 angle closed (raw (angle,point))).symm

/-- The actual determinant deviation acts as cofactor+a_C on the SAME
weighted fields, retaining the entire native matrix product. -/
theorem weighted_flux_action
    (cofactorSame : StartupWeightedRep parameters.sigma0 parameters.gamma 1 cofactor
      (nativeScaledMatrixRaw 1 (originalCofactorFamily parameters length state.epsilon state.field) raw))
    (cofactorContinuous : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle =>
      nativeScaledMatrixRaw 1 (originalCofactorFamily parameters length state.epsilon state.field) raw (angle,point))) :
    originalMatrixKernel (unitDiskAdmissible parameters) state.data.fluxDeviation (state.coherent radiusNonnegative).2.2.2.2.1 covariant = cofactor+covariant := by
  apply (covariantSame.matrix (unitDiskAdmissible parameters) state.data.fluxDeviation (state.coherent radiusNonnegative).2.2.2.2.1 regular).ext
  apply (cofactorSame.add covariantSame cofactorContinuous regular.axial_ae).congr_raw
  filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
  intro angle
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  rw [startupRawMatrix_value _ _ angle closed,nativeUnitMatrixRaw_value _ _ angle closed]
  exact (state.cofactorFlux_action 0 angle closed (raw (angle,point))).symm

end Grad.OriginalCoreRealization.OriginalUnitRankState
