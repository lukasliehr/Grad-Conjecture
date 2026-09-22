import AKBT9ScaledNativeMatrixContinuity
import AKBQ15SameNativeCoefficientProducts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
namespace Grad.ActualScaledNativeCoefficients
open Grad.PDEBootstrap Grad.CartesianStartup Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ActualCurrentPrimitives Grad.Constraints.Gauges Grad.BoundaryTrace
open Grad.AnalyticWeights.Calculus Grad.GaugeCoefficients.Physical Grad.SourceCollarCoefficients
open Grad.SourceCollar Grad.GaugeCoefficients.Physical.Frame

 def nativeScaledMatrixRaw {input output : ℕ} {sigma gamma : ℝ} (ell : ℝ)
    (family : CoefficientFamily 1 sigma gamma 1 input output)
    (raw : ℝ × Spatial → PhysicalValue input) (pair : ℝ × Spatial) : PhysicalValue output :=
  closedDiskLift (coefficientPhysicalValue (family 0) pair.1) (ell • pair.2) (raw pair)

 theorem nativeScaledMatrixRaw_value {L ell : ℝ} {parameters : PhaseParameters}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (raw : ℝ × Spatial → PhysicalValue input) (angle : ℝ) (point : ClosedDisk) :
    nativeScaledMatrixRaw ell family raw (angle,point.val) =
      coefficientPhysicalValue (family 0) angle
        (physicalScaledPoint ell admissible.2.2.2.1.le (admissible.2.2.2.2.trans (min_le_left _ _)) point)
        (raw (angle,point.val)) := by
  have inside : ell • point.val ∈ closedUnitDisk := (physicalScaledPoint ell admissible.2.2.2.1.le
    (admissible.2.2.2.2.trans (min_le_left _ _)) point).property
  simp only [nativeScaledMatrixRaw,closedDiskLift,dif_pos inside]
  rfl

variable {L ell : ℝ} {parameters : PhaseParameters}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (low : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    {covariant force cofactor : StartupL2 3} {raw : ℝ × Spatial → PhysicalValue 3}
    (covariantSame : StartupWeightedRep parameters.sigma0 parameters.gamma ell covariant raw)
    (regular : StartupOrbitContinuous raw)

include covariantSame regular low
/-- The actual scaled planar/third ledger kernels are the SAME completed
native force output, before taking either selected row. -/
theorem actualWeighted_forceLedger_actions
    (forceSame : StartupWeightedRep parameters.sigma0 parameters.gamma ell force
      (nativeScaledMatrixRaw ell (forceMatrixFamily parameters L epsilon base) raw))
    (forceContinuous : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle =>
      nativeScaledMatrixRaw ell (forceMatrixFamily parameters L epsilon base) raw (angle,point))) :
    originalMatrixKernel admissible ledger.val.rotatedPlanarProduct ledger.property.1.2.2.2.2.2.2.2.1 covariant =
      originalValueKernel planarPartMap force ∧
    originalMatrixKernel admissible ledger.val.rotatedThirdProduct ledger.property.1.2.2.2.2.2.2.2.2 covariant =
      originalValueKernel toroidalPartMap force := by
  constructor
  · apply (covariantSame.matrix admissible ledger.val.rotatedPlanarProduct ledger.property.1.2.2.2.2.2.2.2.1 regular).ext
    apply (forceSame.value forceContinuous planarPartMap).congr_raw
    filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
    intro angle
    let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
    rw [startupRawMatrix_value _ _ angle closed,nativeScaledMatrixRaw_value admissible _ _ angle closed]
    exact (scaledLedgerPlanarForce_action ledger low 0 angle closed (raw (angle,point))).symm
  · apply (covariantSame.matrix admissible ledger.val.rotatedThirdProduct ledger.property.1.2.2.2.2.2.2.2.2 regular).ext
    apply (forceSame.value forceContinuous toroidalPartMap).congr_raw
    filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
    intro angle
    let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
    rw [startupRawMatrix_value _ _ angle closed,nativeScaledMatrixRaw_value admissible _ _ angle closed]
    exact (scaledLedgerThirdForce_action ledger low 0 angle closed (raw (angle,point))).symm

/-- The actual determinant deviation acts as cofactor+a_C on the SAME
weighted fields, retaining the entire native matrix product. -/
theorem actualWeighted_fluxLedger_action
    (cofactorSame : StartupWeightedRep parameters.sigma0 parameters.gamma ell cofactor
      (nativeScaledMatrixRaw ell (originalCofactorFamily parameters L epsilon base) raw))
    (cofactorContinuous : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle =>
      nativeScaledMatrixRaw ell (originalCofactorFamily parameters L epsilon base) raw (angle,point))) :
    originalMatrixKernel admissible ledger.val.fluxDeviation ledger.property.1.2.2.2.2.1 covariant = cofactor+covariant := by
  apply (covariantSame.matrix admissible ledger.val.fluxDeviation ledger.property.1.2.2.2.2.1 regular).ext
  apply (cofactorSame.add covariantSame cofactorContinuous regular.axial_ae).congr_raw
  filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
  intro angle
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  rw [startupRawMatrix_value _ _ angle closed,nativeScaledMatrixRaw_value admissible _ _ angle closed]
  exact (scaledLedgerFlux_action ledger low 0 angle closed (raw (angle,point))).symm

end Grad.ActualScaledNativeCoefficients
