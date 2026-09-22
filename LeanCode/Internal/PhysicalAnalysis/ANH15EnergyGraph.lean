import ANH5PhysicalBoundary
import ANH9DiskPoincare

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

def highBoundary : highDiskGrade →L[ℂ] BoundaryL2 :=
  diskBoundary.comp highDiskGrade.subtypeL

abbrev EnergyAmbient := WithLp 2 (highDiskGrade × BoundaryL2)

def energyDecode : EnergyAmbient ≃L[ℂ] highDiskGrade × BoundaryL2 :=
  WithLp.prodContinuousLinearEquiv 2 ℂ highDiskGrade BoundaryL2

def energyConstraint : EnergyAmbient →L[ℂ] BoundaryL2 :=
  highBoundary.comp ((ContinuousLinearMap.fst ℂ highDiskGrade BoundaryL2).comp energyDecode.toContinuousLinearMap) -
    (ContinuousLinearMap.snd ℂ highDiskGrade BoundaryL2).comp energyDecode.toContinuousLinearMap

/-- U4 at the ordinary single disk: the actual closed graph of its boundary
trace, with the inherited H1-plus-boundary square-sum Hilbert norm. -/
def EnergySpace : Submodule ℂ EnergyAmbient := energyConstraint.ker

instance energy_complete : CompleteSpace EnergySpace := by
  have closed : IsClosed (EnergySpace : Set EnergyAmbient) := energyConstraint.isClosed_ker
  exact closed.completeSpace_coe

def energyGraph : highDiskGrade →L[ℂ] EnergyAmbient :=
  energyDecode.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.id ℂ highDiskGrade).prod highBoundary)

def energyFromDisk : highDiskGrade →L[ℂ] EnergySpace :=
  energyGraph.codRestrict _ (fun field => by
    change energyConstraint (energyGraph field) = 0
    change highBoundary field - highBoundary field = 0
    exact sub_self _)

def energyToDisk : EnergySpace →L[ℂ] highDiskGrade :=
  ((ContinuousLinearMap.fst ℂ highDiskGrade BoundaryL2).comp energyDecode.toContinuousLinearMap).comp EnergySpace.subtypeL

theorem energyToFrom (field : highDiskGrade) : energyToDisk (energyFromDisk field) = field := rfl

theorem energyFromTo (field : EnergySpace) : energyFromDisk (energyToDisk field) = field := by
  apply Subtype.ext
  apply energyDecode.injective
  apply Prod.ext
  · rfl
  · exact sub_eq_zero.mp field.property

def energyEquiv : highDiskGrade ≃L[ℂ] EnergySpace where
  toLinearEquiv :=
    { toLinearMap := energyFromDisk.toLinearMap
      invFun := energyToDisk
      left_inv := energyToFrom
      right_inv := energyFromTo }
  continuous_toFun := energyFromDisk.continuous
  continuous_invFun := energyToDisk.continuous

theorem energy_norm_sq (field : highDiskGrade) :
    ‖energyFromDisk field‖ ^ 2 = ‖highDiskBulk field‖ ^ 2 +
      ‖diskGradX field.val‖ ^ 2 + ‖diskGradY field.val‖ ^ 2 + ‖highBoundary field‖ ^ 2 := by
  have pair := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (field, highBoundary field))
  change ‖energyFromDisk field‖ ^ 2 = ‖field‖ ^ 2 + ‖highBoundary field‖ ^ 2 at pair
  exact pair.trans (congrArg (fun value : ℝ => value + ‖highBoundary field‖ ^ 2)
    (highDiskGrade_norm_sq field))

theorem energy_H1_lower (field : highDiskGrade) : ‖field‖ ≤ ‖energyFromDisk field‖ := by
  have pair := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (field, highBoundary field))
  change ‖energyFromDisk field‖ ^ 2 = ‖field‖ ^ 2 + ‖highBoundary field‖ ^ 2 at pair
  nlinarith [norm_nonneg field, norm_nonneg (energyFromDisk field), sq_nonneg ‖highBoundary field‖]

theorem energyCore_denseRange : DenseRange (fun core : ClosedJet 1 => energyFromDisk (highDiskCoreInto core)) :=
  energyEquiv.surjective.denseRange.comp highDiskCoreInto_denseRange energyEquiv.continuous

end Grad.CircularHighWeak
