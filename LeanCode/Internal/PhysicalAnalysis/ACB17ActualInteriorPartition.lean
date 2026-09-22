import ACB16ActualNativeOuterBounds
import ASP5WeakSmoothCore
import AIB3InteriorEstimateConsumer
import ABF1OrdinaryBulkFaithfulness

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualInverseInduction Grad.InteriorLocalization Grad.OrdinaryDiskCalculus
open Grad.OrdinaryInteriorBootstrap Grad.OrdinaryDiskFaithfulness Grad.ActualSmoothPDE
open Grad.NonlinearProduct
open Grad.NonlinearDivision (laplacianJet)
attribute [local instance] unitNormedSpace

/-- A fixed auxiliary instance used only to instantiate accepted phase-free
ordinary disk theorems. It does not enter any source, solution, or norm. -/
def auxiliaryOrdinaryParameters : PhaseParameters where
  length := 1
  sigma0 := 1
  gamma := 1 / 2
  length_pos := by norm_num
  sigma0_pos := by norm_num
  gamma_pos := by norm_num
  gamma_lt_min := by norm_num

def centerInnerJet (mode : ℤ) (field : ClosedJet 1) : ClosedJet 1 := field - centerOuterJet mode field

theorem centerOuterJet_value (mode : ℤ) (field : ClosedJet 1) (pure : angularClosedJet mode field = field)
    (point : ClosedDisk) :
    (centerOuterJet mode field).value point = outerCutoffScalar point.val • field.value point := by
  have literal : pureExtension mode field point.val = field.value point :=
    congrArg (fun jet : ClosedJet 1 => jet.value point) (pureExtension_jet mode field pure)
  change outerCutoffScalar point.val • pureExtension mode field point.val = _
  rw [literal]

theorem centerInnerJet_value (mode : ℤ) (field : ClosedJet 1) (pure : angularClosedJet mode field = field)
    (point : ClosedDisk) :
    (centerInnerJet mode field).value point = interiorCutoff.toFun point.val • field.value point := by
  simp only [centerInnerJet, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, centerOuterJet_value mode field pure, outerCutoffScalar]
  module

theorem centerInnerJet_bulk (mode : ℤ) (field : ClosedJet 1) (pure : angularClosedJet mode field = field) :
    closedL2Core (centerInnerJet mode field) = diskScalar interiorCutoff.toFun interiorCutoff.smooth (closedL2Core field) := by
  apply Lp.ext
  filter_upwards [closedContinuousToDiskL2_ae (centerInnerJet mode field).value,
    closedContinuousToDiskL2_ae field.value,
    diskScalar_ae interiorCutoff.toFun interiorCutoff.smooth (closedL2Core field),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point first second action inside
  change closedContinuousToDiskL2 (centerInnerJet mode field).value point = _
  rw [action]
  change closedContinuousToDiskL2 (centerInnerJet mode field).value point =
    interiorCutoff.toFun point • closedContinuousToDiskL2 field.value point
  rw [first, second]
  simp only [closedDiskLift, openDiskMembershipClosed point inside, dite_true]
  exact centerInnerJet_value mode field pure ⟨point, openDiskMembershipClosed point inside⟩

theorem center_partition (mode : ℤ) (field : ClosedJet 1) : centerInnerJet mode field + centerOuterJet mode field = field :=
  sub_add_cancel _ _

/-- The actual inner cutoff of the same smooth solution receives the
accepted ordinary interior gain, with its literal Laplacian. -/
theorem centerInner_native_estimate (grade : ℕ) (mode : ℤ) (field : ClosedJet 1)
    (pure : angularClosedJet mode field = field) :
    ‖unitDiskCoreInto (grade + 2) (centerInnerJet mode field)‖ ≤
      ordinaryInteriorSourceConstant grade * ‖unitDiskCoreInto grade (laplacianJet field)‖ +
        ordinaryInteriorStateConstant grade * ‖unitDiskCoreInto (grade + 1) field‖ := by
  have weak : HasDiskWeakLaplacian (unitDiskBulk (grade + 1) (unitDiskCoreInto (grade + 1) field))
      (unitDiskBulk grade (unitDiskCoreInto grade (laplacianJet field))) := by
    exact (congrArg₂ HasDiskWeakLaplacian
      (unitDiskBulk_core (grade + 1) field)
      (unitDiskBulk_core grade (laplacianJet field))).mpr (closedL2Core_weakLaplacian field)
  obtain ⟨regular, same, bound⟩ := ordinaryInterior_estimate auxiliaryOrdinaryParameters grade
    (unitDiskCoreInto (grade + 1) field) (unitDiskCoreInto grade (laplacianJet field)) weak
  have sameBulk := same.trans
    (congrArg (diskScalar interiorCutoff.toFun interiorCutoff.smooth)
      (unitDiskBulk_core (grade + 1) field))
  have identity : regular = unitDiskCoreInto (grade + 2) (centerInnerJet mode field) := by
    apply ordinaryBulk_injective auxiliaryOrdinaryParameters (grade + 2)
    exact sameBulk.trans ((unitDiskBulk_core (grade + 2) (centerInnerJet mode field)).trans
      (centerInnerJet_bulk mode field pure)).symm
  rwa [identity] at bound

end Grad.ActualCenterBounds
