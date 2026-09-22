import AKBV12ClosedAnnularCartesianDescent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.DiskExtension.Operator

variable {dimension : ℕ} (lower join upper : ℝ) (below : lower < join) (above : join < upper)
    (inner outer : SpatialCell → ComplexEuclidean dimension)
    (agree : EqOn inner outer {point | ‖planarPart point‖ ∈ Ioo lower upper})

def gluedWeightedCylinder (point : SpatialCell) : ComplexEuclidean dimension :=
  if ‖planarPart point‖ ≤ join then inner point else outer point

include below agree in
theorem gluedWeightedCylinder_inner (point : SpatialCell) (small : ‖planarPart point‖ < upper) :
    gluedWeightedCylinder join inner outer point = inner point := by
  unfold gluedWeightedCylinder
  split_ifs with inside
  · rfl
  · exact (agree ⟨below.trans (lt_of_not_ge inside),small⟩).symm

include above agree in
theorem gluedWeightedCylinder_outer (point : SpatialCell) (large : lower < ‖planarPart point‖) :
    gluedWeightedCylinder join inner outer point = outer point := by
  unfold gluedWeightedCylinder
  split_ifs with inside
  · exact agree ⟨large,inside.trans_lt above⟩
  · rfl

include below above agree in
theorem gluedWeightedCylinder_smooth
    (innerSmooth : ContDiff ℝ ∞ inner)
    (outerSmooth : ContDiffOn ℝ ∞ outer {point | ‖planarPart point‖ ∈ Icc lower 1}) :
    ContDiffOn ℝ ∞ (gluedWeightedCylinder join inner outer) closedUnitCylinder := by
  intro point inside
  have radiusContinuous : Continuous (fun source : SpatialCell => ‖planarPart source‖) := continuous_planarPart.norm
  by_cases small : ‖planarPart point‖ < upper
  · apply innerSmooth.contDiffAt.contDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds ((isOpen_lt radiusContinuous continuous_const).mem_nhds small)] with source member
      exact gluedWeightedCylinder_inner lower join upper below inner outer agree source member
    · exact gluedWeightedCylinder_inner lower join upper below inner outer agree point small
  · have large : lower < ‖planarPart point‖ := below.trans (above.trans_le (le_of_not_gt small))
    have localOuter : ContDiffWithinAt ℝ ∞ outer
        (closedUnitCylinder ∩ {source | lower < ‖planarPart source‖}) point :=
      (outerSmooth point ⟨large.le,inside⟩).mono (fun _ member => ⟨member.2.le,member.1⟩)
    have regular := localOuter.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _
      ((isOpen_lt continuous_const radiusContinuous).mem_nhds large))
    apply regular.congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds ((isOpen_lt continuous_const radiusContinuous).mem_nhds large)] with source member
      exact gluedWeightedCylinder_outer lower join upper above inner outer agree source member
    · exact gluedWeightedCylinder_outer lower join upper above inner outer agree point large

theorem gluedWeightedCylinder_periodic
    (innerPeriodic : ∀ point : SpatialPlane, Function.Periodic (fun axial => inner (assembleSpatialCell point axial)) (2*Real.pi))
    (outerPeriodic : ∀ point : SpatialPlane, Function.Periodic (fun axial => outer (assembleSpatialCell point axial)) (2*Real.pi))
    (point : SpatialPlane) :
    Function.Periodic (fun axial => gluedWeightedCylinder join inner outer (assembleSpatialCell point axial)) (2*Real.pi) := by
  intro axial
  simp only [gluedWeightedCylinder,planarPart_assembleSpatialCell]
  split_ifs
  · exact innerPeriodic point axial
  · exact outerPeriodic point axial

/-- Glue the genuine near-axis weighted field to the SAME native annular field, then apply the already accepted exact analytic-core equivalence. -/
def gluedWeightedOriginalCore (parameters : PhaseParameters)
    (innerSmooth : ContDiff ℝ ∞ inner)
    (outerSmooth : ContDiffOn ℝ ∞ outer {point | ‖planarPart point‖ ∈ Icc lower 1})
    (innerPeriodic : ∀ point : SpatialPlane, Function.Periodic (fun axial => inner (assembleSpatialCell point axial)) (2*Real.pi))
    (outerPeriodic : ∀ point : SpatialPlane, Function.Periodic (fun axial => outer (assembleSpatialCell point axial)) (2*Real.pi)) :
    ACore parameters dimension :=
  (weightedSmoothEquiv parameters).symm
    (periodicClosedCylinderJet (gluedWeightedCylinder join inner outer)
      (gluedWeightedCylinder_smooth lower join upper below above inner outer agree innerSmooth outerSmooth)
      (gluedWeightedCylinder_periodic join inner outer innerPeriodic outerPeriodic))

theorem gluedWeightedOriginalCore_actual (parameters : PhaseParameters)
    (innerSmooth : ContDiff ℝ ∞ inner)
    (outerSmooth : ContDiffOn ℝ ∞ outer {point | ‖planarPart point‖ ∈ Icc lower 1})
    (innerPeriodic : ∀ point : SpatialPlane, Function.Periodic (fun axial => inner (assembleSpatialCell point axial)) (2*Real.pi))
    (outerPeriodic : ∀ point : SpatialPlane, Function.Periodic (fun axial => outer (assembleSpatialCell point axial)) (2*Real.pi))
    (point : ClosedDisk) (axial : ℝ) :
    (weightedSmoothEquiv parameters (gluedWeightedOriginalCore lower join upper below above inner outer agree
      parameters innerSmooth outerSmooth innerPeriodic outerPeriodic)).value (point,(axial : CellCircle)) =
      gluedWeightedCylinder join inner outer (assembleSpatialCell point.val axial) := by
  rw [gluedWeightedOriginalCore,LinearEquiv.apply_symm_apply]
  exact periodicClosedCylinderJet_actual _ _ _ point axial

end Grad.CartesianCoreRecovery
