import AKBL13SameCovariantNativeGauge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelCovariantRecovery
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualSmoothPhysicalField Grad.AnnularOriginalSmoothCore Grad.ActualPhysicalField
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness
open Grad.AnnularCurrentEnergy Grad.AnnularRestriction Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularCoupledInverse Grad.AnnularFullGraph

/-- The SAME full original packet has both actual covariant gauges. The
native Xi/r zero mode is discharged here, for arbitrary original data and
candidate; no Cartesian regularity or homogeneous-source premise occurs. -/
theorem startupNative_originalPacket_gauged (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : AnnularReconstructionState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (originalSevenPacket parameters lower length positive bounded.le lengthPositive data candidate))
    (radius : Icc lower (1 : ℝ)) :
    radialPhysicalGaugeMeans parameters length compact state.val (tupleRadius lower positive radius) 0 0
      (originalCurveNegativeTrace (curves.covariant parameters length compact lower positive bounded state) radius) = 0 := by
  apply startupNative_covariantCurve_gauged parameters length compact lower positive bounded state curves
  intro cell
  exact fullStrongScalarOverRadius_zeroAngular parameters length lower positive bounded lengthPositive
    (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data)
    (originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive candidate) cell

/-- The literal physical gauge product of that SAME covariant reconstruction
has zero angular mean in every original axial cell and every collar radius.
All coefficient products remain inside their original Fourier coefficient. -/
theorem startupNative_originalPacket_physicalGaugeMean (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : AnnularReconstructionState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (originalSevenPacket parameters lower length positive bounded.le lengthPositive data candidate))
    (radius : Icc lower (1 : ℝ)) (kind : Fin 2) (cell : ℤ) :
    angularCoefficient (fun polar => angularCoefficient (fun axial =>
      originalTotalGaugeProduct parameters length compact state.val (tupleRadius lower positive radius) kind
        (fun angles => (curves.covariant parameters length compact lower positive bounded state).fullField bounded
          (radius.val,angles)) (polar,axial)) cell) 0 = 0 :=
  startupNative_gaugePhysicalCell_angularMean parameters length compact state.val lower positive
    (curves.covariant parameters length compact lower positive bounded state) bounded radius
    (startupNative_originalPacket_gauged parameters length compact lower positive bounded lengthPositive state data candidate curves radius)
    kind cell

end Grad.CartesianStartup
