import AEK7UniformKnownFunctionalBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Ledger

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed
  Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed
  Grad.AnnularCurrentEnergy.energyRealModule

section DataFunctional

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (angular cell : ℕ) (large : 3 ≤ angular + cell + 2)

/-- The exact known functional of one coherent BF2 data packet. -/
def ActualHighKnownData.functional
    (data : ActualHighKnownData parameters L lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell large) :
    annularEnergySpace lower L positive →L[ℝ] ℝ :=
  actualHighKnownFunctional parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state angular cell data.weighted data.auxiliary
      data.datum data.source.val

/-- Restriction to the actual zero-incoming test space consumed by AEL. -/
def ActualHighKnownData.zeroFunctional
    (data : ActualHighKnownData parameters L lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell large) :
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ :=
  actualHighKnownZeroFunctional parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state angular cell data.weighted data.auxiliary
      data.datum data.source.val

/-- Uniform size in the original independent weighted bulk, datum and global
source norms.  No inner-radius factor occurs. -/
def ActualHighKnownData.functionalSize
    (data : ActualHighKnownData parameters L lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell large) : ℝ :=
  actualHighKnownFunctionalSize parameters L compact lower lengthPositive state angular cell
    data.weighted data.auxiliary data.datum data.source.val

theorem ActualHighKnownData.functional_apply_bound
    (data : ActualHighKnownData parameters L lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell large)
    (test : annularEnergySpace lower L positive) :
    ‖data.functional parameters L compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state angular cell large test‖ ≤
      data.functionalSize parameters L compact lower positive lowerHalf lengthPositive
        state angular cell large * ‖test‖ :=
  actualHighKnownFunctional_apply_bound parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state angular cell data.weighted data.auxiliary
      data.datum data.source.val test

/-- Operator norm form of the same uniform estimate, ready for the actual dual
inverse. -/
theorem ActualHighKnownData.zeroFunctional_norm
    (data : ActualHighKnownData parameters L lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell large) :
    ‖data.zeroFunctional parameters L compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state angular cell large‖ ≤
      data.functionalSize parameters L compact lower positive lowerHalf lengthPositive
        state angular cell large := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (actualHighKnownFunctionalSize_nonnegative parameters L compact lower lengthPositive
      state angular cell data.weighted data.auxiliary data.datum data.source.val)
  intro test
  change ‖data.functional parameters L compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state angular cell large test.val‖ ≤ _
  exact data.functional_apply_bound parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state angular cell large test.val

/-- Boundary reconstruction really consumes the genuine graph tuple: after
using the packet compatibility, BCI19's original source vector is exactly the
projection of `(F0,RF0,F2)` from those graphs. -/
theorem ActualHighKnownData.originalSourceBoundaryVector_graph
    (data : ActualHighKnownData parameters L lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell large) :
    originalSourceBoundaryVector parameters L angular cell data.source.val =
      fullNegativeKernelAction parameters angular cell
        (sourceTupleProjectionKernel parameters)
        (sevenSlotFlatten parameters angular cell
          (sevenSlotTrace parameters angular cell 0 0
            (highGraphOuterTuple parameters lower positive
              (lowerHalf.trans_lt (by norm_num)) (angular + cell) data.graphs))) := by
  unfold originalSourceBoundaryVector actualSevenSlotTrace
  rw [data.outer_sourceRange]

end DataFunctional

end Grad.AnnularCurrentSource
