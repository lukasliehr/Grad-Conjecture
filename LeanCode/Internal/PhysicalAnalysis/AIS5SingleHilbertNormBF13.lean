import AIS4LiteralHighDataNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators

namespace Grad.AnnularCurrentSource

open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularUniformBoundary Grad.AnnularCurrentEnergy Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.BoundaryKernelAction
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed
  Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed
  Grad.AnnularCurrentEnergy.energyRealModule

section Base

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- The accepted graph-native BF13 functional, now attached to the exact
complete BF2 Hilbert carrier. -/
def ActualHighKnownCarrier.functional
    (data : ActualHighKnownCarrier parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0) :
    annularEnergySpace lower L positive →L[ℝ] ℝ :=
  (ActualHighKnownCarrier.toGraphKnownData parameters lower positive
    (lowerHalf.trans (by norm_num)) 0 0 data).functional parameters L compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state 0 0

def ActualHighKnownCarrier.zeroFunctional
    (data : ActualHighKnownCarrier parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0) :
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive →L[ℝ] ℝ :=
  (ActualHighKnownCarrier.toGraphKnownData parameters lower positive
    (lowerHalf.trans (by norm_num)) 0 0 data).zeroFunctional parameters L compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state 0 0

/-- One collar-independent coefficient multiplying the single BF2 Hilbert
norm.  Its physical coefficients use exactly `1+B8`. -/
def actualHighKnownBF13Constant : ℝ :=
  5 * (4 * eliminatedBulkConstant parameters L compact 0 *
      state.val.val.size 1 + 3) +
    uniformOuterTraceConstant L *
      (knownBoundaryInverseConstant parameters L compact 1 *
          state.val.val.size 1 +
        3 * (graphSourceLiftMomentConstant parameters L compact 1 *
          state.val.val.size 1 *
          fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
          uniformSourceOuterConstant))

theorem actualHighKnownBF13Constant_nonnegative :
    0 ≤ actualHighKnownBF13Constant parameters L compact state := by
  let sizeOne := state.val.val.size 1
  have sizeOneNonnegative : 0 ≤ sizeOne := state.val.val.size_nonnegative 1
  have bulkCoefficient :
      0 ≤ 4 * eliminatedBulkConstant parameters L compact 0 * sizeOne :=
    mul_nonneg (mul_nonneg (by norm_num)
      (eliminatedBulkConstant_nonnegative parameters L compact 0)) sizeOneNonnegative
  have datumCoefficient :
      0 ≤ knownBoundaryInverseConstant parameters L compact 1 * sizeOne :=
    mul_nonneg (knownBoundaryInverseConstant_nonnegative parameters L compact 1)
      sizeOneNonnegative
  have graphCoefficient :
      0 ≤ graphSourceLiftMomentConstant parameters L compact 1 * sizeOne *
        fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
          uniformSourceOuterConstant :=
    mul_nonneg (mul_nonneg (mul_nonneg
      (graphSourceLiftMomentConstant_nonnegative parameters L compact 1) sizeOneNonnegative)
      (fullKernelMoment_nonnegative parameters 1 _))
      uniformSourceOuterConstant_nonnegative
  unfold actualHighKnownBF13Constant
  change 0 ≤ 5 * (_ * sizeOne + 3) +
    uniformOuterTraceConstant L * (_ * sizeOne + 3 * (_ * sizeOne * _ * _))
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg bulkCoefficient (by norm_num)))
    (mul_nonneg (uniformOuterTraceConstant_nonnegative L)
      (add_nonneg datumCoefficient (mul_nonneg (by norm_num) graphCoefficient)))

/-- A coefficient fixed before the background state and the inner collar.
It controls the complete BF2 high datum throughout the physical B8 ball. -/
def actualHighKnownBF13BallConstant : ℝ :=
  5 * (8 * eliminatedBulkConstant parameters L compact 0 + 3) +
    uniformOuterTraceConstant L *
      (2 * knownBoundaryInverseConstant parameters L compact 1 +
        6 * (graphSourceLiftMomentConstant parameters L compact 1 *
          fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
          uniformSourceOuterConstant))

theorem actualHighKnownBF13BallConstant_nonnegative :
    0 ≤ actualHighKnownBF13BallConstant parameters L compact := by
  have bulk := eliminatedBulkConstant_nonnegative parameters L compact 0
  have datum := knownBoundaryInverseConstant_nonnegative parameters L compact 1
  have graph := graphSourceLiftMomentConstant_nonnegative parameters L compact 1
  have moment := fullKernelMoment_nonnegative parameters 1
    (sourceTupleProjectionKernel parameters)
  have source := uniformSourceOuterConstant_nonnegative
  have trace := uniformOuterTraceConstant_nonnegative L
  unfold actualHighKnownBF13BallConstant
  positivity

theorem actualHighKnownBF13Constant_le_ball
    (small : physicalBudget parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon 8 ≤ 1) :
    actualHighKnownBF13Constant parameters L compact state ≤
      actualHighKnownBF13BallConstant parameters L compact := by
  have sizeBound : state.val.val.size 1 ≤ 2 := by
    change 1 + physicalBudget parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon 8 ≤ 2
    linarith
  have bulkNonnegative := eliminatedBulkConstant_nonnegative parameters L compact 0
  have datumNonnegative := knownBoundaryInverseConstant_nonnegative parameters L compact 1
  have graphNonnegative := graphSourceLiftMomentConstant_nonnegative parameters L compact 1
  have momentNonnegative := fullKernelMoment_nonnegative parameters 1
    (sourceTupleProjectionKernel parameters)
  have sourceNonnegative := uniformSourceOuterConstant_nonnegative
  have traceNonnegative := uniformOuterTraceConstant_nonnegative L
  have bulkBound :
      4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 1 ≤
        8 * eliminatedBulkConstant parameters L compact 0 := by
    have := mul_le_mul_of_nonneg_left sizeBound
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) bulkNonnegative)
    nlinarith
  have datumBound :
      knownBoundaryInverseConstant parameters L compact 1 * state.val.val.size 1 ≤
        2 * knownBoundaryInverseConstant parameters L compact 1 := by
    have := mul_le_mul_of_nonneg_left sizeBound datumNonnegative
    nlinarith
  have graphBound :
      graphSourceLiftMomentConstant parameters L compact 1 * state.val.val.size 1 *
          fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
            uniformSourceOuterConstant ≤
        2 * (graphSourceLiftMomentConstant parameters L compact 1 *
          fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
            uniformSourceOuterConstant) := by
    have coefficientNonnegative :
        0 ≤ graphSourceLiftMomentConstant parameters L compact 1 *
          fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
            uniformSourceOuterConstant :=
      mul_nonneg (mul_nonneg graphNonnegative momentNonnegative) sourceNonnegative
    have comparison := mul_le_mul_of_nonneg_left sizeBound coefficientNonnegative
    calc
      _ = (graphSourceLiftMomentConstant parameters L compact 1 *
          fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
            uniformSourceOuterConstant) * state.val.val.size 1 := by ring
      _ ≤ (graphSourceLiftMomentConstant parameters L compact 1 *
          fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
            uniformSourceOuterConstant) * 2 := comparison
      _ = _ := by ring
  have bulkInside :
      4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 1 + 3 ≤
        8 * eliminatedBulkConstant parameters L compact 0 + 3 :=
    add_le_add bulkBound le_rfl
  have bulkScaled :
      5 * (4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 1 + 3) ≤
        5 * (8 * eliminatedBulkConstant parameters L compact 0 + 3) :=
    mul_le_mul_of_nonneg_left bulkInside (by norm_num)
  have boundaryInside := add_le_add datumBound
    (mul_le_mul_of_nonneg_left graphBound (by norm_num : (0 : ℝ) ≤ 3))
  have boundaryScaled := mul_le_mul_of_nonneg_left boundaryInside traceNonnegative
  unfold actualHighKnownBF13Constant actualHighKnownBF13BallConstant
  calc
    _ ≤ 5 * (8 * eliminatedBulkConstant parameters L compact 0 + 3) +
        uniformOuterTraceConstant L *
          (2 * knownBoundaryInverseConstant parameters L compact 1 +
            3 * (2 * (graphSourceLiftMomentConstant parameters L compact 1 *
              fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
                uniformSourceOuterConstant))) :=
      add_le_add bulkScaled boundaryScaled
    _ = _ := by ring

/-- The literal AEK B8 component expression is bounded by one coefficient
times the exact BF2 Hilbert norm, with no collar-dependent norm conversion. -/
def actualHighKnownCarrierB8Size
    (data : ActualHighKnownCarrier parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0) : ℝ :=
  actualHighGraphKnownB8Size parameters L compact lower state
      (actualHighKnownWeighted parameters lower positive
        (lowerHalf.trans (by norm_num)) 0 0 data)
      (actualHighKnownAuxiliary parameters lower positive
        (lowerHalf.trans (by norm_num)) 0 0 data)
      (ActualHighKnownCarrier.graphs parameters lower positive
        (lowerHalf.trans (by norm_num)) 0 0 data)
      (actualHighKnownDatum parameters lower positive
        (lowerHalf.trans (by norm_num)) 0 0 data)

theorem actualHighKnownCarrierB8Size_le_single_norm
    (data : ActualHighKnownCarrier parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0) :
    actualHighKnownCarrierB8Size parameters L compact lower positive lowerHalf state data ≤
      actualHighKnownBF13Constant parameters L compact state * ‖data‖ := by
  let bounded : lower ≤ 1 := lowerHalf.trans (by norm_num)
  rcases ActualHighKnownCarrier.component_bounds parameters lower positive bounded 0 0 data with
    ⟨knownBound, auxiliaryBound, f0Bound, f2Bound, datumBound, _⟩
  have graphBound := ActualHighKnownCarrier.graph_sum_bound parameters lower positive bounded 0 0 data
  let bulkCoefficient :=
    4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 1
  let datumCoefficient :=
    knownBoundaryInverseConstant parameters L compact 1 * state.val.val.size 1
  let graphCoefficient :=
    graphSourceLiftMomentConstant parameters L compact 1 * state.val.val.size 1 *
      fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
        uniformSourceOuterConstant
  have bulkNonnegative : 0 ≤ bulkCoefficient :=
    mul_nonneg (mul_nonneg (by norm_num)
      (eliminatedBulkConstant_nonnegative parameters L compact 0))
      (state.val.val.size_nonnegative 1)
  have datumNonnegative : 0 ≤ datumCoefficient :=
    mul_nonneg (knownBoundaryInverseConstant_nonnegative parameters L compact 1)
      (state.val.val.size_nonnegative 1)
  have graphNonnegative : 0 ≤ graphCoefficient :=
    mul_nonneg (mul_nonneg (mul_nonneg
      (graphSourceLiftMomentConstant_nonnegative parameters L compact 1)
      (state.val.val.size_nonnegative 1))
      (fullKernelMoment_nonnegative parameters 1 _))
      uniformSourceOuterConstant_nonnegative
  have bulkPart :
      bulkCoefficient * ‖actualHighKnownWeighted parameters lower positive bounded 0 0 data‖ +
          3 * ‖actualHighKnownAuxiliary parameters lower positive bounded 0 0 data‖ ≤
        (bulkCoefficient + 3) * ‖data‖ := by
    have first := mul_le_mul_of_nonneg_left knownBound bulkNonnegative
    have second := mul_le_mul_of_nonneg_left auxiliaryBound (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have boundaryPart :
      datumCoefficient * ‖actualHighKnownDatum parameters lower positive bounded 0 0 data‖ +
          graphCoefficient *
            (2 * ‖actualHighKnownF0Graph parameters lower positive bounded 0 0 data‖ +
              ‖actualHighKnownF2Graph parameters lower positive bounded 0 0 data‖) ≤
        (datumCoefficient + 3 * graphCoefficient) * ‖data‖ := by
    have first := mul_le_mul_of_nonneg_left datumBound datumNonnegative
    have second := mul_le_mul_of_nonneg_left graphBound graphNonnegative
    nlinarith
  have bulkScaled := mul_le_mul_of_nonneg_left bulkPart (by norm_num : (0 : ℝ) ≤ 5)
  have boundaryScaled := mul_le_mul_of_nonneg_left boundaryPart
    (uniformOuterTraceConstant_nonnegative L)
  unfold actualHighKnownCarrierB8Size actualHighGraphKnownB8Size
  unfold actualHighKnownBF13Constant
  change 5 * (bulkCoefficient * _ + 3 * _) +
    uniformOuterTraceConstant L * (datumCoefficient * _ + graphCoefficient * _) ≤ _
  dsimp only [bulkCoefficient, datumCoefficient, graphCoefficient] at bulkScaled boundaryScaled ⊢
  calc
    _ ≤ 5 * ((4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 1 + 3) * ‖data‖) +
        uniformOuterTraceConstant L *
          ((knownBoundaryInverseConstant parameters L compact 1 * state.val.val.size 1 +
            3 * (graphSourceLiftMomentConstant parameters L compact 1 * state.val.val.size 1 *
              fullKernelMoment parameters 1 (sourceTupleProjectionKernel parameters) *
                uniformSourceOuterConstant)) * ‖data‖) :=
      add_le_add bulkScaled boundaryScaled
    _ = _ := by ring

/-- The exact accepted AEK component size itself is controlled by the single
Hilbert norm.  This is the form consumed by the full high response estimate. -/
theorem ActualHighKnownCarrier.functionalSize_le_single_norm
    (data : ActualHighKnownCarrier parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0) :
    (ActualHighKnownCarrier.toGraphKnownData parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0 data).functionalSize
        parameters L compact lower state 0 0 ≤
      actualHighKnownBF13Constant parameters L compact state * ‖data‖ := by
  exact (actualHighGraphKnownFunctionalSize_base_le_B8 parameters L compact lower state
    (actualHighKnownWeighted parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0 data)
    (actualHighKnownAuxiliary parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0 data)
    (ActualHighKnownCarrier.graphs parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0 data)
    (actualHighKnownDatum parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0 data)).trans
    (actualHighKnownCarrierB8Size_le_single_norm parameters L compact lower positive
      lowerHalf state data)

/-- Exact BF13 on the complete original high datum: the accepted literal
functional has a uniform operator norm bounded by one constant times the
single Hilbert data norm. -/
theorem ActualHighKnownCarrier.zeroFunctional_norm_BF13
    (data : ActualHighKnownCarrier parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0) :
    ‖ActualHighKnownCarrier.zeroFunctional parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state data‖ ≤
      actualHighKnownBF13Constant parameters L compact state * ‖data‖ := by
  exact ((ActualHighKnownCarrier.toGraphKnownData parameters lower positive
    (lowerHalf.trans (by norm_num)) 0 0 data).zeroFunctional_norm_base_B8
      parameters L compact lower positive lowerHalf lengthPositive widthHalf
        widthLength state).trans
    (actualHighKnownCarrierB8Size_le_single_norm parameters L compact lower positive
      lowerHalf state data)

/-- State-independent complete-data BF13 component bound on the physical B8
ball.  The coefficient is fixed before the background state and collar. -/
theorem ActualHighKnownCarrier.functionalSize_le_ball_single_norm
    (small : physicalBudget parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon 8 ≤ 1)
    (data : ActualHighKnownCarrier parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0) :
    (ActualHighKnownCarrier.toGraphKnownData parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0 data).functionalSize
        parameters L compact lower state 0 0 ≤
      actualHighKnownBF13BallConstant parameters L compact * ‖data‖ := by
  exact (ActualHighKnownCarrier.functionalSize_le_single_norm parameters L compact lower positive
    lowerHalf state data).trans (mul_le_mul_of_nonneg_right
      (actualHighKnownBF13Constant_le_ball parameters L compact state small)
      (norm_nonneg data))

/-- State-independent operator-norm form of BF13 on the same B8 ball. -/
theorem ActualHighKnownCarrier.zeroFunctional_norm_ball_BF13
    (small : physicalBudget parameters state.val.val.field state.val.val.rho
      state.val.val.epsilon 8 ≤ 1)
    (data : ActualHighKnownCarrier parameters lower positive
      (lowerHalf.trans (by norm_num)) 0 0) :
    ‖ActualHighKnownCarrier.zeroFunctional parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state data‖ ≤
      actualHighKnownBF13BallConstant parameters L compact * ‖data‖ := by
  exact (ActualHighKnownCarrier.zeroFunctional_norm_BF13 parameters L compact lower positive
    lowerHalf lengthPositive widthHalf widthLength state data).trans
      (mul_le_mul_of_nonneg_right
        (actualHighKnownBF13Constant_le_ball parameters L compact state small)
        (norm_nonneg data))

end Base

end Grad.AnnularCurrentSource
