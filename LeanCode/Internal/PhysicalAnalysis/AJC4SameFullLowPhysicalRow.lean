import AJC3OnceOnlyPhysicalInput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentSource Grad.AnnularStrongData Grad.AnnularFullSource
open Grad.AnnularCrossMaps Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularLowCompletion Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

private theorem assemblePhysicalRows {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (J C V : E →L[ℂ] F) (first cell angular : F →L[ℂ] G)
    (high low known : E) (f rg : F) (diagonal : G) :
    (diagonal + (first (J low) + cell (C low) + angular (V low))) +
      (first (J known + f) + cell (C known) + angular (V known - rg)) +
      (first (J high) + cell (C high) + angular (V high)) =
    diagonal + first (J (high + low + known) + f) + cell (C (high + low + known)) +
      angular (V (high + low + known) - rg) := by
  simp only [map_add, map_sub]
  abel

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L)
    (state : RetainedInverseState parameters L compact)

/-- The original normalized low physical residual, evaluated on ONE full
seven-slot reconstruction. f and g retain all their original modes. -/
def strongLowPhysicalRHS
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) : LowEnergyBulk lower :=
  let input := fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution
  let known := strongKnownBulk parameters lower positive bounded data
  let g := (strongToLow parameters lower positive bounded 0 0 data).ofLp.1.ofLp.2
  lowCommonDiagonal parameters L lower lengthPositive positive (solution.ofLp.2.val 0) +
    lowFirstOutput parameters lower L
      (lowPhysicalRowAction parameters L compact lower positive bounded state 0 input + highSourceF lower known) +
    lowCellOutput lower L positive
      (lowPhysicalRowAction parameters L compact lower positive bounded state 1 input) +
    lowAngularOutput lower L positive
      (lowPhysicalRowAction parameters L compact lower positive bounded state 2 input - radialRadiusRow lower positive g)

theorem strongLowPhysicalRHS_decomposition
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    strongLowPhysicalRHS parameters L compact lower positive bounded lengthPositive state data solution =
      lowCurrentBulk parameters L compact lower lengthPositive positive bounded state (solution.ofLp.2.val 0) +
      knownLowForcing parameters L compact lower positive bounded state
        (strongKnownBulk parameters lower positive bounded data)
        (strongToLow parameters lower positive bounded 0 0 data).ofLp.1.ofLp.2 +
      highToLowBulkCross parameters lower L compact lengthPositive positive bounded state solution.ofLp.1 := by
  exact (assemblePhysicalRows
    (lowPhysicalRowAction parameters L compact lower positive bounded state 0)
    (lowPhysicalRowAction parameters L compact lower positive bounded state 1)
    (lowPhysicalRowAction parameters L compact lower positive bounded state 2)
    (lowFirstOutput parameters lower L) (lowCellOutput lower L positive) (lowAngularOutput lower L positive)
    (highCrossSevenInput lower L positive lengthPositive solution.ofLp.1)
    (lowNormalizedSevenInput parameters lower L lengthPositive positive (solution.ofLp.2.val 0))
    (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded data))
    (highSourceF lower (strongKnownBulk parameters lower positive bounded data))
    (radialRadiusRow lower positive (strongToLow parameters lower positive bounded 0 0 data).ofLp.1.ofLp.2)
    (lowCommonDiagonal parameters L lower lengthPositive positive (solution.ofLp.2.val 0))).symm

omit bounded in
/-- The derivative coordinate of the SAME original completed low graph
satisfies the full original low equation with the once-only physical input. -/
theorem sharedStrongResponse_fullLowRow (lowerHalf : lower ≤ 1 / 2)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    let solution := sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    solution.ofLp.2.val 1 =
      strongLowPhysicalRHS parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state data solution := by
  dsimp only
  rw [strongLowPhysicalRHS_decomposition]
  exact coupledKnownResponse_lowSlope parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
      (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data))
    (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data)

end Grad.AnnularStrongSolution
