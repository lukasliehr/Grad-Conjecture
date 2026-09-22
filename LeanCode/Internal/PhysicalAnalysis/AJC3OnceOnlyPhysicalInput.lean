import AJC2SharedStrongCoupledInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentSource Grad.AnnularStrongData Grad.AnnularFullSource
open Grad.AnnularCrossMaps Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularLowCompletion

private theorem threePacketBound {E : Type*} [NormedAddCommGroup E]
    (high low known : E) (L solutionSize dataSize : ℝ)
    (highBound : ‖high‖ ≤ (4 + 2 * L) * solutionSize)
    (lowBound : ‖low‖ ≤ (7 + 2 * L) * solutionSize)
    (knownBound : ‖known‖ ≤ 3 * dataSize) :
    ‖high + low + known‖ ≤ (11 + 4 * L) * solutionSize + 3 * dataSize := by
  exact (norm_add_le _ _).trans
    ((add_le_add (norm_add_le _ _) le_rfl).trans (by linarith only [highBound, lowBound, knownBound]))

/-- The same prescribed full F0/RF0/F2/f tuple used in both diagonal solvers. -/
def strongKnownBulk (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) : HighKnownSourceBulk lower :=
  (strongToLow parameters lower positive bounded 0 0 data).ofLp.1.ofLp.1

theorem strongKnownBulk_bound (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ‖strongKnownBulk parameters lower positive bounded data‖ ≤ ‖data‖ :=
  (knownLowData_component_bounds lower (strongToLow parameters lower positive bounded 0 0 data)).1.trans
    (strongToLow_bound parameters lower positive bounded 0 0 data)

/-- The free high and low physical variables occupy slots 0--3. -/
def homogeneousCoupledSevenInput (parameters : PhaseParameters) (L lower : ℝ)
    (lengthPositive : 0 < L) (positive : 0 < lower) :
    CoupledSpace lower L positive lengthPositive →L[ℂ] DivisionRow 7 lower :=
  (highCrossSevenInput lower L positive lengthPositive).comp (coupledHigh lower L positive lengthPositive) +
    (lowNormalizedSevenInput parameters lower L lengthPositive positive).comp
      ((lowStoredCoordinate lower L positive 0).comp (coupledLow lower L positive lengthPositive))

/-- One physical seven-slot input: the two homogeneous field pieces plus
the prescribed F0/RF0/F2 tuple exactly once, in slots 4--6. -/
def fullStrongSevenInput (parameters : PhaseParameters) (L lower : ℝ)
    (lengthPositive : 0 < L) (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) : DivisionRow 7 lower :=
  homogeneousCoupledSevenInput parameters L lower lengthPositive positive solution +
    knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded data)

theorem fullStrongSevenInput_exact (parameters : PhaseParameters) (L lower : ℝ)
    (lengthPositive : 0 < L) (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution =
      highCrossSevenInput lower L positive lengthPositive solution.ofLp.1 +
      lowNormalizedSevenInput parameters lower L lengthPositive positive (solution.ofLp.2.val 0) +
      knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded data) := rfl

/-- The common weighted physical input has a radius-independent estimate
in the original complete coupled norm and the single strong-data norm. -/
theorem fullStrongSevenInput_bound (parameters : PhaseParameters) (L lower : ℝ)
    (lengthPositive : 0 < L) (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    ‖fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution‖ ≤
      (11 + 4 * L) * ‖solution‖ + 3 * ‖data‖ := by
  have high := (highCrossSevenInput_bound lower L positive lengthPositive solution.ofLp.1).trans
    (mul_le_mul_of_nonneg_left (coupledHigh_bound lower L positive lengthPositive solution)
      (by positivity : 0 ≤ 4 + 2 * |L|))
  rw [abs_of_pos lengthPositive] at high
  have lowValue := (lowStoredCoordinate_bound lower L positive 0 solution.ofLp.2).trans
    (coupledLow_bound lower L positive lengthPositive solution)
  have low := (lowNormalizedSevenInput_bound parameters lower L lengthPositive positive (solution.ofLp.2.val 0)).trans
    (mul_le_mul_of_nonneg_left lowValue (by positivity : 0 ≤ 7 + 2 * L))
  have known := (knownLowSevenPacket_bound lower (strongKnownBulk parameters lower positive bounded data)).trans
    (mul_le_mul_of_nonneg_left (strongKnownBulk_bound parameters lower positive bounded data) (by norm_num : (0 : ℝ) ≤ 3))
  exact threePacketBound _ _ _ L ‖solution‖ ‖data‖ high low known

end Grad.AnnularStrongSolution
