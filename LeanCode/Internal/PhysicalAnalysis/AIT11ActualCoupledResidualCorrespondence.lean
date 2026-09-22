import AIT10ActualCoupledNeumannInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.AnnularPhysicalSolution Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (lower length compact : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
  (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
  (state : RetainedInverseState parameters length compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

/-- Both fixed-point coordinates use the SAME original diagonal response. -/
theorem actualCoupledInverse_coordinates (known : CoupledSpace lower length positive lengthPositive) :
    let solution := actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known
    solution.ofLp.1 = known.ofLp.1 +
      actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state
        (coupledPrimitive_highSmall parameters length compact state small) solution.ofLp.2 ∧
    solution.ofLp.2 = known.ofLp.2 +
      actualLowOffDiagonal parameters lower length compact lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state solution.ofLp.1 := by
  have fixed := actualCoupledInverse_fixedPoint parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known
  exact ⟨congrArg (fun field : CoupledSpace lower length positive lengthPositive => field.ofLp.1) fixed,
    congrArg (fun field : CoupledSpace lower length positive lengthPositive => field.ofLp.2) fixed⟩

/-- The high residual is exactly the physical cross response in W × Domega. -/
theorem actualCoupledInverse_highResidual (known : CoupledSpace lower length positive lengthPositive) :
    let solution := actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known
    solution.ofLp.1 - known.ofLp.1 =
      actualHighCrossResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (coupledPrimitive_highSmall parameters length compact state small)
        (lowToHighCross parameters lower length compact lengthPositive positive lowerHalf state solution.ofLp.2) := by
  dsimp only
  have high := (actualCoupledInverse_coordinates parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known).1
  change _ = known.ofLp.1 + _ at high
  rw [high]
  abel

/-- The lower residual uses the actual current Cauchy operator, with its
physical normalized source and genuine incoming included together. -/
theorem actualCoupledInverse_lowResidual (known : CoupledSpace lower length positive lengthPositive) :
    let solution := actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known
    lowCurrentDataOperator parameters length compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state solution.ofLp.2 =
      lowCurrentDataOperator parameters length compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state known.ofLp.2 +
      highToLowCross parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state solution.ofLp.1 := by
  let solution := actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known
  let forward := lowCurrentDataOperator parameters length compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
  let correction := actualLowOffDiagonal parameters lower length compact lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state solution.ofLp.1
  have fixed : solution.ofLp.2 = known.ofLp.2 + correction :=
    (actualCoupledInverse_coordinates parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known).2
  have mapped : forward solution.ofLp.2 = forward (known.ofLp.2 + correction) := congrArg forward fixed
  have response : forward correction =
      highToLowCross parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state solution.ofLp.1 :=
    actualLowOffDiagonal_equation parameters lower length compact lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
      (coupledPrimitive_lowSmall parameters length compact state small) solution.ofLp.1
  exact mapped.trans ((map_add forward known.ofLp.2 correction).trans
    (congrArg (fun data : LowEnergyData lower => forward known.ofLp.2 + data) response))

/-- Arbitrary original Xalpha candidates with these SAME actual high and
low residual equations agree; no regularity or density premise is added. -/
theorem actualCoupledInverse_residual_unique (known candidate : CoupledSpace lower length positive lengthPositive)
    (high : candidate.ofLp.1 = known.ofLp.1 +
      actualHighOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state
        (coupledPrimitive_highSmall parameters length compact state small) candidate.ofLp.2)
    (low : lowCurrentDataOperator parameters length compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state candidate.ofLp.2 =
      lowCurrentDataOperator parameters length compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state known.ofLp.2 +
      highToLowCross parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state candidate.ofLp.1) :
    candidate = actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known := by
  have lowFixed := congrArg
    (lowCurrentInverse parameters length compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state) low
  rw [lowCurrentInverse_dataOperator parameters length compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
    (coupledPrimitive_lowSmall parameters length compact state small), map_add,
    lowCurrentInverse_dataOperator parameters length compact lower lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
      (coupledPrimitive_lowSmall parameters length compact state small)] at lowFixed
  apply actualCoupledInverse_unique parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known candidate
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  exact Prod.ext high lowFixed

/-- The coupled correction does not alter the prescribed genuine low trace. -/
theorem actualCoupledInverse_incoming (known : CoupledSpace lower length positive lengthPositive) :
    lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      (actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known).ofLp.2 =
      lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num)) known.ofLp.2 := by
  rw [(actualCoupledInverse_coordinates parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known).2,
    map_add, actualLowOffDiagonal_incoming parameters lower length compact lengthPositive positive (lowerHalf.trans_lt (by norm_num)) state
      (coupledPrimitive_lowSmall parameters length compact state small), add_zero]

end Grad.AnnularCoupledInverse
