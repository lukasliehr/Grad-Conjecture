import AKCQ13ActualSigmaEulerAllocation
import AKCQ14ActualGaugeEulerAllocation
import GC15BudgetAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Allocation

/-- Physical interpolation is applied before multiplying coarse moments.
Reference contributions are included without introducing a high-high term. -/
theorem referencePhysicalBudget_pair (parameters : PhaseParameters) (field : ACore parameters 3)
    (rho epsilon : ℝ) (offset total first second : ℕ) (allocated : first+second ≤ total)
    (low : physicalBudget parameters field rho epsilon offset ≤ 1) :
    (1+physicalBudget parameters field rho epsilon (offset+first)) *
      (1+physicalBudget parameters field rho epsilon (offset+second)) ≤
        (3+pairBudgetConstant offset total 1) *
          (1+physicalBudget parameters field rho epsilon (offset+total)) := by
  have firstLe := physicalBudget_monotone parameters field rho epsilon (show offset+first ≤ offset+total by omega)
  have secondLe := physicalBudget_monotone parameters field rho epsilon (show offset+second ≤ offset+total by omega)
  have product := physical_budget_pair offset total first second allocated parameters field rho epsilon 1 zero_le_one low
  have budget0 := physicalBudget_nonnegative parameters field rho epsilon (offset+total)
  have constant0 := pairBudgetConstant_nonnegative offset total (lowBound := (1 : ℝ)) zero_le_one
  nlinarith

/-- An ordered full-kernel product, with its raw ranks still separate.
Each of the two moment allocations spends at most outerRank+innerRank+moment.
The actual full composition and original radius/phase are retained. -/
theorem fullKernelComposition_joint_oneHigh {source middle target : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (radius : RadialPoint) (offset total outerRank innerRank moment : ℕ)
    (allocated : outerRank+innerRank+moment ≤ total)
    (low : physicalBudget parameters field rho epsilon offset ≤ 1)
    (outer : RadialKernel parameters radius middle target)
    (inner : RadialKernel parameters radius source middle)
    (outerHigh outerLow innerHigh innerLow : ℝ)
    (outerHigh0 : 0 ≤ outerHigh) (outerLow0 : 0 ≤ outerLow)
    (innerHigh0 : 0 ≤ innerHigh) (innerLow0 : 0 ≤ innerLow)
    (outerMoment : fullKernelMoment (radialKernelParameters parameters radius) moment outer ≤
      outerHigh*(1+physicalBudget parameters field rho epsilon (offset+(outerRank+moment))))
    (outerBase : fullKernelMoment (radialKernelParameters parameters radius) 0 outer ≤
      outerLow*(1+physicalBudget parameters field rho epsilon (offset+outerRank)))
    (innerMoment : fullKernelMoment (radialKernelParameters parameters radius) moment inner ≤
      innerHigh*(1+physicalBudget parameters field rho epsilon (offset+(innerRank+moment))))
    (innerBase : fullKernelMoment (radialKernelParameters parameters radius) 0 inner ≤
      innerLow*(1+physicalBudget parameters field rho epsilon (offset+innerRank))) :
    fullKernelMoment (radialKernelParameters parameters radius) moment (fullKernelComposition outer inner) ≤
      (2^moment*(outerHigh*innerLow+outerLow*innerHigh)*(3+pairBudgetConstant offset total 1)) *
        (1+physicalBudget parameters field rho epsilon (offset+total)) := by
  have one := mul_le_mul outerMoment innerBase (fullKernelMoment_nonnegative _ _ _)
    (mul_nonneg outerHigh0 (by have := physicalBudget_nonnegative parameters field rho epsilon (offset+(outerRank+moment)); linarith))
  have two := mul_le_mul outerBase innerMoment (fullKernelMoment_nonnegative _ _ _)
    (mul_nonneg outerLow0 (by have := physicalBudget_nonnegative parameters field rho epsilon (offset+outerRank); linarith))
  have firstPaid := mul_le_mul_of_nonneg_left
    (referencePhysicalBudget_pair parameters field rho epsilon offset total (outerRank+moment) innerRank (by omega) low)
    (mul_nonneg outerHigh0 innerLow0)
  have secondPaid := mul_le_mul_of_nonneg_left
    (referencePhysicalBudget_pair parameters field rho epsilon offset total outerRank (innerRank+moment) (by omega) low)
    (mul_nonneg outerLow0 innerHigh0)
  have first : fullKernelMoment (radialKernelParameters parameters radius) moment outer *
      fullKernelMoment (radialKernelParameters parameters radius) 0 inner ≤
      (outerHigh*innerLow)*((3+pairBudgetConstant offset total 1)*
        (1+physicalBudget parameters field rho epsilon (offset+total))) := by
    apply one.trans
    convert firstPaid using 1; ring
  have second : fullKernelMoment (radialKernelParameters parameters radius) 0 outer *
      fullKernelMoment (radialKernelParameters parameters radius) moment inner ≤
      (outerLow*innerHigh)*((3+pairBudgetConstant offset total 1)*
        (1+physicalBudget parameters field rho epsilon (offset+total))) := by
    apply two.trans
    convert secondPaid using 1; ring
  exact (fullKernelComposition_moment_le moment outer inner).trans
    ((mul_le_mul_of_nonneg_left (add_le_add first second) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) moment)).trans_eq (by ring))

end Grad.OriginalCartesianTameEstimate
