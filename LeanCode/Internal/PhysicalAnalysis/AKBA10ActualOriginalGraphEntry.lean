import AKBA9LiteralKernelTupleFields
import AKR37LiteralTotalCoreOriginalGraphClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.AnnularOriginalCoreRealization
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularFullGraph Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower)
    (domain : lower≤min (1/2) length) (lengthPositive : 0<length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤coupledPrimitiveRadius parameters length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤originalCoefficientLowRadius parameters length)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)

def originalPhysicalKernelGraphPoint : OriginalFiveBlockAmbient parameters lower length positive :=
  literalOriginalCoreGraphMap parameters length compact lower positive domain lengthPositive state
    (originalKernelSmoothTuple parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive
      ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) total vector scalar)

include small in
/-- The actual original smooth physical restriction lies in the immutable
original equation graph. Its F1/G3 coordinates are the genuine computed
residuals; their vanishing still requires the original homogeneous equations. -/
theorem originalPhysicalKernelGraphPoint_member :
    originalPhysicalKernelGraphPoint parameters length compact lower positive domain lengthPositive state coefficientSmall total vector scalar ∈
      OriginalObservedEquationGraph parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
        widthHalf widthLength state :=
  everyLiteralTuple_originalEquation parameters length compact lower positive domain lengthPositive widthHalf widthLength state small _

theorem originalPhysicalKernelGraphPoint_represents :
    OriginalTupleObservation parameters length compact lower positive
      ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive state
      (originalKernelSmoothTuple parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive
        ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) total vector scalar)
      (originalPhysicalKernelGraphPoint parameters length compact lower positive domain lengthPositive state coefficientSmall total vector scalar) :=
  originalTupleGraphLinear_represents parameters length compact lower positive
    ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive state _

end Grad.OriginalKernelGraphRestriction
