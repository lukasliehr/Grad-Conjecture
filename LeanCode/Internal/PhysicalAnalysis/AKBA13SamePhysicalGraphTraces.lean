import AKBA12ActualCopiedSourcesVanish

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.AnnularOriginalCoreRealization
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularFullGraph Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.OriginalKernelRetainedDecay

theorem originalCircleRotation_coefficient {dimension : ℕ} (parameters : PhaseParameters) (radius : ℝ)
    {field rotated : CellL2 dimension} (rotation : OriginalCircleRotation field rotated) (mode : ℤ × ℤ) :
    lambdaCircleCoefficient parameters radius rotated mode =
      (Complex.I*(mode.1 : ℂ)) • lambdaCircleCoefficient parameters radius field mode := by
  rw [lambdaCircleCoefficient,rotation mode,smul_comm]
  rfl

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0<lower)
    (domain : lower≤min (1/2) length) (lengthPositive : 0<length)
    (state : RetainedInverseState parameters length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤originalCoefficientLowRadius parameters length)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)

/-- At every closed collar radius the graph scalar is precisely the same
original weighted scalar from the Cartesian field. -/
theorem originalPhysicalKernelGraphPoint_Xi (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXiCoefficient parameters lower length positive
      ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive
      (originalCoupledEquivalence parameters lower length positive
        ((domain.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
        (originalPhysicalKernelGraphPoint parameters length compact lower positive domain lengthPositive state coefficientSmall total vector scalar).ofLp.1)
      0 radius mode =
      lambdaCircleCoefficient parameters radius.val
        (originalCoreCircleTrace parameters (originalKernelXi total vector scalar)
          ⟨radius.val,positive.le.trans radius.property.1,radius.property.2⟩) mode := by
  rw [← (originalPhysicalKernelGraphPoint_represents parameters length compact lower positive domain lengthPositive state coefficientSmall total vector scalar).scalar radius mode]
  exact originalKernelSmoothTuple_scalarCoefficient parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive
    ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) total vector scalar radius.val radius.property mode

/-- The graph x coordinate is the SAME actual Rp, including both endpoint
traces. Thus the accepted original A4 decay applies to this exact coordinate. -/
theorem originalPhysicalKernelGraphPoint_X (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXCoefficient parameters lower length positive
      ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive
      (originalCoupledEquivalence parameters lower length positive
        ((domain.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
        (originalPhysicalKernelGraphPoint parameters length compact lower positive domain lengthPositive state coefficientSmall total vector scalar).ofLp.1)
      0 radius mode =
      lambdaCircleCoefficient parameters radius.val
        (originalKernelPhysicalX parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
          ⟨radius.val,positive.le.trans radius.property.1,radius.property.2⟩ total vector scalar) mode := by
  let bounded : lower<1 := (domain.trans (min_le_left _ _)).trans_lt (by norm_num)
  let tuple := originalKernelSmoothTuple parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive bounded total vector scalar
  change sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
    (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive) 0 radius mode = _
  rw [tupleWeightedRetained_X]
  rw [originalKernelSmoothTuple_pressureCoefficient parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive bounded total vector scalar radius.val radius.property mode]
  exact (originalCircleRotation_coefficient parameters radius.val
    (originalKernelPhysicalX_is_rotation parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      ⟨radius.val,positive.le.trans radius.property.1,radius.property.2⟩ total vector scalar) mode).symm

end Grad.OriginalKernelGraphRestriction
