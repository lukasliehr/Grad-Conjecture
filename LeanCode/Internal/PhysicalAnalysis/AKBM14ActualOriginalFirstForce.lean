import AKBM13ActualOriginalCovariantDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ActualPolarEquations Grad.ActualCartesianEquations Grad.SourceCollarFullSource
open Grad.NonlinearRange
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.Constraints Grad.Cor18
open Grad.OriginalKernelCovariantRecovery Grad.AnnularPhysicalReconstruction Grad.ActualDeterminantEquations
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.SourceCollar Grad.FinitePhysicalJetLift

variable (parameters : PhaseParameters) (compact : ℝ) (nonzero : parameters.length≠0)
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalCoefficientLowRadius parameters parameters.length)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)


include nonzero sameBase sameEpsilon constrained homogeneous



/-- The SAME physical first force identity before any derivative notation. -/
theorem originalHomogeneous_sevenFirstForce (radius : Icc lower (1:ℝ)) (angles : ℝ×ℝ) :
    let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar
    let covariant := seven.covariant parameters parameters.length compact lower positive bounded state.val
    let rotated := seven.rotatedCovariant parameters parameters.length compact lower positive bounded state.val
    (physicalForceCurves parameters parameters.length compact lower positive bounded state.val 0 covariant).fullField bounded (radius.val,angles) 0+
      seven.fullField bounded (radius.val,angles) 1-2*covariant.fullField bounded (radius.val,angles) 0-
      rotated.fullField bounded (radius.val,angles) 1=0 := by
  dsimp only
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let covariant := seven.covariant parameters parameters.length compact lower positive bounded state.val
  let rotated := seven.rotatedCovariant parameters parameters.length compact lower positive bounded state.val
  let force := physicalForceCurves parameters parameters.length compact lower positive bounded state.val 0 covariant
  let residual := ((force.add (seven.bulkUnit (0:Fin 1) 1)).sub ((covariant.bulkUnit (0:Fin 1) 0).smul 2)).sub
    (rotated.bulkUnit (0:Fin 1) 1)
  have zero : originalCurveNegativeTrace residual radius=0 := by
    dsimp only [residual]
    simp only [originalCurveNegativeTrace_sub,originalCurveNegativeTrace_add,originalCurveNegativeTrace_smul]
    rw [originalKernelSevenSlot_negative]
    simp only [force,originalCurveNegativeTrace_force,originalCurveNegativeTrace_bulkUnit,covariant,rotated,seven,
      originalKernelSevenCurves_covariant,originalKernelSevenCurves_rotated]
    rw [← originalHomogeneous_covariantRecovery parameters compact nonzero state small insideSeed lower positive bounded physicalState
        sameBase sameEpsilon vector scalar constrained homogeneous radius,
      originalHomogeneous_rotatedCovariantRecovery parameters compact nonzero state small insideSeed lower positive bounded physicalState
        sameBase sameEpsilon vector scalar constrained homogeneous radius,
      originalKernelTuple_normalizedInput]
    have actual := originalHomogeneous_negativeFirst parameters parameters.length compact nonzero state.val small lower positive bounded vector radius
      physicalState sameBase scalar homogeneous
    simp only [forceCoordinateTrace,coordinateProjectionKernel] at actual
    have reorder (f q a r : NegativeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 1) :
        f+q-a-r= -r-a+f+q := by abel
    exact (reorder _ _ _ _).trans actual
  have evaluated := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (originalCurveFullField_zero_of_negative residual bounded radius zero angles)
  simp only [residual,SmoothLowPhysicalRow.fullField_sub _ bounded _ radius.val radius.property angles,
    SmoothLowPhysicalRow.fullField_add _ bounded _ radius.val radius.property angles,
    samePhysical_fullField_smul _ bounded 2 radius.val radius.property angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius.val radius.property angles,
    PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,matrixUnit_apply,operatorBasis,ite_true,smul_eq_mul,mul_one] at evaluated
  exact evaluated

end Grad.OriginalKernelHomogeneousGraph
