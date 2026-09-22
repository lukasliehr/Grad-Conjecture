import AKCH3SameOriginalCovariantCore
import AKBD26SameCartesianSignedCofactorFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped Topology
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.ActualSmoothPhysicalField Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay Grad.NonlinearRange
open Grad.ActualCurrentPrimitives Grad.ActualCartesianDescent Grad.SourceCollar
open Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelHomogeneousGraph Grad.ActualDeterminantEquations Grad.Constraints Grad.NonlinearQuotientBounds

/-- The native signed cofactor convolution equals the actual original smooth
core flux, from SAME physical values alone. Coefficients act before selection. -/
theorem nativeCofactor_sameOriginalCore (parameters : PhaseParameters) (length compact : ℝ)
    (nonzero : length≠0) (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))
    (vector : ACore parameters 3) (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ)
    (same : ((curves.covariant parameters length compact lower positive bounded state.val).physicalUFromPolar
      parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small lower positive bounded).fullField bounded (radius,angles)=
      coreValue vector (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2) :
    coreValue (originalCartesianCofactorFluxCore length physicalState vector)
      (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2=
      (samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.fullField bounded (radius,angles) := by
  have covariant := nativeCovariant_sameOriginalCore parameters length state.val.val.rho state.val.val.epsilon nonzero
    state.val.val.field small lower positive bounded (curves.covariant parameters length compact lower positive bounded state.val)
    vector radius inside angles same
  rw [originalCovariantCore_value parameters length state.val.val.epsilon nonzero state.val.val.field vector,
    SmoothLowPhysicalRow.fullField_cartesianCovariant bounded _ radius inside angles] at covariant
  rw [← originalCartesianCofactorFlux_value parameters length state.val.val.rho state.val.val.epsilon nonzero
    state.val.val.field small physicalState sameBase sameEpsilon vector,
    sameCartesianCofactorFlux_literal parameters length compact lower positive bounded state curves radius inside angles]
  exact congrArg (fun value : ComplexEuclidean 3 => WithLp.toLp 2
    ((originalPhysicalSignedCofactor parameters length state.val.val.epsilon state.val.val.field angles.2
      (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)).mulVec value)) covariant

end Grad.OriginalCoreRealization
