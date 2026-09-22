import AKBM18ActualOriginalRemainingAngularRows
import AKBM9ActualProjectedPolarDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set Filter
open scoped Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ActualPolarFlux
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



/-- Full AD13--AD17 cancellation for the original homogeneous physical
field, with the two variable-coefficient projections kept in their places. -/
theorem originalHomogeneous_projectedRawScalar_zero (radius : ℝ) (inside : radius∈Ioo lower 1) (angles : ℝ×ℝ) :
    let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar
    removePolarMean (fun query =>
      scalarDirectionalField (rawCorrectedPCurves parameters parameters.length compact lower positive bounded state seven) bounded 0 (1,0,0) (radius,query)+
      (rawCorrectedPCurves parameters parameters.length compact lower positive bounded state seven).fullField bounded (radius,query) 0/(radius:ℂ)+
      scalarDirectionalField (seven.bThree parameters parameters.length compact lower positive bounded state) bounded 0 (0,0,1) (radius,query)/(parameters.length:ℂ)+
      retainedRVRawField parameters parameters.length compact lower positive bounded state seven radius query 0/(radius:ℂ)) angles=0 := by
  dsimp only
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  have expanded (query : ℝ×ℝ) := originalDeterminant_productExpansion parameters parameters.length compact lower positive bounded state seven
    nonzero radius inside query.1 query.2
    (originalHomogeneous_firstAngularRow parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous radius inside query.1 query.2)
    (originalHomogeneous_secondAngularRow parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous radius inside query.1 query.2)
    (originalHomogeneous_thirdAngularRow parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous radius inside query.1 query.2)
    (originalSmoothSeven_scalarAngular bounded pressure xi radius inside query.1 query.2)
  have same := funext expanded
  rw [same]
  exact originalHomogeneous_projectedPolarDivergence_zero parameters compact nonzero state small insideSeed lower positive bounded physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous radius inside angles

end Grad.OriginalKernelHomogeneousGraph
