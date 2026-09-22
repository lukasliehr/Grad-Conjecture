import AKBM17ActualOriginalFirstAngularRow

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



/-- The original first quotient force gives the second angular row. -/
theorem originalHomogeneous_secondAngularRow (radius : ℝ) (inside : radius∈Ioo lower 1) (polar axial : ℝ) :
    let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar
    let covariant := seven.covariant parameters parameters.length compact lower positive bounded state.val
    scalarDirectionalField covariant bounded 1 (0,1,0) (radius,polar,axial)=
      scalarDirectionalField seven bounded 3 (0,1,0) (radius,polar,axial)+
      (covariant.forceZero parameters parameters.length compact lower positive bounded state).fullField bounded (radius,polar,axial) 0 := by
  dsimp only
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let covariant := seven.covariant parameters parameters.length compact lower positive bounded state.val
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  have law := originalHomogeneous_sevenFirstForce parameters compact nonzero state small insideSeed lower positive bounded physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous ⟨radius,closed⟩ (polar,axial)
  have angular := originalSmoothSeven_scalarAngular bounded pressure xi radius inside polar axial
  change scalarDirectionalField seven bounded 3 (0,1,0) (radius,polar,axial)=seven.fullField bounded (radius,polar,axial) 1 at angular
  change scalarDirectionalField covariant bounded 1 (0,1,0) (radius,polar,axial)=_
  rw [originalKernelSevenCovariant_scalarAngular parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar compact state 1 radius inside polar axial,
    angular,fullField_originalForceZero parameters parameters.length compact lower positive bounded state covariant radius closed (polar,axial)]
  dsimp only at law
  linear_combination -law

/-- The original fourth quotient force gives the third angular row. -/
theorem originalHomogeneous_thirdAngularRow (radius : ℝ) (inside : radius∈Ioo lower 1) (polar axial : ℝ) :
    let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar
    let covariant := seven.covariant parameters parameters.length compact lower positive bounded state.val
    scalarDirectionalField covariant bounded 2 (0,1,0) (radius,polar,axial)=
      (radius:ℂ)/(parameters.length:ℂ)*scalarDirectionalField seven bounded 3 (0,0,1) (radius,polar,axial)-
      removePolarMean (fun angles => (physicalForceCurves parameters parameters.length compact lower positive bounded state.val 1 covariant).fullField bounded (radius,angles) 0) (polar,axial) := by
  dsimp only
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let covariant := seven.covariant parameters parameters.length compact lower positive bounded state.val
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  let force := physicalForceCurves parameters parameters.length compact lower positive bounded state.val 1 covariant
  have law := originalHomogeneous_sevenThirdForce parameters compact nonzero state small insideSeed lower positive bounded physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous ⟨radius,closed⟩ (polar,axial)
  dsimp only at law
  change (seven.rotatedCovariant parameters parameters.length compact lower positive bounded state.val).fullField bounded (radius,polar,axial) 2+
    (removePolarMean (fun query => force.fullField bounded (radius,query)) (polar,axial)) 0-
    (parameters.length:ℂ)⁻¹*seven.fullField bounded (radius,polar,axial) 2=0 at law
  rw [removePolarMean_coordinate _ (force.fullField_continuous_angles bounded radius closed) (polar,axial)] at law
  have axialDerivative := originalSmoothSeven_scalarAxial bounded pressure xi radius inside polar axial
  change scalarDirectionalField seven bounded 3 (0,0,1) (radius,polar,axial)=
    (radius:ℂ)⁻¹*seven.fullField bounded (radius,polar,axial) 2 at axialDerivative
  change scalarDirectionalField covariant bounded 2 (0,1,0) (radius,polar,axial)=_
  rw [originalKernelSevenCovariant_scalarAngular parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar compact state 2 radius inside polar axial,axialDerivative]
  have cancellation : (radius:ℂ)/(parameters.length:ℂ)*((radius:ℂ)⁻¹*seven.fullField bounded (radius,polar,axial) 2)=
      (parameters.length:ℂ)⁻¹*seven.fullField bounded (radius,polar,axial) 2 := by
    field_simp [Complex.ofReal_ne_zero.mpr (positive.trans inside.1).ne']
  rw [cancellation]
  linear_combination law

end Grad.OriginalKernelHomogeneousGraph
