import AKBM4SameOriginalFullFlux
import AKBM5OriginalCartesianCurveDivergence
import AKBM7OriginalDeterminantProductExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ActualCartesianDescent Grad.ActualCartesianEquations Grad.PhysicalFamily Grad.BoundaryTrace
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



/-- The SAME reconstructed polar divergence is the actual original core
Piola divergence divided by L, at every point of the open collar. -/
theorem originalHomogeneous_sevenPolarDivergence (radius : ℝ) (inside : radius∈Ioo lower 1) (polar axial : ℝ) :
    (parameters.length:ℂ)*originalPolarDivergence parameters parameters.length compact lower positive bounded state
      (originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive bounded physicalState.2.1 vector scalar) radius (polar,axial)=
    coreValue (originalCartesianDivergenceCore parameters.length (originalCartesianCofactorFluxCore parameters.length physicalState vector))
      (polarClosedPoint radius polar (positive.le.trans inside.1.le) inside.2.le) axial 0 := by
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let flux := samePolarCofactorVector parameters parameters.length compact lower positive bounded state seven
  let core := originalCartesianCofactorFluxCore parameters.length physicalState vector
  have same (r : Icc lower (1:ℝ)) (angles : ℝ×ℝ) : flux.cartesianCovariant.fullField bounded (r.val,angles)=
      coreValue core (polarClosedPoint r.val angles.1 (positive.le.trans r.property.1) r.property.2) angles.2 :=
    originalHomogeneous_sevenCartesianFlux parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous r angles
  have normInside : ‖polarPlane (radius,polar)‖∈Ioo lower 1 := by
    simpa only [polarPlane_norm,abs_of_pos (positive.trans inside.1)] using inside
  have actual := originalSmoothCurve_cartesianDivergence flux.cartesianCovariant bounded core same parameters.length
    (polarPlane (radius,polar),axial) normInside
  rw [sameCartesianRotation_divergence flux bounded parameters.length nonzero radius inside polar axial] at actual
  change (parameters.length:ℂ)*(_+_+_+_)=_ at actual
  simp only [flux,samePolarCofactorVector_directional parameters parameters.length compact lower positive bounded state seven _ _ radius inside (polar,axial),
    samePolarCofactorVector_component parameters parameters.length compact lower positive bounded state seven _ radius ⟨inside.1.le,inside.2.le⟩ (polar,axial)] at actual
  exact actual

end Grad.OriginalKernelHomogeneousGraph
