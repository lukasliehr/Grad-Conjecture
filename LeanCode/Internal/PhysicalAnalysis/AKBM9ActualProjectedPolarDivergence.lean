import AKBM8ActualOriginalPolarDivergence

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

/-- The original core angular projection is the literal circle projection. -/
theorem originalCoreCircle_meanFree (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (field : ACore parameters 1) (radius : Icc lower (1:ℝ)) (angles : ℝ×ℝ) :
    removePolarMean (fun query => coreValue field
      (polarClosedPoint radius.val query.1 (positive.le.trans radius.property.1) radius.property.2) query.2) angles=
    coreValue (removeAngularCore parameters field)
      (polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2) angles.2 := by
  let curves := originalCoreLowCurves parameters lower positive bounded field
  let projected := originalCoreLowCurves parameters lower positive bounded (removeAngularCore parameters field)
  have negative : originalCurveNegativeTrace projected radius=originalCurveNegativeTrace curves.meanFree radius := by
    rw [originalCurveNegativeTrace_meanFree]
    exact originalCoreNegativeTrace_meanFree parameters lower positive bounded field radius
  have full := originalCurveFullField_eq_of_negative projected curves.meanFree bounded radius negative angles
  have original : (fun query => curves.fullField bounded (radius.val,query))=
      (fun query => coreValue field (polarClosedPoint radius.val query.1 (positive.le.trans radius.property.1) radius.property.2) query.2) :=
    funext (originalCoreLowCurves_fullField parameters lower positive bounded field radius.val radius.property)
  calc
    _ = removePolarMean (fun query => curves.fullField bounded (radius.val,query)) angles :=
      congrArg (fun function => removePolarMean function angles) original.symm
    _ = curves.meanFree.fullField bounded (radius.val,angles) := (curves.fullField_meanFree bounded radius.val radius.property angles).symm
    _ = projected.fullField bounded (radius.val,angles) := full.symm
    _ = _ := originalCoreLowCurves_fullField parameters lower positive bounded _ radius.val radius.property angles

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




/-- The actual original homogeneous determinant annihilates the complete
reconstructed polar cofactor divergence, with the original outer P. -/
theorem originalHomogeneous_projectedPolarDivergence_zero (radius : ℝ) (inside : radius∈Ioo lower 1) (angles : ℝ×ℝ) :
    removePolarMean (fun query => originalPolarDivergence parameters parameters.length compact lower positive bounded state
      (originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive bounded physicalState.2.1 vector scalar) radius query) angles=0 := by
  let divergence := fun query => originalPolarDivergence parameters parameters.length compact lower positive bounded state
    (originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar) radius query
  let core := originalCartesianDivergenceCore parameters.length (originalCartesianCofactorFluxCore parameters.length physicalState vector)
  let r : Icc lower (1:ℝ) := ⟨radius,⟨inside.1.le,inside.2.le⟩⟩
  have literal : (fun query => (parameters.length:ℂ) • divergence query)=
      (fun query => coreValue core (polarClosedPoint radius query.1 (positive.le.trans inside.1.le) inside.2.le) query.2 0) := by
    funext query
    exact originalHomogeneous_sevenPolarDivergence parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous radius inside query.1 query.2
  have projected := congrArg (fun field : ℝ×ℝ→ℂ => removePolarMean field angles) literal
  rw [congrFun (removePolarMean_smul (parameters.length:ℂ) divergence) angles] at projected
  have coreProjection := originalCoreCircle_meanFree parameters lower positive bounded core r angles
  have coordinate := congrArg (fun value : ComplexEuclidean 1 => value 0) coreProjection
  change (removePolarMean (originalCoreCircle parameters core (tupleRadius lower positive r)) angles) 0=_ at coordinate
  rw [removePolarMean_coordinate _
    (originalCoreCircle_continuous parameters core (tupleRadius lower positive r)) angles] at coordinate
  have zero := originalHomogeneous_cartesianCofactorDivergence parameters parameters.length nonzero physicalState vector scalar homogeneous
  change removeAngularCore parameters core=0 at zero
  rw [zero] at coordinate
  simp only [show coreValue (0 : ACore parameters 1) (polarClosedPoint r.val angles.1 (positive.le.trans r.property.1) r.property.2) angles.2=0 from by simp [coreValue],PiLp.zero_apply] at coordinate
  change removePolarMean (fun query => coreValue core
    (polarClosedPoint radius query.1 (positive.le.trans inside.1.le) inside.2.le) query.2 0) angles=0 at coordinate
  rw [coordinate] at projected
  exact (smul_eq_zero.mp projected).resolve_left (Complex.ofReal_ne_zero.mpr nonzero)

end Grad.OriginalKernelHomogeneousGraph
