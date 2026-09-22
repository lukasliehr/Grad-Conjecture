import AKBM20SameActualCorrectedPressure

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



/-- The actual original homogeneous field obeys the corrected scalar
radial law with the literal b3 and V actions. -/
theorem originalHomogeneous_correctedScalar_zero (radius : ℝ) (inside : radius∈Ioo lower 1) (angles : ℝ×ℝ) :
    let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
    let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
    let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar
    scalarDirectionalField pressure bounded 0 (1,0,0) (radius,angles)+pressure.fullField bounded (radius,angles) 0/(radius:ℂ)+
      removePolarMean (fun query => scalarDirectionalField (seven.bThree parameters parameters.length compact lower positive bounded state)
        bounded 0 (0,0,1) (radius,query)) angles/(parameters.length:ℂ)+
      (seven.lowPhysicalCurves parameters parameters.length compact lower positive bounded state 2).fullField bounded (radius,angles) 0/(radius:ℂ)=0 := by
  dsimp only
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  let rawCurve := rawCorrectedPCurves parameters parameters.length compact lower positive bounded state seven
  let raw : C(ℝ×ℝ,ℂ) := ⟨fun query => rawCurve.fullField bounded (radius,query) 0,
    fullScalarField_continuous_angles rawCurve bounded 0 radius closed⟩
  let rawRadial : C(ℝ×ℝ,ℂ) := ⟨fun query => scalarDirectionalField rawCurve bounded 0 (1,0,0) (radius,query),
    scalarDirectionalField_continuous_angles rawCurve bounded 0 (1,0,0) radius inside⟩
  let thirdAxial : C(ℝ×ℝ,ℂ) := ⟨fun query => scalarDirectionalField (seven.bThree parameters parameters.length compact lower positive bounded state)
    bounded 0 (0,0,1) (radius,query),scalarDirectionalField_continuous_angles _ bounded 0 (0,0,1) radius inside⟩
  let retained : C(ℝ×ℝ,ℂ) := ⟨fun query => retainedRVRawField parameters parameters.length compact lower positive bounded state seven radius query 0,
    (PiLp.proj (𝕜:=ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp
      (retainedRVRawField_continuous parameters parameters.length compact lower positive bounded state seven radius closed)⟩
  have zero : polarMeanFreeLinearMap (rawRadial+(radius:ℂ)⁻¹ • raw+(parameters.length:ℂ)⁻¹ • thirdAxial+(radius:ℂ)⁻¹ • retained)=0 := by
    apply ContinuousMap.ext
    intro query
    have actual := originalHomogeneous_projectedRawScalar_zero parameters compact nonzero state small insideSeed lower positive bounded
      physicalState sameBase sameEpsilon vector scalar constrained homogeneous radius inside query
    change removePolarMean (fun query =>
      scalarDirectionalField rawCurve bounded 0 (1,0,0) (radius,query)+
      (radius:ℂ)⁻¹*rawCurve.fullField bounded (radius,query) 0+
      (parameters.length:ℂ)⁻¹*scalarDirectionalField (seven.bThree parameters parameters.length compact lower positive bounded state)
        bounded 0 (0,0,1) (radius,query)+
      (radius:ℂ)⁻¹*retainedRVRawField parameters parameters.length compact lower positive bounded state seven radius query 0) query=0
    simpa only [div_eq_mul_inv,mul_comm] using actual
  rw [map_add,map_add,map_add,map_smul,map_smul,map_smul] at zero
  have coordinate := congrArg (fun field : C(ℝ×ℝ,ℂ) => field angles) zero
  change removePolarMean (fun query => scalarDirectionalField rawCurve bounded 0 (1,0,0) (radius,query)) angles+
    (radius:ℂ)⁻¹ * removePolarMean (fun query => rawCurve.fullField bounded (radius,query) 0) angles+
    (parameters.length:ℂ)⁻¹ * removePolarMean (fun query => scalarDirectionalField (seven.bThree parameters parameters.length compact lower positive bounded state)
      bounded 0 (0,0,1) (radius,query)) angles+
    (radius:ℂ)⁻¹ * removePolarMean (fun query => retainedRVRawField parameters parameters.length compact lower positive bounded state seven radius query 0) angles=0 at coordinate
  rw [← correctedP_radial_projected parameters parameters.length compact lower positive bounded state seven radius inside angles.1 angles.2,
    ← correctedP_projection_same parameters parameters.length compact lower positive bounded state seven radius closed angles,
    ← sameRV_scalar parameters parameters.length compact lower positive bounded state seven radius closed angles,
    originalHomogeneous_correctedP_radialSame parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous radius inside angles.1 angles.2,
    originalHomogeneous_correctedP_same parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous ⟨radius,closed⟩ angles] at coordinate
  simpa only [div_eq_mul_inv,mul_comm] using coordinate

end Grad.OriginalKernelHomogeneousGraph
