import AKBM16ActualOriginalXiRadialLaw

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



/-- Genuine first angular row of the original homogeneous covariant,
using its proved radial Xi law and retaining the inner force projection. -/
theorem originalHomogeneous_firstAngularRow (radius : ℝ) (inside : radius∈Ioo lower 1) (polar axial : ℝ) :
    let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar
    let covariant := seven.covariant parameters parameters.length compact lower positive bounded state.val
    scalarDirectionalField covariant bounded 0 (0,1,0) (radius,polar,axial)=
      seven.fullField bounded (radius,polar,axial) 3+(radius:ℂ)*scalarDirectionalField seven bounded 3 (1,0,0) (radius,polar,axial)+
      removePolarMean (fun angles => (covariant.retainedForce parameters parameters.length compact lower positive bounded state).fullField bounded (radius,angles) 0) (polar,axial) := by
  dsimp only
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let covariant := seven.covariant parameters parameters.length compact lower positive bounded state.val
  let retained := covariant.retainedForce parameters parameters.length compact lower positive bounded state
  let j := seven.lowPhysicalCurves parameters parameters.length compact lower positive bounded state 0
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  have radial := originalHomogeneous_xiRadial parameters compact nonzero state small insideSeed lower positive bounded physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous radius closed (polar,axial)
  have scalarLaw := ((PiLp.proj (𝕜:=ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius
    (radial.hasDerivAt (Icc_mem_nhds inside.1 inside.2))
  have equality := (scalarRadial_hasDerivAt xi bounded 0 radius inside polar axial).unique scalarLaw
  change scalarDirectionalField xi bounded 0 (1,0,0) (radius,polar,axial)=j.meanFree.fullField bounded (radius,polar,axial) 0 at equality
  rw [originalSmoothSeven_scalarRadial bounded pressure xi radius inside polar axial,
    j.fullField_meanFree bounded radius closed (polar,axial),
    removePolarMean_coordinate _ (j.fullField_continuous_angles bounded radius closed) (polar,axial)] at equality
  have scalarSum (angles : ℝ×ℝ) : j.fullField bounded (radius,angles) 0=
      scalarDirectionalField covariant bounded 0 (0,1,0) (radius,angles)-retained.fullField bounded (radius,angles) 0 := by
    rw [sameFirstPhysicalRow_pointwise parameters parameters.length compact lower positive bounded state seven radius closed angles]
    change ((seven.rotatedCovariant parameters parameters.length compact lower positive bounded state.val).bulkUnit (0:Fin 1) 0).fullField bounded (radius,angles) 0-
      retained.fullField bounded (radius,angles) 0=_
    rw [fullField_bulkUnit_zero_scalar _ bounded 0 radius closed angles,
      originalKernelSevenCovariant_scalarAngular parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive bounded physicalState.2.1 vector scalar compact state 0 radius inside angles.1 angles.2]
  simp_rw [scalarSum] at equality
  have retainedContinuous : Continuous (fun angles => retained.fullField bounded (radius,angles) 0) :=
    (PiLp.proj (𝕜:=ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp (retained.fullField_continuous_angles bounded radius closed)
  rw [congrFun (removePolarMean_sub (fun angles => scalarDirectionalField covariant bounded 0 (0,1,0) (radius,angles))
    (fun angles => retained.fullField bounded (radius,angles) 0)
    (scalarDirectionalField_continuous_angles covariant bounded 0 (0,1,0) radius inside) retainedContinuous) (polar,axial),
    sameScalarAngular_meanFree covariant bounded 0 radius inside (polar,axial)] at equality
  exact sub_eq_iff_eq_add.mp equality.symm

end Grad.OriginalKernelHomogeneousGraph
