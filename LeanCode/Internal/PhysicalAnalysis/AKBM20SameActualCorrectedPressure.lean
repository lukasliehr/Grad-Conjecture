import AKBM19ActualOriginalScalarCancellation

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



/-- The computed corrected p is the SAME original pressure stored in the
tuple, including its outer angular projection. -/
theorem originalHomogeneous_correctedP_same (radius : Icc lower (1:ℝ)) (angles : ℝ×ℝ) :
    let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
    let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
    let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar
    (seven.correctedP parameters parameters.length compact lower positive bounded state).fullField bounded (radius.val,angles)=
      pressure.fullField bounded (radius.val,angles) := by
  dsimp only
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  rw [fullField_originalCorrectedP parameters parameters.length compact lower positive bounded state seven radius.val radius.property angles,
    SmoothLowPhysicalRow.fullField_meanFree _ bounded radius.val radius.property angles]
  congr 1
  funext query
  rw [originalHomogeneous_sevenCovariantFullField parameters compact nonzero state small insideSeed lower positive bounded physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous radius query]
  have slot : matrixUnit (0:Fin 1) (3:Fin 7) (seven.fullField bounded (radius.val,query))=
      (radius.val:ℂ)⁻¹ • xi.fullField bounded (radius.val,query) := by
    change matrixUnit (0:Fin 1) (3:Fin 7) ((originalSmoothSevenCurves pressure xi bounded).fullField bounded (radius.val,query))=_
    rw [originalSmoothSevenCurves_fullField bounded pressure xi radius.val radius.property query]
    apply PiLp.ext
    intro component
    fin_cases component
    simp [matrixUnit_apply,operatorBasis]
  rw [slot,originalSignedCofactorRow_symmetric parameters parameters.length compact state 1 0 query,
    originalSignedFlux_sameRaw parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded vector radius (fun query => xi.fullField bounded (radius.val,query)) query,
    originalRawFluxCurves_fullField parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small lower positive bounded
      (originalVectorLowCurves parameters lower positive bounded vector) xi radius.val radius.property query]
  have sameVector : (fun query => (originalVectorLowCurves parameters lower positive bounded vector).fullField bounded (radius.val,query))=
      originalCoreCircle parameters vector (tupleRadius lower positive radius) :=
    funext (originalVectorLowCurves_fullField parameters lower positive bounded vector radius.val radius.property)
  rw [sameVector]
  rfl

/-- The same full pressure equality determines its genuine radial derivative. -/
theorem originalHomogeneous_correctedP_radialSame (radius : ℝ) (inside : radius∈Ioo lower 1) (polar axial : ℝ) :
    let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
    let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
    let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar
    scalarDirectionalField (seven.correctedP parameters parameters.length compact lower positive bounded state) bounded 0 (1,0,0) (radius,polar,axial)=
      scalarDirectionalField pressure bounded 0 (1,0,0) (radius,polar,axial) := by
  dsimp only
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  have same : (fun location => (seven.correctedP parameters parameters.length compact lower positive bounded state).fullField bounded (location,polar,axial) 0)=ᶠ[𝓝 radius]
      (fun location => pressure.fullField bounded (location,polar,axial) 0) := by
    filter_upwards [Ioo_mem_nhds inside.1 inside.2] with location member
    exact congrArg (fun value : ComplexEuclidean 1 => value 0)
      (originalHomogeneous_correctedP_same parameters compact nonzero state small insideSeed lower positive bounded physicalState sameBase sameEpsilon
        vector scalar constrained homogeneous ⟨location,⟨member.1.le,member.2.le⟩⟩ (polar,axial))
  exact (scalarRadial_hasDerivAt _ bounded 0 radius inside polar axial).unique
    ((scalarRadial_hasDerivAt pressure bounded 0 radius inside polar axial).congr_of_eventuallyEq same)

end Grad.OriginalKernelHomogeneousGraph
