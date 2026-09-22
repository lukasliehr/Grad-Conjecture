import AKEG3PhysicalUnitWeightedActions
import AKBT12SameNativeERRowRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.Constraints Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- Exact actual coefficient actions, together with the proven native
Qa recovery, discharge all three BP startup operator identities. -/
 theorem nativeERRows_actualFourOperators {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (covariant force cofactor : StartupMoments 3)
    (knownForce : StartupMoments 2) (knownThird determinant : StartupMoments 1)
    (recovered : originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent
      (originalCircleKernel covariant.field)=covariant.field)
    (planar : originalMatrixKernel admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1 covariant.field=
      originalValueKernel planarPartMap force.field)
    (third : originalMatrixKernel admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2 covariant.field=
      originalValueKernel toroidalPartMap force.field)
    (flux : originalMatrixKernel admissible data.fluxDeviation coherent.2.2.2.2.1 covariant.field=cofactor.field+covariant.field) :
    let rows := nativeERRows covariant force cofactor knownForce knownThird determinant
    startupGenuineForceKernel admissible data coherent inverseCoherent rows.circle.field=rows.forceCorrection.field ∧
    originalThirdCorrectionKernel admissible data coherent inverseCoherent rows.circle.field=rows.thirdCorrection.field ∧
    startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent rows.circle.field=rows.currentFlux.field ∧
    originalScalarFluxKernel admissible data coherent inverseCoherent rows.circle.field=rows.scalarFlux.field := by
  have first := nativeERRows_actualOperators admissible data coherent inverseCoherent
    covariant force cofactor knownForce knownThird determinant recovered planar third flux
  refine ⟨first.1,first.2.1,first.2.2,?_⟩
  change originalScalarMeanFreeKernel (originalValueKernel toroidalPartMap
    (originalMatrixKernel admissible data.fluxDeviation coherent.2.2.2.2.1
      (originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent
        (originalCircleKernel covariant.field)))) = _
  rw [recovered,flux]
  rfl

end Grad.CartesianStartup

namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Set Filter MeasureTheory
open Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ActualCurrentPrimitives Grad.ActualScaledNativeCoefficients Grad.Constraints.Gauges

/-- Propositional parameter transport before inserting the actual native representatives. -/
theorem weighted_native_actions {parameters : PhaseParameters} {length radius : ℝ}
    (radiusNonnegative : 0 ≤ radius) (state : OriginalUnitRankState parameters length radius)
    (physicalEpsilon : ℝ) (physicalField : ACore parameters 3)
    (epsilonSame : state.epsilon=physicalEpsilon) (fieldSame : state.field=physicalField)
    {covariant force cofactor : StartupL2 3} {raw : ℝ × Spatial → PhysicalValue 3}
    (covariantSame : StartupWeightedRep parameters.sigma0 parameters.gamma 1 covariant raw)
    (regular : StartupOrbitContinuous raw)
    (forceSame : StartupWeightedRep parameters.sigma0 parameters.gamma 1 force
      (nativeScaledMatrixRaw 1 (forceMatrixFamily parameters length physicalEpsilon physicalField) raw))
    (cofactorSame : StartupWeightedRep parameters.sigma0 parameters.gamma 1 cofactor
      (nativeScaledMatrixRaw 1 (originalCofactorFamily parameters length physicalEpsilon physicalField) raw))
    (forceContinuous : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle =>
      nativeScaledMatrixRaw 1 (forceMatrixFamily parameters length physicalEpsilon physicalField) raw (angle,point)))
    (cofactorContinuous : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle =>
      nativeScaledMatrixRaw 1 (originalCofactorFamily parameters length physicalEpsilon physicalField) raw (angle,point))) :
    (originalMatrixKernel (unitDiskAdmissible parameters) state.data.rotatedPlanarProduct
      (state.coherent radiusNonnegative).2.2.2.2.2.2.2.1 covariant=originalValueKernel planarPartMap force ∧
    originalMatrixKernel (unitDiskAdmissible parameters) state.data.rotatedThirdProduct
      (state.coherent radiusNonnegative).2.2.2.2.2.2.2.2 covariant=originalValueKernel toroidalPartMap force) ∧
    originalMatrixKernel (unitDiskAdmissible parameters) state.data.fluxDeviation
      (state.coherent radiusNonnegative).2.2.2.2.1 covariant=cofactor+covariant := by
  subst physicalEpsilon
  subst physicalField
  exact ⟨weighted_force_actions radiusNonnegative state covariantSame regular forceSame forceContinuous,
    weighted_flux_action radiusNonnegative state covariantSame regular cofactorSame cofactorContinuous⟩

end Grad.OriginalCoreRealization.OriginalUnitRankState
