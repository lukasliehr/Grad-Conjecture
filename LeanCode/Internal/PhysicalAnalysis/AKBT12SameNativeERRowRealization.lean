import AKBT11ActualNativeMatrixRepresentatives
import AKBP32OriginalB10NativeStartup

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.Constraints Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

 def StartupMoments.scalarMeanFree (family : StartupMoments 1) : StartupMoments 1 :=
  family.map originalScalarMeanFreeKernel ((StartupCellwise.id 1).sub (startupAngularKernel_cellwise _ _ _))

/-- The eight genuine ER fields obtained from the SAME completed native
covariant, full force matrix output and signed cofactor output. -/
 def nativeERRows (covariant force cofactor : StartupMoments 3)
    (knownForce : StartupMoments 2) (knownThird determinant : StartupMoments 1) : StartupNativeERRows where
  covariant := covariant
  knownForce := knownForce.qrad
  forceCorrection := ((force.value planarPartMap).qrad).smul 2
  knownThird := knownThird
  thirdCorrection := ((force.value toroidalPartMap).scalarMeanFree).smul 2
  determinant := determinant
  planarFlux := ((cofactor.add covariant).value planarPartMap).sub (((cofactor.add covariant).value planarPartMap).average)
  scalarFlux := ((cofactor.add covariant).value toroidalPartMap).scalarMeanFree

/-- Exact actual coefficient actions, together with the proven native
Qa recovery, discharge all three BP startup operator identities. -/
 theorem nativeERRows_actualOperators {L sigma gamma ell : ℝ}
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
    startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent rows.circle.field=rows.currentFlux.field := by
  constructor
  · change (2:ℂ) • startupGenuineQradKernel (originalMatrixKernel admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1
      (originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent (originalCircleKernel covariant.field))) = _
    rw [recovered,planar]
    rfl
  constructor
  · change (2:ℂ) • originalScalarMeanFreeKernel (originalMatrixKernel admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2
      (originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent (originalCircleKernel covariant.field))) = _
    rw [recovered,third]
    rfl
  · change originalPlanarMeanFreeKernel (originalValueKernel planarPartMap
      (originalMatrixKernel admissible data.fluxDeviation coherent.2.2.2.2.1
        (originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent (originalCircleKernel covariant.field)))) -
      (1/2:ℂ) • originalValueKernel quarterValueMap (originalAverageKernel
        (startupGenuineForceKernel admissible data coherent inverseCoherent (originalCircleKernel covariant.field))) = _
    rw [recovered,flux]
    change _ - (1/2:ℂ) • originalValueKernel quarterValueMap (originalAverageKernel
      ((2:ℂ) • startupGenuineQradKernel (originalMatrixKernel admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1
        (originalCurrentKernel admissible data.gaugeDeviation coherent.2.2.2.1 inverseCoherent (originalCircleKernel covariant.field))))) = _
    rw [recovered,planar]
    rfl

end Grad.CartesianStartup
