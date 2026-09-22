import AJE15OriginalKnownBulkCovariance
import AJE14CompleteKnownCoefficientTower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2 Grad.AnnularCurrentEnergy Grad.AnnularCurrentBoundary

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)

/-- The complete AEK12 real known functional jet on the original full high
ambient, with genuine source graphs and actual beta/source lift terms. -/
def knownFunctionalOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :
    ActualHighKnownAmbient parameters lower 0 0 →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ :=
  pairedRealOperator ((highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ)
      (knownBulkOrbitJet parameters L compact lower positive lowerHalf state angular cell tau) -
    pairedRealOperator ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0).restrictScalars ℝ)
      (knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state angular cell tau)

theorem knownFunctionalOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (knownFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell)
      (orbitColumns (knownFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state (angular + 1) cell tau)
        (knownFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular (cell + 1) tau)) tau := by
  exact differenceOrbit_hasFDerivAt _ _ _ _ _ _ tau
    (pairedRealOperator_hasFDerivAt
      ((highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ) _ _ _ tau
      (knownBulkOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf state angular cell tau))
    (pairedRealOperator_hasFDerivAt
      ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0).restrictScalars ℝ) _ _ _ tau
      (knownBoundaryOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf state angular cell tau))

theorem knownFunctionalOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (knownFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell) :=
  orbitTower_contDiff _
    (knownFunctionalOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) angular cell

theorem knownFunctionalOrbitJet_literal (angular cell : ℕ) (tau : OrbitParameter)
    (data : ActualHighKnownAmbient parameters lower 0 0) (test : annularEnergySpace lower L positive) :
    knownFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau data test =
      (inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
        (knownBulkOrbitJet parameters L compact lower positive lowerHalf state angular cell tau data) -
       inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test)
        (knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state angular cell tau data)).re := by
  change pairedRealOperator
      ((highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ)
      (knownBulkOrbitJet parameters L compact lower positive lowerHalf state angular cell tau) data test -
    pairedRealOperator
      ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0).restrictScalars ℝ)
      (knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state angular cell tau) data test = _
  exact congrArg₂ (fun first second : ℝ => first - second)
    (pairedRealOperator_apply
      ((highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ)
      (knownBulkOrbitJet parameters L compact lower positive lowerHalf state angular cell tau) data test)
    (pairedRealOperator_apply
      ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0).restrictScalars ℝ)
      (knownBoundaryOrbitJet parameters L compact lower positive lowerHalf state angular cell tau) data test)

end Grad.AnnularStrongOrbit
