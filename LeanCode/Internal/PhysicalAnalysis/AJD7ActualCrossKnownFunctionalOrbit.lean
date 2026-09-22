import AJD6ActualCrossKnownBulkOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularHighInverseOrbit Grad.AnnularCurrentBoundary

section Pairing
variable {X D V P : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
local instance pairingRealInner : InnerProductSpace ℝ D := InnerProductSpace.rclikeToReal ℂ D

def realTestPairing (test : V →L[ℝ] D) : D →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ D) test

def pairedComplexOperator (test : V →L[ℝ] D) : (X →L[ℂ] D) →L[ℝ] (X →L[ℝ] V →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ X D (V →L[ℝ] ℝ)) (realTestPairing test)).comp
    (ContinuousLinearMap.restrictScalarsIsometry ℂ X D ℝ ℝ).toContinuousLinearMap

theorem pairedComplexOperator_apply (test : V →L[ℝ] D) (mapping : X →L[ℂ] D) (source : X) (field : V) :
    pairedComplexOperator test mapping source field = (inner ℂ (test field) (mapping source)).re :=
  inner_re_symm (𝕜 := ℂ) _ _

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem pairedComplexOperator_contDiff (test : V →L[ℝ] D) (family : P → X →L[ℂ] D)
    (smooth : ContDiff ℝ ∞ family) : ContDiff ℝ ∞ (fun point => pairedComplexOperator test (family point)) := by
  have composed := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := X →L[ℂ] D) (F := X →L[ℝ] V →L[ℝ] ℝ)
    (pairedComplexOperator (X := X) (D := D) (V := V) test)).comp smooth
  simpa only [Function.comp_def] using composed
end Pairing

private theorem complexOperator_precompose_contDiff {P X D F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup D] [NormedSpace ℂ D] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (family : P → D →L[ℂ] F) (input : X →L[ℂ] D) (smooth : ContDiff ℝ ∞ family) :
    ContDiff ℝ ∞ (fun point => (family point).comp input) :=
  (((ContinuousLinearMap.compL ℂ X D F).flip input).restrictScalars ℝ).contDiff.comp smooth

private theorem difference_contDiff {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (first second : P → E)
    (hf : ContDiff ℝ ∞ first) (hg : ContDiff ℝ ∞ second) :
    ContDiff ℝ ∞ (fun point => first point - second point) := hf.sub hg

local instance crossDataNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedAddCommGroup (CrossHighData parameters lower) := inferInstance
local instance crossDataSeminormed (parameters : PhaseParameters) (lower : ℝ) :
    SeminormedAddCommGroup (CrossHighData parameters lower) :=
  (crossDataNormed parameters lower).toSeminormedAddCommGroup
local instance crossDataRealInner (parameters : PhaseParameters) (lower : ℝ) :
    InnerProductSpace ℝ (CrossHighData parameters lower) :=
  InnerProductSpace.rclikeToReal ℂ (CrossHighData parameters lower)
local instance crossDataRealNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedSpace ℝ (CrossHighData parameters lower) :=
  (crossDataRealInner parameters lower).toNormedSpace
local instance crossDataRealModule (parameters : PhaseParameters) (lower : ℝ) :
    Module ℝ (CrossHighData parameters lower) := (crossDataRealNormed parameters lower).toModule

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)

def crossBoundaryValueOrbit (tau : OrbitParameter) :
    CrossHighData parameters lower →L[ℂ] NegativeTrace parameters 0 0 1 :=
  (actualBoundaryInverseOrbitJet parameters L compact state 0 0 tau).comp (crossBoundaryCoordinate parameters lower)

theorem crossBoundaryValueOrbit_contDiff :
    ContDiff ℝ ∞ (crossBoundaryValueOrbit parameters L compact lower state) :=
  complexOperator_precompose_contDiff _ _ (actualBoundaryInverseOrbitJet_contDiff parameters L compact state 0 0)

/-- The actual known real functional, as a bounded operator of the original cross datum. -/
def crossKnownFunctionalOrbit (tau : OrbitParameter) :
    CrossHighData parameters lower →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ :=
  pairedComplexOperator
      ((highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ)
      (crossKnownBulkOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state tau) -
    pairedComplexOperator
      ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0).restrictScalars ℝ)
      (crossBoundaryValueOrbit parameters L compact lower state tau)

theorem crossKnownFunctionalOrbit_contDiff :
    ContDiff ℝ ∞ (crossKnownFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) := by
  exact difference_contDiff _ _
    (pairedComplexOperator_contDiff _ _ (crossKnownBulkOrbit_contDiff parameters L compact lower positive (lowerHalf.trans (by norm_num)) state))
    (pairedComplexOperator_contDiff _ _ (crossBoundaryValueOrbit_contDiff parameters L compact lower state))

theorem crossKnownFunctionalOrbit_literal (tau : OrbitParameter) (datum : CrossHighData parameters lower)
    (test : annularEnergySpace lower L positive) :
    crossKnownFunctionalOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau datum test =
      (inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
        (crossKnownBulkOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state tau datum) -
       inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test)
        (crossBoundaryValueOrbit parameters L compact lower state tau datum)).re := by
  exact congrArg₂ (fun first second : ℝ => first - second)
    (pairedComplexOperator_apply (X := CrossHighData parameters lower) (D := DivisionRow 3 lower)
      ((highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ)
      (crossKnownBulkOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) state tau) datum test)
    (pairedComplexOperator_apply (X := CrossHighData parameters lower) (D := NegativeTrace parameters 0 0 1)
      ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0).restrictScalars ℝ)
      (crossBoundaryValueOrbit parameters L compact lower state tau) datum test)

end Grad.AnnularCrossOrbit
