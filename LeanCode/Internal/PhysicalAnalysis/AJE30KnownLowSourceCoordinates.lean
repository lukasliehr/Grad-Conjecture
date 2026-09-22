import AJE12RealKnownOperatorCalculus
import AIR8ExactKnownLowResponseConsumer
import AJE7CompleteSharedDataUnitary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularReconstruction
open Grad.AnnularHighInverseOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2
open Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularLowOrbit

private def knownLowBulkProjection (lower : ℝ) : KnownLowData lower →L[ℝ] KnownLowBulkData lower :=
  (ContinuousLinearMap.fst ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

def knownLowWeightedProjection (lower : ℝ) : KnownLowData lower →L[ℝ] HighKnownSourceBulk lower :=
  ((ContinuousLinearMap.fst ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap).comp
    (knownLowBulkProjection lower)

def knownLowGProjection (lower : ℝ) : KnownLowData lower →L[ℝ] DivisionRow 1 lower :=
  ((ContinuousLinearMap.snd ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap).comp
    (knownLowBulkProjection lower)

def knownLowIncomingProjection (lower : ℝ) : KnownLowData lower →L[ℝ] LowEnergyBoundary :=
  (ContinuousLinearMap.snd ℝ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

/-- Genuine translation of AIR's original independent known datum. -/
def knownLowInputTranslation (lower : ℝ) (tau : OrbitParameter) : KnownLowData lower ≃ₗᵢ[ℝ] KnownLowData lower :=
  realHilbertProductEquivalence
    (realHilbertProductEquivalence
      (finiteRealHilbertEquivalence 4 (realCharacterEquivalence (orbitLpEquivalence (RadialL2 1 lower) tau)))
      (realCharacterEquivalence (orbitLpEquivalence (RadialL2 1 lower) tau)))
    (realCharacterEquivalence (lowBoundaryTranslationEquivalence tau))

theorem knownLowInputTranslation_exact (lower : ℝ) (tau : OrbitParameter) (data : KnownLowData lower) :
    knownLowInputTranslation lower tau data =
      WithLp.toLp 2
        (WithLp.toLp 2 (WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (data.ofLp.1.ofLp.1 slot)),
          orbitLpAction (RadialL2 1 lower) tau data.ofLp.1.ofLp.2),
        lowBoundaryTranslation tau data.ofLp.2) := rfl

/-- Complete shared-data restriction commutes with AIR's genuine datum
translation, including its independent incoming coordinate. -/
theorem strongToLow_translation (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (angular cell : ℕ) (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    strongToLow parameters lower positive bounded angular cell
      (strongDataTranslation parameters lower positive bounded angular cell tau data) =
      knownLowInputTranslation lower tau (strongToLow parameters lower positive bounded angular cell data) := rfl

def knownLowSourceInput (lower : ℝ) : KnownLowData lower →L[ℝ] DivisionRow 7 lower :=
  ((knownLowSevenPacket lower).restrictScalars ℝ).comp (knownLowWeightedProjection lower)

/-- Original direct forcing +f and +Rg, with the unchanged original
normalizations in lowFirstOutput and lowAngularOutput. -/
def knownLowDirectInput (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) :
    KnownLowData lower →L[ℝ] LowEnergyBulk lower :=
  ((lowFirstOutput parameters lower length).restrictScalars ℝ).comp
      (((highSourceF lower).restrictScalars ℝ).comp (knownLowWeightedProjection lower)) -
    ((lowAngularOutput lower length positive).restrictScalars ℝ).comp
      (((radialRadiusRow lower positive).restrictScalars ℝ).comp (knownLowGProjection lower))

/-- Insert an actual forcing row as bulk and zero independent incoming. -/
def knownLowBulkIntoData (lower : ℝ) : LowEnergyBulk lower →L[ℝ] LowEnergyData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ (LowEnergyBulk lower)).prod (0 : LowEnergyBulk lower →L[ℝ] LowEnergyBoundary))

/-- Fixed complete datum contribution, with original direct forcing and
the original incoming datum retained once. -/
def knownLowDirectData (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) :
    KnownLowData lower →L[ℝ] LowEnergyData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((knownLowDirectInput parameters lower length positive).prod (knownLowIncomingProjection lower))

end Grad.AnnularStrongOrbit
