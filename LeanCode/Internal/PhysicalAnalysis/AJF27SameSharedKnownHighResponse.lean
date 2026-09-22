import AJF26SameSharedKnownHighFlux
import AIU1FullKnownHighResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularHighInverseOrbit Grad.AnnularCurrentInverse Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularReconstruction Grad.CartesianState
open Grad.AnnularOrbitGenerators Grad.AnnularInverseCalculus Grad.ClosedJets Grad.SourceCollarDivision
open Grad.AnnularCurrentSource Grad.AnnularCurrentSolution Grad.AnnularStrongOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelL2
open Grad.AnnularStrongData Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution Grad.AnnularCurrentGreen
open Grad.AnnularCrossMaps Grad.AnnularFullSource

section Pairing
variable {P X E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def realHilbertOperatorPair (first : X →L[ℝ] E) (second : X →L[ℝ] F) : X →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp (first.prod second)

theorem realHilbertOperatorPair_contDiff (first : P → X →L[ℝ] E) (second : P → X →L[ℝ] F)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) :
    ContDiff ℝ ∞ (fun point => realHilbertOperatorPair (first point) (second point)) := by
  have paired := (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := X) (F := E) (G := F) ℝ).contDiff.comp
    (firstSmooth.prodMk secondSmooth)
  have same : (fun point => (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := X) (F := E) (G := F) ℝ) (first point, second point)) =
      (fun point => (first point).prod (second point)) := by
    funext point
    apply ContinuousLinearMap.ext
    intro value
    rfl
  simp only [Function.comp_def] at paired
  rw [same] at paired
  exact realOperatorComposition_contDiff _ _ contDiff_const paired
end Pairing

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

local instance sharedHighRealNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CrossHighSpace lower L positive lengthPositive) :=
  NormedSpace.restrictScalars ℝ ℂ (CrossHighSpace lower L positive lengthPositive)
local instance sharedHighRealModule (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    Module ℝ (CrossHighSpace lower L positive lengthPositive) :=
  (sharedHighRealNormed lower L positive lengthPositive).toModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

def knownHighDatumEnergy (data : ActualHighKnownAmbient parameters lower 0 0) : annularEnergySpace lower L positive :=
  actualHighGraphEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    data.ofLp.1.ofLp.1 data.ofLp.1.ofLp.2 data.ofLp.2.ofLp.1.ofLp data.ofLp.2.ofLp.2.ofLp.1 data.ofLp.2.ofLp.2.ofLp.2

theorem graphDataEnergySolution_highCarrier
    (data : ActualHighKnownCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data) =
    knownHighDatumEnergy parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data.val := rfl

theorem sharedKnownEnergyOrbit_apply (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    sharedKnownEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data =
      energyTranslation lower L positive tau
        (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
            (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
              (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data)))) := by
  have same := strongToHigh_translation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data
  let solution := fun known : ActualHighKnownAmbient parameters lower 0 0 =>
    energyTranslation lower L positive tau
      (knownHighDatumEnergy parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small known)
  have first := knownHighEnergyOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau
    (sharedKnownInput parameters lower positive lowerHalf data)
  have second := congrArg solution same.symm
  have third := congrArg (energyTranslation lower L positive tau)
    (graphDataEnergySolution_highCarrier parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
        (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data)))
  exact first.trans (second.trans third.symm)

/-- The complete high known response is an actual bounded real operator
into the original W × Domega carrier. -/
def sharedKnownHighResponseOrbit (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      CrossHighSpace lower L positive lengthPositive :=
  realHilbertOperatorPair
    (sharedKnownEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    (sharedKnownFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)

theorem sharedKnownHighResponseOrbit_contDiff :
    ContDiff ℝ ∞ (sharedKnownHighResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  realHilbertOperatorPair_contDiff _ _
    (sharedKnownEnergyOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (sharedKnownFluxOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

/-- Both coordinates are those of the SAME full known physical response;
the original shared datum is translated once before its prescribed projections. -/
theorem sharedKnownHighResponseOrbit_apply (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    sharedKnownHighResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data =
      highTranslationEquivalence lower L positive lengthPositive tau
        (fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
            (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
              (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data)))) :=
  congrArg₂ (fun (energy : annularEnergySpace lower L positive)
    (flux : annularOmegaGraph lower L positive lengthPositive) => WithLp.toLp 2 (energy, flux))
    (sharedKnownEnergyOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data)
    (sharedKnownFluxOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data)

end Grad.AnnularHighGenerators
