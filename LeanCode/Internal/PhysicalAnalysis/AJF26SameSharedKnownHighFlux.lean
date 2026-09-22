import AJF24RealClosedGraphOperatorLift
import AJF25SameKnownPhysicalOutputOrbit
import AJE19SharedHighProjectionCovariance
import AJE34KnownLowBaseAndSharedBounds
import AJD12OriginalOmegaCoordinateCovariance

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

attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- Fixed projection of the once-prescribed strong datum to its actual high ambient. -/
abbrev sharedKnownInput :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      ActualHighKnownAmbient parameters lower 0 0 :=
  (ActualHighKnownCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0).subtypeL.comp
    (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)

/-- Literal original known energy response to the SAME shared strong datum. -/
def sharedKnownEnergyOrbit (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      annularEnergySpace lower L positive :=
  (knownHighEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).comp
    (sharedKnownInput parameters lower positive lowerHalf)

theorem sharedKnownEnergyOrbit_contDiff :
    ContDiff ℝ ∞ (sharedKnownEnergyOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  realOperatorComposition_contDiff _ _
    (knownHighEnergyOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) contDiff_const

def sharedKnownPhysicalOutputOrbit (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ] DivisionRow 3 lower :=
  (knownPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).comp
    (sharedKnownInput parameters lower positive lowerHalf)

theorem sharedKnownPhysicalOutputOrbit_contDiff :
    ContDiff ℝ ∞ (sharedKnownPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  realOperatorComposition_contDiff _ _
    (knownPhysicalOutputOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) contDiff_const

def knownHighDatumPhysicalOutput (data : ActualHighKnownAmbient parameters lower 0 0) : DivisionRow 3 lower :=
  actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (actualHighGraphEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      data.ofLp.1.ofLp.1 data.ofLp.1.ofLp.2 data.ofLp.2.ofLp.1.ofLp
      data.ofLp.2.ofLp.2.ofLp.1 data.ofLp.2.ofLp.2.ofLp.2)
    data.ofLp.1.ofLp.1 data.ofLp.1.ofLp.2

theorem graphDataPhysicalOutput_highCarrier
    (data : ActualHighKnownCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data) =
    knownHighDatumPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data.val := rfl

theorem sharedKnownPhysicalOutputOrbit_apply (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    sharedKnownPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data =
      orbitLpAction (RadialL2 3 lower) tau
        (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
            (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
              (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data)))) := by
  have same := strongToHigh_translation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data
  let packet := fun known : ActualHighKnownAmbient parameters lower 0 0 =>
    orbitLpAction (RadialL2 3 lower) tau
      (knownHighDatumPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small known)
  have first := knownPhysicalOutputOrbit_apply parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau
    (sharedKnownInput parameters lower positive lowerHalf data)
  have second := congrArg packet same.symm
  have third := congrArg (orbitLpAction (RadialL2 3 lower) tau)
    (graphDataPhysicalOutput_highCarrier parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
        (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data)))
  exact first.trans (second.trans third.symm)

/-- Fixed projection is used only to express linearity and smoothness. The
following identity proves this is the SAME original physical Domega field. -/
def sharedKnownFluxOrbit (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      annularOmegaGraph lower L positive lengthPositive :=
  realGraphOperatorProjection (annularOmegaGraph lower L positive lengthPositive)
    (((physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ).comp
      (sharedKnownPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau))

theorem sharedKnownFluxOrbit_apply (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    sharedKnownFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data =
      fluxTranslation lower L positive lengthPositive tau
        (graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
            (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
              (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data)))) := by
  let datum := ActualHighKnownCarrier.toGraphKnownData parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
    (strongToHigh parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
      (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (-tau) data))
  let field := fluxTranslation lower L positive lengthPositive tau
    (graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small datum)
  have coordinates : physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength
      (sharedKnownPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data) = field.val := by
    apply PiLp.ext
    intro coordinate
    apply lp.ext
    funext mode
    rw [sharedKnownPhysicalOutputOrbit_apply, physicalOmegaCoordinates_covariant]
    exact (fluxTranslation_apply lower L positive lengthPositive tau
      (graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small datum) coordinate mode).symm
  change (annularOmegaGraph lower L positive lengthPositive).orthogonalProjectionOnto
    (physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength
      (sharedKnownPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau data)) = field
  exact (congrArg (annularOmegaGraph lower L positive lengthPositive).orthogonalProjectionOnto coordinates).trans
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self field)

theorem sharedKnownFluxOrbit_contDiff :
    ContDiff ℝ ∞ (sharedKnownFluxOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) := by
  let coordinates := (physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ
  let projection := (annularOmegaGraph lower L positive lengthPositive).orthogonalProjectionOnto.restrictScalars ℝ
  have ambient := realOperatorComposition_contDiff (fun _ : OrbitParameter => coordinates)
    (sharedKnownPhysicalOutputOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) contDiff_const
    (sharedKnownPhysicalOutputOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
  exact realOperatorComposition_contDiff (fun _ : OrbitParameter => projection) _ contDiff_const ambient

end Grad.AnnularHighGenerators
