import AIQ13UniformCrossEnergyBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph

def crossOutputConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  eliminatedBulkConstant parameters L compact 0 * crossResponseSize parameters L compact * (4 + 2 * |L|) *
    (32 * crossKnownConstant parameters L compact) +
    4 * eliminatedBulkConstant parameters L compact 0 * crossResponseSize parameters L compact + 3

theorem crossOutputConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ crossOutputConstant parameters L compact := by
  unfold crossOutputConstant
  have := eliminatedBulkConstant_nonnegative parameters L compact 0
  have := crossResponseSize_nonnegative parameters L compact
  have := crossKnownConstant_nonnegative parameters L compact
  positivity

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

def crossPhysicalOutputValue (data : CrossHighData parameters lower) : DivisionRow 3 lower :=
  actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    (crossKnownWeighted parameters lower data) (crossKnownAuxiliary parameters lower data)

theorem crossPhysicalOutputValue_add (first second : CrossHighData parameters lower) :
    crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small (first + second) =
      crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small first +
      crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small second := by
  simp only [crossPhysicalOutputValue, crossEnergyValue_add, crossKnownWeighted_add, crossKnownAuxiliary_add,
    actualFullHighOutput, actualHighKnownBulkOutput, map_add]
  abel

theorem crossPhysicalOutputValue_smul (scalar : ℂ) (data : CrossHighData parameters lower) :
    crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small (scalar • data) =
      scalar • crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
  simp only [crossPhysicalOutputValue, crossEnergyValue_smul, crossKnownWeighted_smul, crossKnownAuxiliary_smul,
    actualFullHighOutput, actualHighKnownBulkOutput, map_smul, smul_add]

theorem crossPhysicalOutputValue_bound (data : CrossHighData parameters lower) :
    ‖crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ ≤
      crossOutputConstant parameters L compact * ‖data‖ := by
  have output := actualFullHighOutput_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    (crossKnownWeighted parameters lower data) (crossKnownAuxiliary parameters lower data)
  obtain ⟨weighted, auxiliary, _datum⟩ := crossKnown_embedding_bounds parameters lower data
  change ‖crossKnownWeighted parameters lower data‖ ≤ ‖data‖ at weighted
  change ‖crossKnownAuxiliary parameters lower data‖ ≤ ‖data‖ at auxiliary
  obtain ⟨size0, _size1⟩ := crossResponseSize_bounds parameters L compact state small
  have energy := crossEnergyValue_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have base := eliminatedBulkConstant_nonnegative parameters L compact 0
  have size := crossResponseSize_nonnegative parameters L compact
  have known := crossKnownConstant_nonnegative parameters L compact
  apply output.trans
  calc
    _ ≤ eliminatedBulkConstant parameters L compact 0 * crossResponseSize parameters L compact * (4 + 2 * |L|) *
        ((32 * crossKnownConstant parameters L compact) * ‖data‖) +
        4 * eliminatedBulkConstant parameters L compact 0 * crossResponseSize parameters L compact * ‖data‖ + 3 * ‖data‖ := by
      gcongr
    _ = crossOutputConstant parameters L compact * ‖data‖ := by unfold crossOutputConstant; ring

def crossPhysicalOutputLinear : CrossHighData parameters lower →ₗ[ℂ] DivisionRow 3 lower where
  toFun := crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
  map_add' := crossPhysicalOutputValue_add parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
  map_smul' := crossPhysicalOutputValue_smul parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small

def crossPhysicalOutputResponse : CrossHighData parameters lower →L[ℂ] DivisionRow 3 lower :=
  (crossPhysicalOutputLinear parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).mkContinuous
    (crossOutputConstant parameters L compact)
    (crossPhysicalOutputValue_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

def crossFluxResponse : CrossHighData parameters lower →L[ℂ] annularOmegaGraph lower L positive lengthPositive :=
  ((physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength).comp
    (crossPhysicalOutputResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)).codRestrict
      (annularOmegaGraph lower L positive lengthPositive)
      (fun data => (graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (data.toGraphKnown parameters lower)).property)

/-- The actual BF high inverse response, in the unchanged W × Domega Hilbert carrier. -/
def actualHighCrossResponse : CrossHighData parameters lower →L[ℂ] CrossHighSpace lower L positive lengthPositive :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (annularEnergySpace lower L positive)
    (annularOmegaGraph lower L positive lengthPositive)).symm.toContinuousLinearMap.comp
      ((crossEnergyResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).prod
        (crossFluxResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small))

theorem actualHighCrossResponse_energy (data : CrossHighData parameters lower) :
    (actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1 =
      graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (data.toGraphKnown parameters lower) := rfl

theorem actualHighCrossResponse_flux (data : CrossHighData parameters lower) :
    (actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.2 =
      graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (data.toGraphKnown parameters lower) := rfl

end Grad.AnnularPhysicalSolution
