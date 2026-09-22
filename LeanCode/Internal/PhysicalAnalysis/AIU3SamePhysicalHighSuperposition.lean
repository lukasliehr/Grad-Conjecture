import AIU2ExactCrossDataAddition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution Grad.AnnularCurrentBoundary

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

theorem graphDataEnergySolution_addCross (data : ActualHighGraphKnownData parameters lower 0 0)
    (cross : CrossHighData parameters lower) :
    graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (addCrossData parameters lower data cross) =
    graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data +
      crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small cross := by
  symm
  apply graphDataEnergySolution_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
  · rw [map_add, map_add, graphDataEnergySolution_physical_inner, crossEnergyValue_inner, add_zero]
    rfl
  · intro test
    rw [currentHighFormValue_add_field, crossEnergyValue_equation]
    have law := actualHighGraphEnergySolution_complex parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      data.weighted data.auxiliary data.graphs data.datum data.innerValue test
    change currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) test.val = _ at law
    rw [law]
    exact (addCrossData_functional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data cross test.val).symm

/-- The physical flux packet, including direct qc/rqv terms, superposes
for the same high field. -/
theorem graphDataPhysicalOutput_addCross (data : ActualHighGraphKnownData parameters lower 0 0)
    (cross : CrossHighData parameters lower) :
    graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (addCrossData parameters lower data cross) =
    graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data +
      crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small cross := by
  unfold graphDataPhysicalOutput crossPhysicalOutputValue
  rw [graphDataEnergySolution_addCross]
  simp only [addCrossData, actualFullHighOutput, actualHighKnownBulkOutput, map_add]
  abel

/-- Both complete graph coordinates belong to the same superposed physical flux. -/
theorem graphDataPhysicalFlux_addCross (data : ActualHighGraphKnownData parameters lower 0 0)
    (cross : CrossHighData parameters lower) :
    graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (addCrossData parameters lower data cross) =
    graphDataPhysicalFlux parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data +
      crossFluxResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small cross := by
  apply Subtype.ext
  change physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength
      (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (addCrossData parameters lower data cross)) = _
  rw [graphDataPhysicalOutput_addCross, map_add]
  rfl

theorem fullKnownHighResponse_addCross (data : ActualHighGraphKnownData parameters lower 0 0)
    (cross : CrossHighData parameters lower) :
    fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (addCrossData parameters lower data cross) =
    fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data +
      actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small cross := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · exact graphDataEnergySolution_addCross parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data cross
  · exact graphDataPhysicalFlux_addCross parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data cross

end Grad.AnnularFullSource
