import AID9ExactOmegaDerivativeCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph
open Grad.AnnularOmegaGraph Grad.AnnularFluxTrace

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

/-- The original two Hilbert coordinates: sqrt(r)y and sqrt(r)omega⁻¹y'. -/
def physicalOmegaCoordinates : DivisionRow 3 lower →L[ℂ] AnnularOmegaAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => AnnularBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![highPhysicalOutput lower 0,
      physicalOmegaSlope parameters lower L positive lengthPositive widthHalf widthLength])

theorem physicalOmegaCoordinates_value (field : DivisionRow 3 lower) :
    physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field 0 =
      highPhysicalOutput lower 0 field := rfl

theorem physicalOmegaCoordinates_slope (field : DivisionRow 3 lower) :
    physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field 1 =
      physicalOmegaSlope parameters lower L positive lengthPositive widthHalf widthLength field := rfl

theorem physicalOmegaCoordinates_norm_sq (field : DivisionRow 3 lower) :
    ‖physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field‖ ^ 2 =
      ‖highPhysicalOutput lower 0 field‖ ^ 2 +
      ‖physicalOmegaSlope parameters lower L positive lengthPositive widthHalf widthLength field‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  rfl

theorem physicalOmegaCoordinates_bound (field : DivisionRow 3 lower) :
    ‖physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field‖ ≤ 4 * ‖field‖ := by
  have value := highPhysicalOutput_bound lower (0 : Fin 3) field
  have slope := physicalOmegaSlope_bound parameters lower L positive lengthPositive widthHalf widthLength field
  have square := physicalOmegaCoordinates_norm_sq parameters lower L positive lengthPositive widthHalf widthLength field
  have valueSquare := mul_self_le_mul_self (norm_nonneg _) value
  have slopeSquare := mul_self_le_mul_self (norm_nonneg _) slope
  nlinarith [norm_nonneg (physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field),
    norm_nonneg field]

/-- The physical weak equation places these SAME two coordinates in the accepted closed Domega graph. -/
theorem physicalOmegaCoordinates_mem (bounded : lower < 1) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field) :
    physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field ∈
      annularOmegaGraph lower L positive lengthPositive := by
  rw [annularOmegaGraph_mem_iff]
  intro mode
  rw [physicalOmegaCoordinates_value, physicalOmegaCoordinates_slope, physicalOmegaSlope_ordinary]
  exact physicalFluxOrdinary_weak parameters lower L positive lengthPositive widthHalf widthLength bounded field equation mode

/-- Actual graph realization with no independent derivative or endpoint coordinate. -/
def physicalFluxGraph (bounded : lower < 1) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field) :
    annularOmegaGraph lower L positive lengthPositive :=
  ⟨physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field,
    physicalOmegaCoordinates_mem parameters lower L positive lengthPositive widthHalf widthLength bounded field equation⟩

/-- Radius-independent original graph estimate for the literal completed flux packet. -/
theorem physicalFluxGraph_bound (bounded : lower < 1) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field) :
    ‖physicalFluxGraph parameters lower L positive lengthPositive widthHalf widthLength bounded field equation‖ ≤ 4 * ‖field‖ :=
  physicalOmegaCoordinates_bound parameters lower L positive lengthPositive widthHalf widthLength field

end Grad.AnnularCurrentGreen
