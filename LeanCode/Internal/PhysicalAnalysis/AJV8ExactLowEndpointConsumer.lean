import AJV7OriginalLowRestrictionIdentities

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularLowEnergy
open Grad.AnnularOriginalLow Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower upper length : ℝ)
    (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (bounded : upper < 1) (lengthPositive : 0 < length)

/-- Exact V1 low retained block: all measured original coordinates and
both physical fields refer to the SAME restriction with the new endpoint. -/
theorem originalLowEndpointRestriction_exact (field : originalLowGraph lower) :
    let output := originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field
    (∀ slot : Fin 2, ∀ index : LowAnnularIndex,
      output.val slot index = originalLowEndpointRatio parameters lower upper length index •
        collarL2Restriction 1 lower upper included (field.val slot index)) ∧
    (‖output‖ ≤
      ‖(originalLowGraphEquivalence parameters upper length positiveUpper lengthPositive bounded.le).symm.toContinuousLinearMap‖ *
      ‖(originalLowGraphEquivalence parameters lower length positiveLower lengthPositive (included.trans bounded.le)).toContinuousLinearMap‖ * ‖field‖) ∧
    (∀ index : LowAnnularIndex, ∀ radius : Icc upper (1 : ℝ),
      lowPhysicalSection parameters upper length positiveUpper bounded
        (originalLowGraphEquivalence parameters upper length positiveUpper lengthPositive bounded.le output) index radius =
      lowPhysicalSection parameters lower length positiveLower (included.trans_lt bounded)
        (originalLowGraphEquivalence parameters lower length positiveLower lengthPositive (included.trans bounded.le) field) index
        ⟨radius.val, included.trans radius.property.1, radius.property.2⟩) := by
  dsimp only
  refine ⟨?_, originalLowEndpointRestriction_bound parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field, ?_⟩
  · intro slot index
    fin_cases slot
    · exact originalLowEndpointRestriction_value parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field index
    · exact originalLowEndpointRestriction_slope parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field index
  · intro index radius
    rw [originalLowEndpointRestriction_weighted]
    exact lowEnergyRestriction_physical parameters lower upper length included positiveLower positiveUpper bounded _ index radius

/-- The unchanged original Lambda-grade inclusions commute with restriction. -/
theorem originalLowEndpointRestriction_cellInclusion (grade larger : ℕ) (gradeLe : grade ≤ larger)
    (field : originalLowGraph lower) :
    originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive
      (originalLowAJInclusion lower grade larger gradeLe field) =
    originalLowAJInclusion upper grade larger gradeLe
      (originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field) :=
  originalLowEndpointRestriction_diagonal parameters lower upper length included positiveLower positiveUpper bounded lengthPositive
    (originalLowCellGradeRatio grade larger) 1 (by norm_num) (originalLowCellGradeRatio_bound grade larger gradeLe) field

/-- Full original angular, cell and nu insertion is preserved simultaneously. -/
theorem originalLowEndpointRestriction_splitInclusion
    (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (angularLe : angular ≤ largerAngular) (cellLe : cell ≤ largerCell) (insertedLe : inserted ≤ largerInserted)
    (field : originalLowGraph lower) :
    originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive
      (originalLowGraphDiagonal lower
        (originalLowSplitGradeRatio angular cell inserted largerAngular largerCell largerInserted) 1 (by norm_num)
        (originalLowSplitGradeRatio_bound angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe) field) =
    originalLowGraphDiagonal upper
      (originalLowSplitGradeRatio angular cell inserted largerAngular largerCell largerInserted) 1 (by norm_num)
      (originalLowSplitGradeRatio_bound angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe)
      (originalLowEndpointRestriction parameters lower upper length included positiveLower positiveUpper bounded lengthPositive field) :=
  originalLowEndpointRestriction_diagonal parameters lower upper length included positiveLower positiveUpper bounded lengthPositive
    _ 1 (by norm_num) _ field

end Grad.AnnularRestriction
