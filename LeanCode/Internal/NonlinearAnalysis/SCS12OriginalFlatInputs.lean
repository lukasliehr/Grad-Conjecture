import SCS11DecodedRowAlgebra
import AXF26CartesianFlatRange

noncomputable section

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarBulk
open Grad.AxisSplit Grad.AxisJet Grad.AxisCore Grad.Constraints Grad.QuotientProjection Grad.FlatSourceProjection

theorem originalValueFlat_of_traceZero {dimension grade : ℕ}
    (parameters : PhaseParameters) (large : 3 ≤ grade) (field : ACore parameters dimension)
    (zero : traceZero field = 0) :
    OriginalValueFlat parameters large (aGradeEta parameters (GradeCore.ofCoreLinear field)) := by
  intro cell
  rw [completedOriginalCell_core]
  have point : ambientClosedDisk (0 : SpatialPlane) = originPoint := ambientClosedDisk_coe originPoint
  rw [point]
  exact congrFun (congrArg Subtype.val zero) cell

theorem originalValueFlat_of_meanZero {grade : ℕ}
    (parameters : PhaseParameters) (large : 3 ≤ grade) (field : ACore parameters 1)
    (zero : angularCore parameters 0 field = 0) :
    OriginalValueFlat parameters large (aGradeEta parameters (GradeCore.ofCoreLinear field)) := by
  intro cell
  rw [completedOriginalCell_core]
  have point : ambientClosedDisk (0 : SpatialPlane) = originPoint := ambientClosedDisk_coe originPoint
  rw [point]
  have value := congrArg (fun candidate : ACore parameters 1 => originValue (candidate.val cell)) zero
  change originValue (angularClosedJet 0 (field.val cell)) = originValue (0 : ClosedJet 1) at value
  rw [angularJet_zero_originValue, originValue_zero] at value
  exact value

/-- Both divided source inputs are flat as a consequence of the ORIGINAL
BS4 constraints. No additional axis condition is inserted in the source. -/
theorem originalFlatSource_division_inputs {grade : ℕ}
    (parameters : PhaseParameters) (large : 3 ≤ grade)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    OriginalValueFlat parameters large
      (originalSourcePlanar parameters grade (quotientEta parameters grade source)) ∧
    OriginalValueFlat parameters large (quotientEta parameters grade source 3) := by
  have cartesian := (isFlat_iff_cartesian source).mp flat
  constructor
  · rw [originalSourcePlanar_core]
    exact originalValueFlat_of_traceZero parameters large _ cartesian.2.1
  · exact originalValueFlat_of_meanZero parameters large _ cartesian.2.2.2.2.1

end Grad.SourceCollarFullSource
