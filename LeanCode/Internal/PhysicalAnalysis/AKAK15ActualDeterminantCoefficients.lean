import AKAK14ActualDeterminantFields
import AKAK8LiteralSevenUnknownCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.SourceCollarFullSource Grad.BoundaryTrace

private theorem zeroGradeCoefficient_recover (frequency : ℂ)
    (physical stored represented literal : ComplexEuclidean 1)
    (actual : physical = frequency^0 • stored) (selected : stored = represented) (same : represented = literal) :
    physical = literal := by
  simpa only [pow_zero,one_smul,selected,same] using actual

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)

/-- Exact original physical coefficients of (x,c,rV,g). -/
theorem actualDeterminantCoefficientCurves_actual :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      (fun index => actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius index mode) =
        ![sameCoupledXCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field 0
            (radialClamp lower (lowerHalf.trans (by norm_num)) radius) mode,
          lowRhoPhysicalCoefficient parameters lower positive
            (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 1
              (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)) radius mode,
          lowRhoPhysicalCoefficient parameters lower positive
            (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 2
              (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)) radius mode,
          lowRhoPhysicalCoefficient parameters lower positive
            (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2 radius mode] := by
  filter_upwards [(seven.bulkUnit (0 : Fin 1) 0).physicalCurve_actual (lowerHalf.trans_lt (by norm_num)) 0,
    (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 1).physicalCurve_actual (lowerHalf.trans_lt (by norm_num)) 0,
    (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2).physicalCurve_actual (lowerHalf.trans_lt (by norm_num)) 0,
    third.physicalCurve_actual (lowerHalf.trans_lt (by norm_num)) 0,
    fullStrongSevenInput_firstFour_physical parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive data field,
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (0 : Fin 7)
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)]
      with radius x c v g coordinates selected
  intro mode
  funext index
  fin_cases index
  · change (seven.bulkUnit (0 : Fin 1) 0).physicalCurve 0 radius mode = _
    exact zeroGradeCoefficient_recover (annularFrequency mode.1 mode.2 : ℂ)
      ((seven.bulkUnit (0 : Fin 1) 0).physicalCurve 0 radius mode)
      (lowRhoPhysicalCoefficient parameters lower positive
        (Grad.AnnularCurrentEnergy.bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 7)
          (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)) radius mode)
      (matrixUnit (0 : Fin 1) (0 : Fin 7) (lowRhoPhysicalCoefficient parameters lower positive
        (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field) radius mode))
      (sameCoupledXCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field 0
        (radialClamp lower (lowerHalf.trans (by norm_num)) radius) mode)
      (x mode) (selected mode) (coordinates mode 0)
  · change (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 1).physicalCurve 0 radius mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 1
          (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)) radius mode
    simpa only [pow_zero,one_smul] using c mode
  · change (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2).physicalCurve 0 radius mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 2
          (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)) radius mode
    simpa only [pow_zero,one_smul] using v mode
  · change third.physicalCurve 0 radius mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2 radius mode
    simpa only [pow_zero,one_smul] using g mode

end Grad.ActualPolarEquations
