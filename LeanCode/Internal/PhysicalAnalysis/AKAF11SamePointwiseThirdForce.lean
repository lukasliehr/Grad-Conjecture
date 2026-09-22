import AKAF10SamePointwiseFirstForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.AnnularPhysicalReconstruction Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.ActualSmoothPhysicalField Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.PhaseAlgebra
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

theorem physicalCurve_meanFree {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    curves.meanFree.physicalCurve 0 radius mode = if mode.1 = 0 then 0 else curves.physicalCurve 0 radius mode := by
  rw [curves.meanFree.physicalCurve_coefficient bounded 0 radius inside mode,
    curves.physicalCurve_coefficient bounded 0 radius inside mode]
  change _ • ((if mode.1 = 0 then (0 : ℂ) else 1) • curves.curve 0 radius mode) = _
  split_ifs <;> simp

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : AnnularReconstructionState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))

/-- The third original polar force identity holds pointwise on the SAME full
smooth fields, with the original length factor and angular mean-free projection. -/
theorem sharedFull_thirdForce_pointwise (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    let covariant := curves.covariant parameters length compact lower positive bounded state
    let rotated := curves.rotatedCovariant parameters length compact lower positive bounded state
    let force := physicalForceCurves parameters length compact lower positive bounded state 1 covariant
    (rotated.bulkUnit (0 : Fin 1) 2).fullField bounded (radius,angles) +
      removePolarMean (fun query => force.fullField bounded (radius,query)) angles -
      (length : ℂ)⁻¹ • (curves.bulkUnit (0 : Fin 1) 2).fullField bounded (radius,angles) =
      (curves.bulkUnit (0 : Fin 1) 6).fullField bounded (radius,angles) := by
  let covariant := curves.covariant parameters length compact lower positive bounded state
  let rotated := curves.rotatedCovariant parameters length compact lower positive bounded state
  let force := physicalForceCurves parameters length compact lower positive bounded state 1 covariant
  let combined := ((rotated.bulkUnit (0 : Fin 1) 2).add force.meanFree).sub
    ((curves.bulkUnit (0 : Fin 1) 2).smul (length : ℂ)⁻¹)
  let target := curves.bulkUnit (0 : Fin 1) 6
  have combinedCoefficient (location : ℝ) (member : location ∈ Icc lower 1) (mode : ℤ × ℤ) :
      combined.physicalCurve 0 location mode 0 =
      rotated.physicalCurve 0 location mode 2 +
        (if mode.1 = 0 then 0 else force.physicalCurve 0 location mode 0) -
        (length : ℂ)⁻¹ * curves.physicalCurve 0 location mode 2 := by
    dsimp only [combined]
    rw [physicalCurve_sub,physicalCurve_add,physicalCurve_smul]
    change ((rotated.bulkUnit (0 : Fin 1) 2).physicalCurve 0 location mode +
      force.meanFree.physicalCurve 0 location mode -
        (length : ℂ)⁻¹ • (curves.bulkUnit (0 : Fin 1) 2).physicalCurve 0 location mode) 0 = _
    rw [physicalCurve_bulkUnit rotated 0 2 bounded location member mode,
      physicalCurve_bulkUnit curves 0 2 bounded location member mode,
      physicalCurve_meanFree force bounded location member mode]
    by_cases zero : mode.1 = 0 <;> simp [zero,matrixUnit_apply,operatorBasis]
  have equality := samePhysical_fullField_eq combined target bounded (by
    filter_upwards [combined.physicalCurve_actual bounded 0,target.physicalCurve_actual bounded 0,
      force.physicalCurve_actual bounded 0,curves.physicalCurve_actual bounded 0,
      rotated.physicalCurve_actual bounded 0,
      sharedFull_thirdForce_physicalCoefficients parameters length compact lower positive bounded lengthPositive state data solution,
      ae_restrict_mem measurableSet_Icc]
        with location combinedSame targetSame forceSame sevenSame rotatedSame law member
    intro mode
    simp only [pow_zero,one_smul] at combinedSame targetSame forceSame sevenSame rotatedSame
    rw [← combinedSame mode,← targetSame mode]
    apply PiLp.ext
    intro component
    fin_cases component
    change combined.physicalCurve 0 location mode (0 : Fin 1) = target.physicalCurve 0 location mode (0 : Fin 1)
    rw [combinedCoefficient location member mode]
    change _ = (curves.bulkUnit (0 : Fin 1) 6).physicalCurve 0 location mode 0
    rw [physicalCurve_bulkUnit curves 0 6 bounded location member mode]
    simp [matrixUnit_apply,operatorBasis]
    rw [forceSame mode,sevenSame mode,rotatedSame mode]
    have actual := law mode
    simpa only [sharedFullCovariant,sharedFullRotatedCovariant] using actual) radius inside angles
  dsimp only [combined,target] at equality
  rw [SmoothLowPhysicalRow.fullField_sub _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    samePhysical_fullField_smul _ bounded (length : ℂ)⁻¹ radius inside angles,
    SmoothLowPhysicalRow.fullField_meanFree force bounded radius inside angles] at equality
  exact equality

end Grad.ActualPolarEquations
