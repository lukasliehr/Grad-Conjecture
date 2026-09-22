import AKAF9PhysicalCurveLinearCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.AnnularPhysicalReconstruction Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.ActualSmoothPhysicalField Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.PhaseAlgebra
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : AnnularReconstructionState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))

/-- The first original polar force identity holds pointwise on the SAME full
smooth fields, with the original factor two and full F0. -/
theorem sharedFull_firstForce_pointwise (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    let covariant := curves.covariant parameters length compact lower positive bounded state
    let rotated := curves.rotatedCovariant parameters length compact lower positive bounded state
    let force := physicalForceCurves parameters length compact lower positive bounded state 0 covariant
    force.fullField bounded (radius,angles) +
      (curves.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,angles) -
      (rotated.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,angles) -
      (2 : ℂ) • (covariant.bulkUnit (0 : Fin 1) 0).fullField bounded (radius,angles) =
      (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,angles) := by
  let covariant := curves.covariant parameters length compact lower positive bounded state
  let rotated := curves.rotatedCovariant parameters length compact lower positive bounded state
  let force := physicalForceCurves parameters length compact lower positive bounded state 0 covariant
  let combined := ((force.add (curves.bulkUnit (0 : Fin 1) 1)).sub
    (rotated.bulkUnit (0 : Fin 1) 1)).sub ((covariant.bulkUnit (0 : Fin 1) 0).smul 2)
  let target := curves.bulkUnit (0 : Fin 1) 4
  have combinedCoefficient (location : ℝ) (member : location ∈ Icc lower 1) (mode : ℤ × ℤ) :
      combined.physicalCurve 0 location mode 0 =
      force.physicalCurve 0 location mode 0 + curves.physicalCurve 0 location mode 1 -
        rotated.physicalCurve 0 location mode 1 - 2 * covariant.physicalCurve 0 location mode 0 := by
    dsimp only [combined]
    rw [physicalCurve_sub,physicalCurve_sub,physicalCurve_add,physicalCurve_smul]
    change (force.physicalCurve 0 location mode + (curves.bulkUnit (0 : Fin 1) 1).physicalCurve 0 location mode -
      (rotated.bulkUnit (0 : Fin 1) 1).physicalCurve 0 location mode -
        (2 : ℂ) • (covariant.bulkUnit (0 : Fin 1) 0).physicalCurve 0 location mode) 0 = _
    rw [physicalCurve_bulkUnit curves 0 1 bounded location member mode,
      physicalCurve_bulkUnit rotated 0 1 bounded location member mode,
      physicalCurve_bulkUnit covariant 0 0 bounded location member mode]
    simp [matrixUnit_apply,operatorBasis]
  have equality := samePhysical_fullField_eq combined target bounded (by
    filter_upwards [combined.physicalCurve_actual bounded 0,target.physicalCurve_actual bounded 0,
      force.physicalCurve_actual bounded 0,curves.physicalCurve_actual bounded 0,
      covariant.physicalCurve_actual bounded 0,rotated.physicalCurve_actual bounded 0,
      sharedFull_firstForce_physicalCoefficients parameters length compact lower positive bounded lengthPositive state data solution,
      ae_restrict_mem measurableSet_Icc]
        with location combinedSame targetSame forceSame sevenSame covariantSame rotatedSame law member
    intro mode
    simp only [pow_zero,one_smul] at combinedSame targetSame forceSame sevenSame covariantSame rotatedSame
    rw [← combinedSame mode,← targetSame mode]
    apply PiLp.ext
    intro component
    fin_cases component
    change combined.physicalCurve 0 location mode (0 : Fin 1) = target.physicalCurve 0 location mode (0 : Fin 1)
    rw [combinedCoefficient location member mode]
    change _ = (curves.bulkUnit (0 : Fin 1) 4).physicalCurve 0 location mode 0
    rw [physicalCurve_bulkUnit curves 0 4 bounded location member mode]
    simp [matrixUnit_apply,operatorBasis]
    rw [forceSame mode,sevenSame mode,covariantSame mode,rotatedSame mode]
    have actual := law mode
    dsimp only [sharedFullCovariant,sharedFullRotatedCovariant] at actual
    linear_combination actual) radius inside angles
  dsimp only [combined,target] at equality
  rw [SmoothLowPhysicalRow.fullField_sub _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_sub _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    samePhysical_fullField_smul _ bounded 2 radius inside angles] at equality
  exact equality

end Grad.ActualPolarEquations
