import AKBF13ActualOriginalSourceStartupMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularCrossOrbit Grad.AnnularStrongSolution
open Grad.AnnularStrongData Grad.AnnularSmoothCore Grad.AnnularKernelL2 Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularCurrentEnergy Grad.AnnularFullGraph Grad.AnnularWeightedSmoothCore

/-- Genuine zero angular mode of the same full Xi/r packet. -/
theorem fullStrongScalarOverRadius_zeroAngular (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive) (cell : ℤ) :
    bulkMatrixUnit lower (0 : Fin 1) (3 : Fin 7)
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution) (0,cell) = 0 := by
  apply Lp.ext
  filter_upwards [fullStrongSevenInput_scalarOverRadius parameters length lower positive bounded lengthPositive data solution,
    Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1))] with radius same zero
  rw [zero,same (0,cell),sameCoupledXiCoefficient_meanZero,smul_zero,smul_zero]
  rfl

/-- The stored Xi/r of an arbitrary actual original observation has the
same genuine zero angular mode. -/
theorem originalScalarOverRadius_zeroAngular (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (point : OriginalFiveBlockAmbient parameters lower length positive) (cell : ℤ) :
    originalScalarOverRadius parameters length lower positive bounded.le lengthPositive data point (0,cell) = 0 :=
  fullStrongScalarOverRadius_zeroAngular parameters length lower positive bounded lengthPositive
    (Grad.AnnularExhaustionEstimate.originalWeightedDatum parameters lower length positive bounded.le lengthPositive data)
    (Grad.AnnularWeakExhaustion.originalWeightedRetainedObservation parameters lower length positive bounded.le lengthPositive point) cell

open Grad.SourceCollarFullSource Grad.ActualSmoothPhysicalField Grad.BoundaryTrace Grad.ActualPolarEquations

theorem meanFreeRow_of_zeroAngular {dimension : ℕ} (lower : ℝ) (row : DivisionRow dimension lower)
    (zero : ∀ cell : ℤ, row (0,cell) = 0) : meanFreeRow lower row = row := by
  apply lp.ext
  funext mode
  rw [meanFreeRow_apply]
  by_cases angular : mode.1 = 0
  · rw [if_pos angular]
    have equal : mode = (0,mode.2) := Prod.ext angular rfl
    rw [equal,zero]
  · rw [if_neg angular]

/-- Actual smooth angular mean is zero when its native stored row has
zero angular mode. This is an identity of the SAME physical reconstruction. -/
theorem fullField_mean_of_zeroAngular {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (zero : ∀ cell : ℤ, row (0,cell) = 0)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (axial : ℝ) :
    angularCoefficient (fun polar => curves.fullField bounded (radius,polar,axial)) 0 = 0 := by
  have fixed := meanFreeRow_of_zeroAngular lower row zero
  have same := samePhysical_fullField_eq curves.meanFree curves bounded (by
    filter_upwards with location
    intro mode
    rw [fixed]) radius inside (0,axial)
  rw [curves.fullField_meanFree bounded radius inside (0,axial)] at same
  change curves.fullField bounded (radius,0,axial) -
    angularCoefficient (fun polar => curves.fullField bounded (radius,polar,axial)) 0 =
      curves.fullField bounded (radius,0,axial) at same
  exact sub_eq_self.mp same

end Grad.ActualPhysicalField
