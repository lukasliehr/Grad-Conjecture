import AKBA3ExactWeightedPhysicalCarrier
import AKBA5ExactRadiusDivision

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularCurrentEnergy
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.OriginalKernelRetainedDecay Grad.SourceCollarAngular

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}

def originalRadialCovectorCurves {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow (dimension := 1) parameters lower positive
      (bulkMatrixUnit lower 0 0 (cosineRow lower 0 row)+bulkMatrixUnit lower 0 1 (sineRow lower 0 row)) :=
  (curves.cosine.bulkUnit (0 : Fin 1) 0).add (curves.sine.bulkUnit (0 : Fin 1) 1)

def originalTangentialCovectorCurves {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow (dimension := 1) parameters lower positive
      (bulkMatrixUnit lower 0 1 (cosineRow lower 0 row)-bulkMatrixUnit lower 0 0 (sineRow lower 0 row)) :=
  (curves.cosine.bulkUnit (0 : Fin 1) 1).sub (curves.sine.bulkUnit (0 : Fin 1) 0)

def originalRadialVectorCurves {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow (dimension := 3) parameters lower positive
      (bulkMatrixUnit lower 0 0 (cosineRow lower 0 row)+bulkMatrixUnit lower 1 0 (sineRow lower 0 row)) :=
  (curves.cosine.bulkUnit (0 : Fin 3) 0).add (curves.sine.bulkUnit (1 : Fin 3) 0)

theorem originalRadialCovectorCurves_fullField {row : DivisionRow 3 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalRadialCovectorCurves curves).fullField bounded (radius,angles) =
      originalPolarRadialValue (curves.fullField bounded (radius,angles)) angles.1 := by
  unfold originalRadialCovectorCurves
  rw [SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius inside angles,
    SmoothLowPhysicalRow.fullField_cosine _ bounded radius inside angles,
    SmoothLowPhysicalRow.fullField_sine _ bounded radius inside angles]
  rfl

theorem originalTangentialCovectorCurves_fullField {row : DivisionRow 3 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalTangentialCovectorCurves curves).fullField bounded (radius,angles) =
      originalPolarTangentialValue (curves.fullField bounded (radius,angles)) angles.1 := by
  unfold originalTangentialCovectorCurves
  rw [SmoothLowPhysicalRow.fullField_sub _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius inside angles,
    SmoothLowPhysicalRow.fullField_cosine _ bounded radius inside angles,
    SmoothLowPhysicalRow.fullField_sine _ bounded radius inside angles]
  rfl

theorem originalRadialVectorCurves_fullField {row : DivisionRow 1 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalRadialVectorCurves curves).fullField bounded (radius,angles) =
      originalPolarRadialVector (curves.fullField bounded (radius,angles)) angles.1 := by
  unfold originalRadialVectorCurves
  rw [SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded _ _ radius inside angles,
    SmoothLowPhysicalRow.fullField_cosine _ bounded radius inside angles,
    SmoothLowPhysicalRow.fullField_sine _ bounded radius inside angles]
  rfl

end Grad.OriginalKernelGraphRestriction
