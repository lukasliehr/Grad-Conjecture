import COR12DiskCoefficient

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.CartesianState

def originalCoordinateEnergy {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (index : GradeMultiIndex grade) : ℝ :=
  ∑' cell : ℤ,
    cellFrequency cell ^
        (2 * (grade - cartesianOrder index.toCartesian)) *
      ‖closedDerivativeL2 index.toCartesian
        (phaseWeightedJet parameters cell (field.1 cell))‖ ^ 2

theorem originalCoordinateEnergy_summable {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (index : GradeMultiIndex grade) :
    Summable (fun cell : ℤ =>
      cellFrequency cell ^
          (2 * (grade - cartesianOrder index.toCartesian)) *
        ‖closedDerivativeL2 index.toCartesian
          (phaseWeightedJet parameters cell (field.1 cell))‖ ^ 2) := by
  let coordinate : ℤ → DiskL2 dimension := fun cell =>
    rawCartesianGradeCoordinates parameters grade field.1 cell index
  have coordinateMem : Memℓp coordinate 2 := by
    apply (field.property grade).mono'
    intro cell
    exact PiLp.norm_apply_le
      (rawCartesianGradeCoordinates parameters grade field.1 cell) index
  have coordinateSquare : Summable (fun cell : ℤ => ‖coordinate cell‖ ^ 2) :=
    (memlp_iff_summable_sq coordinate).mp coordinateMem
  apply coordinateSquare.congr
  intro cell
  rw [show coordinate cell =
      (cellFrequency cell : ℂ) ^
          (grade - cartesianOrder index.toCartesian) •
        closedDerivativeL2 index.toCartesian
          (phaseWeightedJet parameters cell (field.1 cell)) by rfl,
    norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (cellFrequency_pos cell)]
  ring

theorem originalGrade_norm_sq_eq_sum_coordinateEnergy {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) :
    ‖(GradeCore.ofCoreLinear (grade := grade) field)‖ ^ 2 =
      ∑ index : GradeMultiIndex grade,
        originalCoordinateEnergy parameters field index := by
  rw [gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_sq]
  calc
    (∑' cell : ℤ, ∑ index : GradeMultiIndex grade,
        cellFrequency cell ^
            (2 * (grade - cartesianOrder index.toCartesian)) *
          ∫ point : SpatialPlane,
            ‖closedDiskLift
              (closedMultiDerivative
                (phaseWeightedJet parameters cell (field.1 cell))
                index.toCartesian) point‖ ^ 2
              ∂volume.restrict openUnitDisk) =
        ∑' cell : ℤ, ∑ index : GradeMultiIndex grade,
          cellFrequency cell ^
              (2 * (grade - cartesianOrder index.toCartesian)) *
            ‖closedDerivativeL2 index.toCartesian
              (phaseWeightedJet parameters cell (field.1 cell))‖ ^ 2 := by
      apply tsum_congr
      intro cell
      apply Finset.sum_congr rfl
      intro index _
      rw [closedDerivativeL2_norm_sq]
    _ = ∑ index : GradeMultiIndex grade,
        ∑' cell : ℤ,
          cellFrequency cell ^
              (2 * (grade - cartesianOrder index.toCartesian)) *
            ‖closedDerivativeL2 index.toCartesian
              (phaseWeightedJet parameters cell (field.1 cell))‖ ^ 2 := by
      exact Summable.tsum_finsetSum
        (fun index _ => originalCoordinateEnergy_summable parameters field index)
    _ = ∑ index : GradeMultiIndex grade,
        originalCoordinateEnergy parameters field index := rfl

theorem originalCoordinateEnergy_nonnegative {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (index : GradeMultiIndex grade) :
    0 ≤ originalCoordinateEnergy parameters field index := by
  exact tsum_nonneg fun _ => mul_nonneg
    (pow_nonneg (cellFrequency_pos _).le _) (sq_nonneg _)

theorem originalCoordinateEnergy_le_norm_sq {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (index : GradeMultiIndex grade) :
    originalCoordinateEnergy parameters field index ≤
      ‖(GradeCore.ofCoreLinear (grade := grade) field)‖ ^ 2 := by
  rw [originalGrade_norm_sq_eq_sum_coordinateEnergy]
  exact Finset.single_le_sum
    (fun candidate _ => originalCoordinateEnergy_nonnegative parameters field candidate)
    (Finset.mem_univ index)

end Grad.COR12Extension

