import NGP02ClosedBound
import P0910GradeExtension

noncomputable section

set_option maxHeartbeats 1200000

open Set
open scoped BigOperators

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.DiskExtension.Operator
open Grad.DiskExtension.Seeley

local instance ngp02ExteriorCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

def physicalCellRepresentative (cell : CellCircle) : ℝ :=
  (AddCircle.equivIco (2 * Real.pi) 0 cell).val

theorem physicalCellRepresentative_mem_Icc (cell : CellCircle) :
    physicalCellRepresentative cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  constructor
  · exact (AddCircle.equivIco (2 * Real.pi) 0 cell).property.1
  · change (AddCircle.equivIco (2 * Real.pi) 0 cell).val ≤ 2 * Real.pi
    simpa only [zero_add] using
      (AddCircle.equivIco (2 * Real.pi) 0 cell).property.2.le

@[simp] theorem physicalCellRepresentative_coe (cell : CellCircle) :
    ((physicalCellRepresentative cell : ℝ) : CellCircle) = cell := by
  exact AddCircle.coe_equivIco

/-- A grade-only squared factor for the exterior `C^j` bound. -/
noncomputable def exteriorPhysicalCNormSquareFactor (grade : ℕ) : ℝ :=
  exteriorGradeGeometryBound grade ^ 2 * absoluteMoment grade *
    (grade + 1 : ℝ) * closedCNormQuadraticFactor grade *
      absoluteMoment grade

theorem exteriorPhysicalCNormSquareFactor_nonnegative (grade : ℕ) :
    0 ≤ exteriorPhysicalCNormSquareFactor grade := by
  unfold exteriorPhysicalCNormSquareFactor
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg _)
          (absoluteMoment_nonnegative grade)) (by positivity))
      (closedCNormQuadraticFactor_nonnegative grade))
    (absoluteMoment_nonnegative grade)

theorem exteriorGradeQuadraticSeries_le_physicalCNorm
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (grade : ℕ)
    (cell : ℝ) (point : SpatialPlane) :
    exteriorGradeQuadraticSeries field grade cell point ≤
      (closedCNormQuadraticFactor grade *
          closedPhysicalCNorm field grade ^ 2) * absoluteMoment grade := by
  have indicatorLe :
      planarClosedGradeCollar.indicator (fun _ => (1 : ℝ)) point ≤ 1 := by
    by_cases membership : point ∈ planarClosedGradeCollar
    · simp [Set.indicator_of_mem membership]
    · simp [Set.indicator, membership]
  have globalMomentNonnegative :
      0 ≤ closedDerivativeGradeQuadraticGlobalBound field grade *
          absoluteMoment grade :=
    mul_nonneg
      (closedDerivativeGradeQuadraticGlobalBound_nonnegative field grade)
      (absoluteMoment_nonnegative grade)
  calc
    exteriorGradeQuadraticSeries field grade cell point ≤
        (closedDerivativeGradeQuadraticGlobalBound field grade *
          absoluteMoment grade) *
            planarClosedGradeCollar.indicator (fun _ => (1 : ℝ)) point :=
      exteriorGradeQuadraticSeries_le_compactMajorant field grade cell point
    _ ≤ closedDerivativeGradeQuadraticGlobalBound field grade *
          absoluteMoment grade :=
      mul_le_of_le_one_right globalMomentNonnegative indicatorLe
    _ ≤ (closedCNormQuadraticFactor grade *
          closedPhysicalCNorm field grade ^ 2) * absoluteMoment grade :=
      mul_le_mul_of_nonneg_right
        (closedDerivativeGradeQuadraticGlobalBound_le_physicalCNorm field grade)
        (absoluteMoment_nonnegative grade)

/-- Uniform exterior pointwise bound, now expressed only through the literal
closed physical `C^grade` norm. -/
theorem exteriorHigherDerivative_norm_sq_le_physicalCNorm
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (point : SpatialPlane)
    (upper : order ≤ grade) (outside : 1 < ‖point‖)
    (cellMembership : cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖exteriorHigherDerivative field order
      (assembleSpatialCell point cell)‖ ^ 2 ≤
      exteriorPhysicalCNormSquareFactor grade *
        closedPhysicalCNorm field grade ^ 2 := by
  have baseNonnegative : 0 ≤
      exteriorGradeGeometryBound grade ^ 2 * absoluteMoment grade *
        (grade + 1 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (absoluteMoment_nonnegative grade))
      (by positivity)
  calc
    ‖exteriorHigherDerivative field order
        (assembleSpatialCell point cell)‖ ^ 2 ≤
      exteriorGradeGeometryBound grade ^ 2 * absoluteMoment grade *
        (grade + 1 : ℝ) *
          exteriorGradeQuadraticSeries field grade cell point :=
      exteriorHigherDerivative_norm_sq_le_uniformQuadraticSeries
        field grade order cell point upper outside cellMembership
    _ ≤ exteriorGradeGeometryBound grade ^ 2 * absoluteMoment grade *
        (grade + 1 : ℝ) *
          ((closedCNormQuadraticFactor grade *
              closedPhysicalCNorm field grade ^ 2) * absoluteMoment grade) :=
      mul_le_mul_of_nonneg_left
        (exteriorGradeQuadraticSeries_le_physicalCNorm
          field grade cell point) baseNonnegative
    _ = exteriorPhysicalCNormSquareFactor grade *
        closedPhysicalCNorm field grade ^ 2 := by
      unfold exteriorPhysicalCNormSquareFactor
      ring

theorem exteriorHigherDerivative_norm_le_physicalCNorm
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : ℝ) (point : SpatialPlane)
    (upper : order ≤ grade) (outside : 1 < ‖point‖)
    (cellMembership : cell ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖exteriorHigherDerivative field order
      (assembleSpatialCell point cell)‖ ≤
      Real.sqrt (exteriorPhysicalCNormSquareFactor grade) *
        closedPhysicalCNorm field grade := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _)
      (closedPhysicalCNorm_nonnegative field))).mp
  calc
    ‖exteriorHigherDerivative field order
        (assembleSpatialCell point cell)‖ ^ 2 ≤
      exteriorPhysicalCNormSquareFactor grade *
        closedPhysicalCNorm field grade ^ 2 :=
      exteriorHigherDerivative_norm_sq_le_physicalCNorm
        field grade order cell point upper outside cellMembership
    _ = (Real.sqrt (exteriorPhysicalCNormSquareFactor grade) *
          closedPhysicalCNorm field grade) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt
        (exteriorPhysicalCNormSquareFactor_nonnegative grade)]

/-- One common direct factor handles both the retained disk and the exterior
part of the same P09 extension. -/
noncomputable def physicalExtensionCNormFactor (grade : ℕ) : ℝ :=
  1 + Real.sqrt (exteriorPhysicalCNormSquareFactor grade)

theorem physicalExtensionCNormFactor_nonnegative (grade : ℕ) :
    0 ≤ physicalExtensionCNormFactor grade := by
  unfold physicalExtensionCNormFactor
  positivity

theorem ambientHigherDerivative_norm_le_physicalCNorm
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (grade order : ℕ) (cell : CellCircle) (point : SpatialPlane)
    (upper : order ≤ grade) :
    ‖ambientHigherDerivative field order
      (assembleSpatialCell point (physicalCellRepresentative cell))‖ ≤
      physicalExtensionCNormFactor grade *
        closedPhysicalCNorm field grade := by
  by_cases inside : ‖point‖ ≤ 1
  · rw [ambientHigherDerivative, if_pos (by
        simpa only [planarPart_assembleSpatialCell] using inside)]
    have closedBound :
        ‖closedHigherDerivative (order := order) field
          (assembleSpatialCell point (physicalCellRepresentative cell))‖ ≤
          closedPhysicalCNorm field grade := by
      change ‖closedPhysicalOperatorDerivative field order
        (retractedDiskCell
          (assembleSpatialCell point (physicalCellRepresentative cell)))‖ ≤ _
      exact (closedPhysicalOperatorDerivative field order).norm_coe_le_norm _ |>.trans
        (closedPhysicalOperatorDerivative_norm_le_cNorm field upper)
    exact closedBound.trans (by
      apply le_mul_of_one_le_left (closedPhysicalCNorm_nonnegative field)
      unfold physicalExtensionCNormFactor
      linarith [Real.sqrt_nonneg (exteriorPhysicalCNormSquareFactor grade)])
  · have exteriorBound := exteriorHigherDerivative_norm_le_physicalCNorm
      field grade order (physicalCellRepresentative cell) point upper
        (lt_of_not_ge inside) (physicalCellRepresentative_mem_Icc cell)
    rw [ambientHigherDerivative, if_neg (by
      simpa only [planarPart_assembleSpatialCell] using inside)]
    exact exteriorBound.trans (by
      apply mul_le_mul_of_nonneg_right _
        (closedPhysicalCNorm_nonnegative field)
      unfold physicalExtensionCNormFactor
      linarith [Real.sqrt_nonneg (exteriorPhysicalCNormSquareFactor grade)])

end Grad.CartesianState
