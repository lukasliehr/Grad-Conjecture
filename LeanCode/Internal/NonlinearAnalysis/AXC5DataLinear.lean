import AXC4ActualExtraction
import AxisThirteenBound
import AxisProjections

noncomputable section

namespace Grad.ChartAxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.QuotientProjection

variable {parameters : PhaseParameters}

theorem scalarOriginGradient_smul (scalar : ℂ) (field : ACore parameters 1) (cell : ℤ) :
    scalarOriginGradient (scalar • field) cell = scalar • scalarOriginGradient field cell := by
  unfold scalarOriginGradient
  rw [acore_val_smul, originPartial_smul, originPartial_smul, planarPair_smul]
  rfl

theorem planarJPair_smul (scalar : ℂ) (point : ComplexEuclidean 2) :
    planarJPair (scalar • point) = scalar • planarJPair point := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change -(scalar * point 1) = scalar * -(point 1)
    ring
  · rfl

theorem sigmaData_smul (scalar : ℂ) (source : QuotientRows parameters) :
    sigmaData (scalar • source) = scalar • sigmaData source := by
  apply Subtype.ext
  funext cell
  change sigmaExtraction (scalar • source) cell = scalar • sigmaExtraction source cell
  unfold sigmaExtraction
  rw [show (scalar • source) 0 = scalar • source 0 from rfl,
    show (scalar • source) 1 = scalar • source 1 from rfl,
    acore_val_smul, acore_val_smul, originValue_smul, originValue_smul,
    planarPair_smul]
  congr 1
  · change (scalar * originValue ((source 0).val cell) 0 +
        scalar * originValue ((source 1).val cell) 0) / 2 = _
    ring
  · change (scalar * originValue ((source 0).val cell) 0 -
        scalar * originValue ((source 1).val cell) 0) / (2 * Complex.I) = _
    ring

theorem etaData_smul (cellLength : ℝ) (scalar : ℂ) (source : QuotientRows parameters) :
    etaData cellLength (scalar • source) = scalar • etaData cellLength source := by
  apply Subtype.ext
  funext cell
  change etaExtraction cellLength (scalar • source) cell = scalar • etaExtraction cellLength source cell
  unfold etaExtraction
  rw [show (scalar • source) 3 = scalar • source 3 from rfl, scalarOriginGradient_smul]
  have sigmaLaw : sigmaExtraction (scalar • source) cell = scalar • sigmaExtraction source cell :=
    congrArg (fun data => data.val cell) (sigmaData_smul scalar source)
  rw [sigmaLaw, smul_comm ((cell : ℂ) * Complex.I) scalar, ← smul_add,
    planarJPair_smul, smul_comm]

def extractionLinear (parameters : PhaseParameters) (cellLength : ℝ) :
    QuotientRows parameters →ₗ[ℂ] AxisData parameters where
  toFun := extractionData cellLength
  map_add' first second := by
    have law := extractionData_sub cellLength (first + second) second
    rw [add_sub_cancel_right] at law
    exact (eq_sub_iff_add_eq.mp law).symm
  map_smul' scalar source := Prod.ext (sigmaData_smul scalar source)
    (etaData_smul cellLength scalar source)

/-- The exact weighted lp carrier, with the original sum of two T norms. -/
abbrev AxisDataGrade (parameters : PhaseParameters) (grade : ℕ) :=
  WithLp 1 (Grad.AxisCore.AxisGrade parameters 2 (grade + 1) ×
    Grad.AxisCore.AxisGrade parameters 2 (grade + 1))

def axisCoreEmbedding (parameters : PhaseParameters) (grade : ℕ) :
    TCore parameters →ₗ[ℂ] Grad.AxisCore.AxisGrade parameters 2 grade where
  toFun data := ⟨axisCoordinates parameters grade data.val, data.property grade⟩
  map_add' first second := by
    apply Subtype.ext
    exact axisCoordinates_add parameters grade first.val second.val
  map_smul' scalar data := by
    apply Subtype.ext
    exact axisCoordinates_smul parameters grade scalar data.val

def axisDataEmbedding (parameters : PhaseParameters) (grade : ℕ) :
    AxisData parameters →ₗ[ℂ] AxisDataGrade parameters grade where
  toFun data := WithLp.toLp 1
    (axisCoreEmbedding parameters (grade + 1) data.1,
      axisCoreEmbedding parameters (grade + 1) data.2)
  map_add' first second := by
    change WithLp.toLp 1 _ = WithLp.toLp 1 _
    congr 1
    exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' scalar data := by
    change WithLp.toLp 1 _ = WithLp.toLp 1 _
    congr 1
    exact Prod.ext (map_smul _ _ _) (map_smul _ _ _)

theorem axisDataEmbedding_norm (parameters : PhaseParameters) (grade : ℕ)
    (data : AxisData parameters) :
    ‖axisDataEmbedding parameters grade data‖ = axisDataNorm parameters grade data := by
  rw [WithLp.prod_norm_eq_of_L1]
  rfl

theorem rowsGradeNorm_le_quotientNorm (parameters : PhaseParameters) (grade : ℕ)
    (source : QuotientRows parameters) :
    rowsGradeNorm grade source ≤ 4 * quotientNorm parameters grade source := by
  have bound := Finset.sum_le_sum (fun (row : Fin 4) (_ : row ∈ Finset.univ) =>
    quotientNorm_component parameters grade source row)
  simpa [rowsGradeNorm] using bound

theorem extraction_exact_norm_bound (parameters : PhaseParameters) (cellLength : ℝ)
    (grade : ℕ) (source : QuotientRows parameters) :
    ‖axisDataEmbedding parameters grade (extractionLinear parameters cellLength source)‖ ≤
      (4 * extractionBoundConstant cellLength) * quotientNorm parameters (grade + 3) source := by
  rw [axisDataEmbedding_norm]
  exact (extractionData_bound cellLength source grade).trans
    ((mul_le_mul_of_nonneg_left (rowsGradeNorm_le_quotientNorm parameters (grade + 3) source)
      (extractionBoundConstant_nonneg cellLength)).trans_eq (by ring))

end Grad.ChartAxisSplit
