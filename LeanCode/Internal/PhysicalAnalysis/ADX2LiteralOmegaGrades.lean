import ADX1ExactOmegaDiagonals

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOmegaGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Literal split/inserted grade membership for Domega: the weight is
required on both the value and the normalized derivative coordinate. -/
def HasAnnularOmegaGrade (lower : ℝ) (angular cell inserted : ℕ)
    (field : AnnularOmegaAmbient lower) : Prop :=
  HasAnnularLpGrade angular cell inserted (field 0) ∧
    HasAnnularLpGrade angular cell inserted (field 1)

def annularOmegaWeightedAmbient (lower : ℝ) (angular cell inserted : ℕ)
    (field : AnnularOmegaAmbient lower) (grade : HasAnnularOmegaGrade lower angular cell inserted field) :
    AnnularOmegaAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => AnnularBulk lower)).symm
    ![annularLpWeighted angular cell inserted (field 0) grade.1,
      annularLpWeighted angular cell inserted (field 1) grade.2]

theorem annularOmegaWeightedAmbient_zero (lower : ℝ) (angular cell inserted : ℕ)
    (field : AnnularOmegaAmbient lower) (grade : HasAnnularOmegaGrade lower angular cell inserted field) :
    annularOmegaWeightedAmbient lower angular cell inserted field grade 0 =
      annularLpWeighted angular cell inserted (field 0) grade.1 := rfl

theorem annularOmegaWeightedAmbient_one (lower : ℝ) (angular cell inserted : ℕ)
    (field : AnnularOmegaAmbient lower) (grade : HasAnnularOmegaGrade lower angular cell inserted field) :
    annularOmegaWeightedAmbient lower angular cell inserted field grade 1 =
      annularLpWeighted angular cell inserted (field 1) grade.2 := rfl

/-- Reweighting both literal coordinates preserves the same fixed-mode
distributional Domega relation. -/
theorem annularOmegaWeightedAmbient_mem (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive)
    (grade : HasAnnularOmegaGrade lower angular cell inserted field.val) :
    annularOmegaWeightedAmbient lower angular cell inserted field.val grade ∈
      annularOmegaGraph lower length positive lengthPositive := by
  rw [annularOmegaGraph_mem_iff]
  intro mode
  have relation := (annularOmegaGraph_mem_iff lower length positive lengthPositive field.val).mp
    field.property mode
  change CollarWeakDerivative lower
    (radialOrdinary 1 lower positive
      ((annularGradeWeight angular cell inserted mode : ℂ) • field.val 0 mode))
    (collarScalar 1 lower (annularOmegaCurve lower length positive mode)
      (radialOrdinary 1 lower positive
        ((annularGradeWeight angular cell inserted mode : ℂ) • field.val 1 mode)))
  simpa only [map_smul] using
    collarWeakDerivative_complex_smul lower (annularGradeWeight angular cell inserted mode : ℂ)
      _ _ relation

def annularOmegaWeightedGraph (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive)
    (grade : HasAnnularOmegaGrade lower angular cell inserted field.val) :
    annularOmegaGraph lower length positive lengthPositive :=
  ⟨annularOmegaWeightedAmbient lower angular cell inserted field.val grade,
    annularOmegaWeightedAmbient_mem lower length positive lengthPositive angular cell inserted field grade⟩

/-- The bounded inverse grade map on the exact closed Domega graph. -/
def annularOmegaGraphDecode (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ) :
    annularOmegaGraph lower length positive lengthPositive →L[ℂ]
      annularOmegaGraph lower length positive lengthPositive :=
  annularOmegaGraphDiagonal lower length positive lengthPositive
    (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹)
    1 (by norm_num) (annularGradeWeight_inv_bound angular cell inserted)

theorem annularOmegaGraphDecode_zero (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted field).val 0 =
      annularLpDecode angular cell inserted (field.val 0) := by
  simpa only [annularOmegaGraphDecode, annularLpDecode] using
    annularOmegaGraphDiagonal_value lower length positive lengthPositive
      (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1 (by norm_num)
      (annularGradeWeight_inv_bound angular cell inserted) field

theorem annularOmegaGraphDecode_one (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted field).val 1 =
      annularLpDecode angular cell inserted (field.val 1) := by
  simpa only [annularOmegaGraphDecode, annularLpDecode] using
    annularOmegaGraphDiagonal_slope lower length positive lengthPositive
      (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1 (by norm_num)
      (annularGradeWeight_inv_bound angular cell inserted) field

theorem annularOmegaGraphDecode_hasGrade (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    HasAnnularOmegaGrade lower angular cell inserted
      (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted field).val := by
  constructor
  · rw [annularOmegaGraphDecode_zero]
    exact annularLpDecode_hasGrade angular cell inserted (field.val 0)
  · rw [annularOmegaGraphDecode_one]
    exact annularLpDecode_hasGrade angular cell inserted (field.val 1)

theorem annularOmegaGraphDecode_weighted (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive)
    (grade : HasAnnularOmegaGrade lower angular cell inserted field.val) :
    annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted
      (annularOmegaWeightedGraph lower length positive lengthPositive angular cell inserted field grade) = field := by
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · have result :
        (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted
          (annularOmegaWeightedGraph lower length positive lengthPositive angular cell inserted
            field grade)).val 0 = field.val 0 := by
      rw [annularOmegaGraphDecode_zero]
      change annularLpDecode angular cell inserted
        (annularOmegaWeightedAmbient lower angular cell inserted field.val grade 0) = field.val 0
      rw [annularOmegaWeightedAmbient_zero]
      exact annularLpDecode_weighted angular cell inserted (field.val 0) grade.1
    simpa using result
  · have result :
        (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted
          (annularOmegaWeightedGraph lower length positive lengthPositive angular cell inserted
            field grade)).val 1 = field.val 1 := by
      rw [annularOmegaGraphDecode_one]
      change annularLpDecode angular cell inserted
        (annularOmegaWeightedAmbient lower angular cell inserted field.val grade 1) = field.val 1
      rw [annularOmegaWeightedAmbient_one]
      exact annularLpDecode_weighted angular cell inserted (field.val 1) grade.2
    simpa using result

theorem annularOmegaGraphDecode_injective (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ) :
    Function.Injective (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted) :=
  annularOmegaGraphDiagonal_injective lower length positive lengthPositive _ 1 (by norm_num)
    (annularGradeWeight_inv_bound angular cell inserted)
    (fun mode => inv_ne_zero (annularGradeWeight_pos angular cell inserted mode).ne')

/-- Both directions of the literal two-coordinate grade realization. -/
theorem annularOmegaGraphGrade_iff (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    HasAnnularOmegaGrade lower angular cell inserted field.val ↔
      ∃ weighted : annularOmegaGraph lower length positive lengthPositive,
        annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted weighted = field := by
  constructor
  · intro grade
    exact ⟨annularOmegaWeightedGraph lower length positive lengthPositive angular cell inserted field grade,
      annularOmegaGraphDecode_weighted lower length positive lengthPositive angular cell inserted field grade⟩
  · rintro ⟨weighted, rfl⟩
    exact annularOmegaGraphDecode_hasGrade lower length positive lengthPositive angular cell inserted weighted

/-- The reciprocal equivalence intertwines the literal Domega grade decode
with AAQ17's exact Dnu grade decode. -/
theorem annularOmegaNormalization_decode (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    annularOmegaNormalizationEquivalence lower length positive lengthPositive
      (annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted field) =
      annularFluxGraphDecode lower positive angular cell inserted
        (annularOmegaNormalizationEquivalence lower length positive lengthPositive field) := by
  simpa only [annularOmegaGraphDecode, annularFluxGraphDecode] using
    annularOmegaNormalization_diagonal lower length positive lengthPositive
      (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1 (by norm_num)
      (annularGradeWeight_inv_bound angular cell inserted) field

/-- Literal Domega grade membership is exactly AAQ17 grade membership
after the proved reciprocal normalization equivalence. -/
theorem annularOmegaGrade_iff_fluxGrade (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    HasAnnularOmegaGrade lower angular cell inserted field.val ↔
      HasAnnularFluxGrade lower positive angular cell inserted
        (annularOmegaNormalizationEquivalence lower length positive lengthPositive field) := by
  constructor
  · intro grade
    obtain ⟨weighted, equality⟩ :=
      (annularOmegaGraphGrade_iff lower length positive lengthPositive angular cell inserted field).mp grade
    have normalized := congrArg
      (annularOmegaNormalizationEquivalence lower length positive lengthPositive) equality
    rw [annularOmegaNormalization_decode] at normalized
    exact (congrArg (HasAnnularFluxGrade lower positive angular cell inserted) normalized).mp
      (annularFluxGraphDecode_hasGrade lower positive angular cell inserted
        (annularOmegaNormalizationEquivalence lower length positive lengthPositive weighted))
  · intro grade
    let normalized := annularOmegaNormalizationEquivalence lower length positive lengthPositive field
    let weighted := annularFluxGraphWeighted lower positive angular cell inserted normalized grade
    let omegaWeighted :=
      (annularOmegaNormalizationEquivalence lower length positive lengthPositive).symm weighted
    have fluxEquality : annularFluxGraphDecode lower positive angular cell inserted weighted = normalized :=
      annularFluxGraphDecode_weighted lower positive angular cell inserted normalized grade
    have omegaEquality :
        annularOmegaGraphDecode lower length positive lengthPositive angular cell inserted omegaWeighted = field := by
      apply (annularOmegaNormalizationEquivalence lower length positive lengthPositive).injective
      rw [annularOmegaNormalization_decode]
      simpa only [omegaWeighted, normalized, ContinuousLinearEquiv.apply_symm_apply] using fluxEquality
    exact (congrArg (fun output : annularOmegaGraph lower length positive lengthPositive =>
      HasAnnularOmegaGrade lower angular cell inserted output.val) omegaEquality).mp
        (annularOmegaGraphDecode_hasGrade lower length positive lengthPositive angular cell inserted omegaWeighted)

/-- The original Hilbert norm of the literal weighted Domega field is
exactly the sum of the two weighted-coordinate squares. -/
theorem annularOmegaWeightedGraph_norm_sq (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length positive lengthPositive)
    (grade : HasAnnularOmegaGrade lower angular cell inserted field.val) :
    ‖annularOmegaWeightedGraph lower length positive lengthPositive angular cell inserted field grade‖ ^ 2 =
      ‖annularLpWeighted angular cell inserted (field.val 0) grade.1‖ ^ 2 +
        ‖annularLpWeighted angular cell inserted (field.val 1) grade.2‖ ^ 2 := by
  rw [annularOmegaGraph_norm_sq]
  rfl

end Grad.AnnularOmegaGraph
