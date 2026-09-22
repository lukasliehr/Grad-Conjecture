import FC3LinearJet
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- Multiplication by the literal positive phase, as a complex-linear map of closed jets. -/
def phaseWeightedJetLinear {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ) :
    ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := phaseWeightedJet parameters cell
  map_add' := phaseWeightedJet_add parameters cell
  map_smul' scalar field := by
    change phaseWeightedJet parameters cell (closedJetSmul scalar field) =
      closedJetSmul scalar (phaseWeightedJet parameters cell field)
    exact phaseWeightedJet_complex_smul parameters cell scalar field

/-- One actual phase-weighted Cartesian derivative in `L²(D,E)`. -/
def weightedDerivativeL2 {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (index : CartesianMultiIndex) : ClosedJet dimension →ₗ[ℂ] DiskL2 dimension :=
  (closedDerivativeL2 index).comp (phaseWeightedJetLinear parameters cell)

theorem weightedDerivativeL2_apply {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (index : CartesianMultiIndex) (field : ClosedJet dimension) :
    weightedDerivativeL2 parameters cell index field =
      closedContinuousToDiskL2
        (closedMultiDerivative (phaseWeightedJet parameters cell field) index) := rfl

/-- The exact factor `lambda_n^(q-|alpha|)` multiplying one derivative coordinate. -/
def gradeDerivativeL2 {dimension grade : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (index : GradeMultiIndex grade) : ClosedJet dimension →ₗ[ℂ] DiskL2 dimension :=
  ((cellFrequency cell : ℂ) ^
      (grade - cartesianOrder index.toCartesian)) •
    weightedDerivativeL2 parameters cell index.toCartesian

theorem gradeDerivativeL2_apply {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (index : GradeMultiIndex grade) (field : ClosedJet dimension) :
    gradeDerivativeL2 parameters cell index field =
      (cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian) •
        closedContinuousToDiskL2
          (closedMultiDerivative (phaseWeightedJet parameters cell field) index.toCartesian) := rfl

/-- The finite Hilbert product over all unordered `|alpha| ≤ q`, each exactly once. -/
abbrev CartesianGradeRow (dimension grade : ℕ) :=
  PiLp 2 (fun _ : GradeMultiIndex grade => DiskL2 dimension)

/-- The finite M1 row of one cell, linear in the original closed jet. -/
def cellGradeRowLinear {dimension grade : ℕ} (parameters : PhaseParameters) (cell : ℤ) :
    ClosedJet dimension →ₗ[ℂ] CartesianGradeRow dimension grade where
  toFun field := WithLp.toLp 2 (fun index => gradeDerivativeL2 parameters cell index field)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (gradeDerivativeL2 parameters cell index).map_add first second
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact (gradeDerivativeL2 parameters cell index).map_smul scalar field

theorem cellGradeRowLinear_apply {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) (index : GradeMultiIndex grade) :
    cellGradeRowLinear parameters cell field index =
      (cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian) •
        closedContinuousToDiskL2
          (closedMultiDerivative (phaseWeightedJet parameters cell field) index.toCartesian) := rfl

/-- The literal M2 coordinates before imposing square summability in the cell index. -/
def rawCartesianGradeCoordinates {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ClosedJet dimension) : ℤ → CartesianGradeRow dimension grade :=
  fun cell => cellGradeRowLinear parameters cell (coefficients cell)

theorem rawCartesianGradeCoordinates_add {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (first second : ℤ → ClosedJet dimension) :
    rawCartesianGradeCoordinates parameters grade (first + second) =
      rawCartesianGradeCoordinates parameters grade first +
        rawCartesianGradeCoordinates parameters grade second := by
  funext cell
  exact (cellGradeRowLinear parameters cell).map_add (first cell) (second cell)

theorem rawCartesianGradeCoordinates_smul {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (scalar : ℂ) (coefficients : ℤ → ClosedJet dimension) :
    rawCartesianGradeCoordinates parameters grade (scalar • coefficients) =
      scalar • rawCartesianGradeCoordinates parameters grade coefficients := by
  funext cell
  exact (cellGradeRowLinear parameters cell).map_smul scalar (coefficients cell)

theorem cellGradeRow_norm_sq {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 =
      ∑ index : GradeMultiIndex grade,
        cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
          ‖closedContinuousToDiskL2
            (closedMultiDerivative (phaseWeightedJet parameters cell field)
              index.toCartesian)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro index _
  rw [cellGradeRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le zero_lt_one (cellFrequency_one_le cell))]
  ring

theorem diskL2_norm_sq {dimension : ℕ} (field : DiskL2 dimension) :
    ‖field‖ ^ 2 =
      ∫ point : SpatialPlane, ‖field point‖ ^ 2 ∂volume.restrict openUnitDisk := by
  let := InnerProductSpace.rclikeToReal ℂ (ComplexEuclidean dimension)
  calc
    ‖field‖ ^ 2 = inner ℝ field field := (real_inner_self_eq_norm_sq field).symm
    _ = ∫ point : SpatialPlane, inner ℝ (field point) (field point)
          ∂volume.restrict openUnitDisk := L2.inner_def (𝕜 := ℝ) field field
    _ = ∫ point : SpatialPlane, ‖field point‖ ^ 2 ∂volume.restrict openUnitDisk := by
      simp only [real_inner_self_eq_norm_sq]

theorem closedDerivativeL2_norm_sq {dimension : ℕ} (field : ClosedJet dimension)
    (index : CartesianMultiIndex) :
    ‖closedDerivativeL2 index field‖ ^ 2 =
      ∫ point : SpatialPlane,
        ‖closedDiskLift (closedMultiDerivative field index) point‖ ^ 2
          ∂volume.restrict openUnitDisk := by
  rw [diskL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [closedDerivativeL2_ae field index] with point equality
  rw [equality]

theorem weightedDerivativeL2_norm_sq {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) (index : CartesianMultiIndex) :
    ‖weightedDerivativeL2 parameters cell index field‖ ^ 2 =
      ∫ point : SpatialPlane,
        ‖closedDiskLift
          (closedMultiDerivative (phaseWeightedJet parameters cell field) index) point‖ ^ 2
          ∂volume.restrict openUnitDisk := by
  exact closedDerivativeL2_norm_sq (phaseWeightedJet parameters cell field) index

end Grad.CartesianState
