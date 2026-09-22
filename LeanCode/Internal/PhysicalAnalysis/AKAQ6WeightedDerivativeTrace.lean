import AKAQ5ExactRetractionCell
import QO17ScalarMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ContDiff
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets Grad.COR12Extension
open Grad.COR13Completion Grad.SourceCollarDivision Grad.Constraints
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.BoundaryLift

def imaginaryWaveLinear (mode : SpatialMode) : SpatialPlane →L[ℝ] ℂ :=
  Complex.I • (Complex.ofRealCLM.comp
    ((Real.pi / 2) • ((mode.1 : ℝ) • EuclideanSpace.proj 0 + (mode.2 : ℝ) • EuclideanSpace.proj 1)))

theorem imaginaryWaveLinear_apply (mode : SpatialMode) (point : SpatialPlane) :
    imaginaryWaveLinear mode point = Complex.I * (waveAngle mode point : ℂ) := by rfl

def planeWave {dimension : ℕ} (mode : SpatialMode) (value : ComplexEuclidean dimension)
    (point : SpatialPlane) : ComplexEuclidean dimension :=
  Complex.exp (imaginaryWaveLinear mode point) • value

theorem planeWave_smooth {dimension : ℕ} (mode : SpatialMode) (value : ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (planeWave mode value) := by
  exact ((imaginaryWaveLinear mode).contDiff.cexp).smul contDiff_const

theorem planeWave_derivative {dimension : ℕ} (mode : SpatialMode) (value : ComplexEuclidean dimension)
    (point direction : SpatialPlane) :
    fderiv ℝ (planeWave mode value) point direction =
      (Complex.exp (imaginaryWaveLinear mode point) * imaginaryWaveLinear mode direction) • value := by
  have law := (((imaginaryWaveLinear mode).hasFDerivAt (x := point)).cexp.smul_const value).fderiv
  rw [show planeWave mode value = (fun point => Complex.exp (imaginaryWaveLinear mode point) • value) from rfl,law]
  rfl

def weightedValueAt {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ) (point : ClosedDisk) :
    AGrade parameters dimension 4 →L[ℂ] ComplexEuclidean dimension :=
  (ContinuousMap.evalCLM ℂ point).comp (completedWeightedCell parameters (by omega) cell)

def weightedDerivativeAt {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) (point : ClosedDisk) :
    AGrade parameters dimension 4 →L[ℂ] ComplexEuclidean dimension :=
  ((spatialPartial direction (cartesianPhase parameters cell) point.val : ℝ) : ℂ) • weightedValueAt parameters cell point +
    (cartesianWeight parameters cell point.val : ℂ) •
      ((ContinuousMap.evalCLM ℂ point).comp (completedCellDerivative parameters 1 (fun _ => direction) cell))

theorem weightedDerivativeAt_core {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) (point : ClosedDisk) (field : GradeCore parameters dimension 4) :
    weightedDerivativeAt parameters cell direction point (aGradeEta parameters field) =
      partialCoefficient direction (phaseWeightedJet parameters cell (field.toCore.val cell)) point := by
  rw [phaseWeighted_partial_value]
  simp only [weightedDerivativeAt,add_apply,smul_apply,
    weightedValueAt,ContinuousLinearMap.comp_apply,ContinuousMap.evalCLM_apply,completedWeightedCell_core,
    completedCellDerivative_eta,partialCoefficient]
  rw [Complex.coe_smul,Complex.coe_smul]

/-- Exact first derivative of the same original weighted completed cell. -/
theorem retraction_single_weightedJet {dimension : ℕ} (parameters : PhaseParameters)
    (mode : SpatialMode) (source cell : ℤ) (value : ComplexEuclidean dimension) :
    phaseWeightedJet parameters cell ((weightedFourierRetraction parameters
      (singleCore (fibreMode (source,mode)) value)).val cell) =
      if source = cell then globalClosedJet (planeWave mode value) (planeWave_smooth mode value) else 0 := by
  classical
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have law := completedRetraction_single_weightedCell parameters mode source cell value point
  rw [← coreToGrade_single,completedRetraction_apply_core,completedWeightedCell_core] at law
  change (phaseWeightedJet parameters cell ((weightedFourierRetraction parameters
      (singleCore (fibreMode (source,mode)) value)).val cell)).value point = _ at law
  by_cases same : source = cell
  · simpa [same,globalClosedJet_value,planeWave,imaginaryWaveLinear_apply] using law
  · simpa [same] using law

theorem completedRetraction_single_weightedDerivative {dimension : ℕ} (parameters : PhaseParameters)
    (mode : SpatialMode) (source cell : ℤ) (value : ComplexEuclidean dimension)
    (direction : Fin 2) (point : ClosedDisk) :
    weightedDerivativeAt parameters cell direction point
      (completedRetraction parameters (coefficientSingle 4 (fibreMode (source,mode)) value)) =
      if source = cell then
        (Complex.exp (imaginaryWaveLinear mode point.val) * imaginaryWaveLinear mode (spatialBasis direction)) • value else 0 := by
  classical
  rw [← coreToGrade_single,completedRetraction_apply_core,weightedDerivativeAt_core]
  change partialCoefficient direction (phaseWeightedJet parameters cell ((weightedFourierRetraction parameters
      (singleCore (fibreMode (source,mode)) value)).val cell)) point = _
  rw [retraction_single_weightedJet]
  by_cases same : source = cell
  · simp only [if_pos same]
    change (partialJet direction (globalClosedJet (planeWave mode value) (planeWave_smooth mode value))).value point = _
    rw [partialJet_global_value,planeWave_derivative]
  · simp only [if_neg same,partialCoefficient]
    change (closedDerivativeLinear 1 (fun _ => direction)) (0 : ClosedJet dimension) point = 0
    rw [map_zero]
    rfl

end Grad.OriginalFlatAxisDecay
