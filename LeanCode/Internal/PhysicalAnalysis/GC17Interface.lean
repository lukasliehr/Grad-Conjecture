import GC16Consumer
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def operatorMatrix {input output : ℕ} (value : OperatorValue input output) :
    Matrix (Fin output) (Fin input) ℂ :=
  fun row column => value (WithLp.toLp 2 fun index => if index = column then 1 else 0) row

/-- Literal Fourier value of the zero spatial derivative at any coefficient
grade. No finite-cell truncation and no weighted-field reconstruction. -/
def coefficientPhysicalValue {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (angle : ℝ) (point : ClosedDisk) : OperatorValue input output :=
  ∑' cell : ℤ, fourierPhase cell angle •
    coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) point

def physicalFrameMatrix (parameters : PhaseParameters) (L ell epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) (point : ClosedDisk) : Matrix (Fin 3) (Fin 3) ℂ :=
  operatorMatrix (referenceFrame + fourierEvaluation (actualFrameFamily parameters L ell epsilon field 0) angle point)

def physicalSeedMatrix (rho alpha delta parameter angle : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  operatorMatrix (harmonicSeedOperator rho alpha delta parameter angle)

def planarPhysicalInclusion : Matrix (Fin 3) (Fin 2) ℂ :=
  fun row column => if (row = 0 ∧ column = 0) ∨ (row = 2 ∧ column = 1) then 1 else 0

def toroidalPhysicalColumn : Matrix (Fin 3) (Fin 1) ℂ :=
  fun row _ => if row = 1 then 1 else 0

def planarFrameColumns : Matrix (Fin 3) (Fin 2) ℂ :=
  fun row column => if row.val = column.val then 1 else 0

def thirdFrameColumn : Matrix (Fin 3) (Fin 1) ℂ :=
  fun row _ => if row = 2 then 1 else 0

def spatialColumn (point : ClosedDisk) : Matrix (Fin 2) (Fin 1) ℂ :=
  fun row _ => (point.val row : ℂ)

def circleTraceCovector (point : ClosedDisk) : Matrix (Fin 1) (Fin 3) ℂ :=
  fun _ column => if bounded : column.val < 2 then (point.val ⟨column.val, bounded⟩ : ℂ) else 0

/-- Exact AO5 stacked rows; all transposes are algebraic, not Hermitian. -/
def physicalGaugeMatrix (seed seedDerivative : Matrix (Fin 2) (Fin 2) ℂ)
    (inverseTranspose : Matrix (Fin 3) (Fin 3) ℂ) (point : ClosedDisk) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun row column => if bounded : row.val < 2 then
    (seed.transpose * planarPhysicalInclusion.transpose * inverseTranspose) ⟨row.val, bounded⟩ column
  else
    ((toroidalPhysicalColumn + planarPhysicalInclusion * seedDerivative * spatialColumn point).transpose *
      inverseTranspose) 0 column

def firstSpatialIndex : DerivativeIndex 1 := ⟨(⟨1, by omega⟩, ⟨0, by omega⟩), by norm_num⟩
def secondSpatialIndex : DerivativeIndex 1 := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by norm_num⟩

/-- The actual R F, with R = -Y2 d1 + Y1 d2 on the rescaled cap. -/
def rotatedPhysicalFrameMatrix (parameters : PhaseParameters) (L ell epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) (point : ClosedDisk) : Matrix (Fin 3) (Fin 3) ℂ :=
  operatorMatrix (
    (-(point.val 1 : ℂ)) • (∑' cell : ℤ, fourierPhase cell angle •
      coefficientDerivative (actualFrameFamily parameters L ell epsilon field 1) cell firstSpatialIndex point) +
    (point.val 0 : ℂ) • (∑' cell : ℤ, fourierPhase cell angle •
      coefficientDerivative (actualFrameFamily parameters L ell epsilon field 1) cell secondSpatialIndex point))

def primitiveSize {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3) (grade : ℕ) : ℝ :=
  ‖actualFrameFamily parameters L ell epsilon field grade‖ +
    ‖seedMatrixDeviationCoefficient admissible grade rho alpha delta parameter‖ +
    ‖seedDerivativeCoefficient admissible grade rho alpha delta parameter‖

/-- Actual coefficients of AQ14–AQ15. Every field is tied to the literal
physical frame, harmonic seed, fixed Y and algebraic matrix formulas.
No inverse, cofactor, row or angular derivative is supplied as a premise. -/
structure LedgerBundle (Square Small Trace Planar : Type) where
  frameInverse : Square
  seedInverse : Small
  inverseTransposeDeviation : Square
  gaugeDeviation : Square
  fluxDeviation : Square
  traceDeviation : Trace
  rotatedFrame : Square
  rotatedPlanarProduct : Planar
  rotatedThirdProduct : Trace

abbrev LedgerData (L sigma gamma ell : ℝ) :=
  LedgerBundle (CoefficientFamily L sigma gamma ell 3 3)
    (CoefficientFamily L sigma gamma ell 2 2) (CoefficientFamily L sigma gamma ell 3 1)
    (CoefficientFamily L sigma gamma ell 3 2)

def LedgerCoherent {L sigma gamma ell : ℝ} (data : LedgerData L sigma gamma ell) : Prop :=
  @FamilyCoherent L sigma gamma ell 3 3 data.frameInverse ∧
  @FamilyCoherent L sigma gamma ell 2 2 data.seedInverse ∧
  @FamilyCoherent L sigma gamma ell 3 3 data.inverseTransposeDeviation ∧
  @FamilyCoherent L sigma gamma ell 3 3 data.gaugeDeviation ∧
  @FamilyCoherent L sigma gamma ell 3 3 data.fluxDeviation ∧
  @FamilyCoherent L sigma gamma ell 3 1 data.traceDeviation ∧
  @FamilyCoherent L sigma gamma ell 3 3 data.rotatedFrame ∧
  @FamilyCoherent L sigma gamma ell 3 2 data.rotatedPlanarProduct ∧
  @FamilyCoherent L sigma gamma ell 3 1 data.rotatedThirdProduct

def frameInverse_identityLaw {L ell : ℝ} (parameters : PhaseParameters)
    (_admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (_rho _alpha _delta _parameter epsilon : ℝ) (field : ACore parameters 3)
    (data : LedgerData L parameters.sigma0 parameters.gamma ell) : Prop :=
  ∀ (grade : ℕ) (angle : ℝ) (point : ClosedDisk),
    let frame := physicalFrameMatrix parameters L ell epsilon field angle point
    let inverse := operatorMatrix (coefficientPhysicalValue (data.frameInverse grade) angle point)
    frame * inverse = 1 ∧ inverse * frame = 1

def seedInverse_identityLaw {L ell : ℝ} (parameters : PhaseParameters)
    (_admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter _epsilon : ℝ) (_field : ACore parameters 3)
    (data : LedgerData L parameters.sigma0 parameters.gamma ell) : Prop :=
  ∀ (grade : ℕ) (angle : ℝ) (point : ClosedDisk),
    let seed := physicalSeedMatrix rho alpha delta parameter angle
    let inverse := operatorMatrix (coefficientPhysicalValue (data.seedInverse grade) angle point)
    seed * inverse = 1 ∧ inverse * seed = 1

def inverseTranspose_formulaLaw {L ell : ℝ} (parameters : PhaseParameters)
    (_admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (_rho _alpha _delta _parameter _epsilon : ℝ) (_field : ACore parameters 3)
    (data : LedgerData L parameters.sigma0 parameters.gamma ell) : Prop :=
  ∀ (grade : ℕ) (angle : ℝ) (point : ClosedDisk),
    operatorMatrix (coefficientPhysicalValue (data.inverseTransposeDeviation grade) angle point) =
      (operatorMatrix (coefficientPhysicalValue (data.frameInverse grade) angle point)).transpose -
        (operatorMatrix referenceFrame).transpose

def gauge_formulaLaw {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter _epsilon : ℝ) (_field : ACore parameters 3)
    (data : LedgerData L parameters.sigma0 parameters.gamma ell) : Prop :=
  ∀ (grade : ℕ) (angle : ℝ) (point : ClosedDisk),
    operatorMatrix (coefficientPhysicalValue (data.gaugeDeviation grade) angle point) =
      physicalGaugeMatrix (physicalSeedMatrix rho alpha delta parameter angle)
        (operatorMatrix (fourierEvaluation (seedDerivativeCoefficient admissible 0 rho alpha delta parameter) angle point))
        (operatorMatrix (coefficientPhysicalValue (data.frameInverse grade) angle point)).transpose point - 1

def flux_formulaLaw {L ell : ℝ} (parameters : PhaseParameters)
    (_admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (_rho _alpha _delta _parameter epsilon : ℝ) (field : ACore parameters 3)
    (data : LedgerData L parameters.sigma0 parameters.gamma ell) : Prop :=
  ∀ (grade : ℕ) (angle : ℝ) (point : ClosedDisk),
    let frame := physicalFrameMatrix parameters L ell epsilon field angle point
    let inverse := operatorMatrix (coefficientPhysicalValue (data.frameInverse grade) angle point)
    operatorMatrix (coefficientPhysicalValue (data.fluxDeviation grade) angle point) =
      frame.det • (inverse * inverse.transpose) + 1

def trace_formulaLaw {L ell : ℝ} (parameters : PhaseParameters)
    (_admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (_rho _alpha _delta _parameter _epsilon : ℝ) (_field : ACore parameters 3)
    (data : LedgerData L parameters.sigma0 parameters.gamma ell) : Prop :=
  ∀ (grade : ℕ) (angle : ℝ) (point : ClosedDisk),
    operatorMatrix (coefficientPhysicalValue (data.traceDeviation grade) angle point) =
      (spatialColumn point).transpose *
        operatorMatrix (coefficientPhysicalValue (data.seedInverse grade) angle point) *
          planarPhysicalInclusion.transpose *
            (operatorMatrix (coefficientPhysicalValue (data.frameInverse grade) angle point)).transpose -
              circleTraceCovector point

def rotation_formulaLaw {L ell : ℝ} (parameters : PhaseParameters)
    (_admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (_rho _alpha _delta _parameter epsilon : ℝ) (field : ACore parameters 3)
    (data : LedgerData L parameters.sigma0 parameters.gamma ell) : Prop :=
  ∀ (grade : ℕ) (angle : ℝ) (point : ClosedDisk),
    operatorMatrix (coefficientPhysicalValue (data.rotatedFrame grade) angle point) =
      rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point

def rotatedPlanar_formulaLaw {L ell : ℝ} (parameters : PhaseParameters)
    (_admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (_rho _alpha _delta _parameter epsilon : ℝ) (field : ACore parameters 3)
    (data : LedgerData L parameters.sigma0 parameters.gamma ell) : Prop :=
  ∀ (grade : ℕ) (angle : ℝ) (point : ClosedDisk),
    operatorMatrix (coefficientPhysicalValue (data.rotatedPlanarProduct grade) angle point) =
      (rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point * planarFrameColumns).transpose *
        (operatorMatrix (coefficientPhysicalValue (data.frameInverse grade) angle point)).transpose

def rotatedThird_formulaLaw {L ell : ℝ} (parameters : PhaseParameters)
    (_admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (_rho _alpha _delta _parameter epsilon : ℝ) (field : ACore parameters 3)
    (data : LedgerData L parameters.sigma0 parameters.gamma ell) : Prop :=
  ∀ (grade : ℕ) (angle : ℝ) (point : ClosedDisk),
    operatorMatrix (coefficientPhysicalValue (data.rotatedThirdProduct grade) angle point) =
      (rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point * thirdFrameColumn).transpose *
        (operatorMatrix (coefficientPhysicalValue (data.frameInverse grade) angle point)).transpose

def ActualLedger {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    := { data : LedgerData L parameters.sigma0 parameters.gamma ell // LedgerCoherent data ∧
  frameInverse_identityLaw parameters admissible rho alpha delta parameter epsilon field data ∧
  seedInverse_identityLaw parameters admissible rho alpha delta parameter epsilon field data ∧
  inverseTranspose_formulaLaw parameters admissible rho alpha delta parameter epsilon field data ∧
  gauge_formulaLaw parameters admissible rho alpha delta parameter epsilon field data ∧
  flux_formulaLaw parameters admissible rho alpha delta parameter epsilon field data ∧
  trace_formulaLaw parameters admissible rho alpha delta parameter epsilon field data ∧
  rotation_formulaLaw parameters admissible rho alpha delta parameter epsilon field data ∧
  rotatedPlanar_formulaLaw parameters admissible rho alpha delta parameter epsilon field data ∧
  rotatedThird_formulaLaw parameters admissible rho alpha delta parameter epsilon field data }

def ledgerSizeFour {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field) (grade : ℕ) : ℝ :=
  ‖ledger.val.inverseTransposeDeviation grade‖ +
    ‖ledger.val.seedInverse grade - gradedIdentityCoefficient L parameters.sigma0 parameters.gamma ell grade 2‖ +
    ‖ledger.val.gaugeDeviation grade‖ + ‖ledger.val.fluxDeviation grade‖ + ‖ledger.val.traceDeviation grade‖

def ledgerSizeFive {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field) (grade : ℕ) : ℝ :=
  ‖ledger.val.rotatedFrame grade‖ + ‖ledger.val.rotatedPlanarProduct grade‖ + ‖ledger.val.rotatedThirdProduct grade‖

/-- CT_GC17 on one fixed B6 neighborhood, retaining the supplied AP27
primitive threshold. The choice precedes all grades; full D_g construction
is a separate CT_GC18 obligation, not assumed here. -/
def ActualLedgerGoal : Prop :=
  ∀ (parameters : PhaseParameters) (L radius threshold : ℝ), 0 < L → 0 ≤ radius → 0 < threshold →
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∃ constantsFour constantsFive : ℕ → ℝ,
        (∀ grade, 0 ≤ constantsFour grade) ∧ (∀ grade, 0 ≤ constantsFive grade) ∧
        ∀ (ell rho alpha delta parameter epsilon : ℝ)
          (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
          |rho| ≤ 1 → |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius → |epsilon| ≤ 1 →
          ∀ field : ACore parameters 3, physicalBudget parameters field rho epsilon 6 ≤ lowRadius →
            ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field,
              primitiveSize parameters admissible rho alpha delta parameter epsilon field 2 ≤ threshold ∧
              ∀ grade, ledgerSizeFour ledger grade ≤
                constantsFour grade * physicalBudget parameters field rho epsilon (grade + 4) ∧
                ledgerSizeFive ledger grade ≤
                  constantsFive grade * physicalBudget parameters field rho epsilon (grade + 5)

end Grad.GaugeCoefficients.Physical.Ledger
