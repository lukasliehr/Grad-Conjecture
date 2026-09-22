import GC14Proof
import Grad.GeometryClosure.Seed

noncomputable section

open Set MeasureTheory
open scoped BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

/-- The paper's physical coordinate order is `(y₁, toroidal, y₂)`. -/
def referenceStateValue (point : ClosedDisk) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ![(point.val 0 : ℂ), 0, (point.val 1 : ℂ)]

def physicalRotation : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![-value 1, value 0, 0]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp
        ring
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp }

/-- The exact AO1 constant Cartesian frame `(iota e₁,iota e₂,e_T)`. -/
def referenceFrame : OperatorValue 3 3 :=
  columnEmbedding 3 3 0 (WithLp.toLp 2 ![1, 0, 0]) +
    columnEmbedding 3 3 1 (WithLp.toLp 2 ![0, 0, 1]) +
    columnEmbedding 3 3 2 (WithLp.toLp 2 ![0, 1, 0])

/-- Original, unweighted physical displacement. The estimate below is valid
for every such state, hence in particular for the normalized physical states. -/
def physicalStateLift {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 3 grade) (point : ClosedDisk) (coordinate : ℝ) :
    ComplexEuclidean 3 :=
  referenceStateValue point + originalPhysicalEvaluationLift parameters field point coordinate

/-- The actual cell coefficient of the reference linear physical state. -/
def referenceStateCell (cell : ℤ) (point : ClosedDisk) : ComplexEuclidean 3 :=
  if cell = 0 then referenceStateValue point else 0

/-- Literal Cartesian frame deviation, before the substitution `y = ell Y`:
the third column includes the actual cell derivative and curvature term. -/
def frameDeviationCell {grade : ℕ} (parameters : PhaseParameters)
    (L epsilon : ℝ) (field : GradeCore parameters 3 grade)
    (cell : ℤ) (point : ClosedDisk) : OperatorValue 3 3 :=
  columnEmbedding 3 3 0 (closedDerivative (field.toCore.1 cell) 1 (fun _ => 0) point) +
    columnEmbedding 3 3 1 (closedDerivative (field.toCore.1 cell) 1 (fun _ => 1) point) +
    columnEmbedding 3 3 2 ((L : ℂ)⁻¹ •
      ((Complex.I * (cell : ℂ)) • (field.toCore.1 cell).value point +
        (epsilon : ℂ) • physicalRotation
          (referenceStateCell cell point + (field.toCore.1 cell).value point)))

def referenceStateMultiDerivative (cell : ℤ) (index : CartesianMultiIndex)
    (point : ClosedDisk) : ComplexEuclidean 3 :=
  if cell = 0 then
    if index = (0, 0) then referenceStateValue point else
    if index = (1, 0) then WithLp.toLp 2 ![1, 0, 0] else
    if index = (0, 1) then WithLp.toLp 2 ![0, 0, 1] else 0
  else 0

/-- All Cartesian derivatives of the actual, unscaled frame columns. -/
def frameDeviationMultiDerivative {grade : ℕ} (parameters : PhaseParameters)
    (L epsilon : ℝ) (field : GradeCore parameters 3 grade)
    (cell : ℤ) (index : CartesianMultiIndex) (point : ClosedDisk) : OperatorValue 3 3 :=
  columnEmbedding 3 3 0
      (closedMultiDerivative (shiftedClosedJet (field.toCore.1 cell) (fun _ : Fin 1 => 0)) index point) +
    columnEmbedding 3 3 1
      (closedMultiDerivative (shiftedClosedJet (field.toCore.1 cell) (fun _ : Fin 1 => 1)) index point) +
    columnEmbedding 3 3 2 ((L : ℂ)⁻¹ •
      ((Complex.I * (cell : ℂ)) • closedMultiDerivative (field.toCore.1 cell) index point +
        (epsilon : ℂ) • physicalRotation
          (referenceStateMultiDerivative cell index point +
            closedMultiDerivative (field.toCore.1 cell) index point)))

/-- The prescribed normalized harmonic seed, as an actual complex-linear
operator on the complexified real physical plane. -/
def harmonicSeedOperator (rho alpha delta parameter coordinate : ℝ) : OperatorValue 2 2 :=
  matrixEmbedding 2 2 (WithLp.toLp 2 fun index =>
    (Grad.GeometryClosure.harmonicSeedMatrix rho alpha delta parameter coordinate
      (finProdFinEquiv.symm index).2 (finProdFinEquiv.symm index).1 : ℂ))

/-- Original-width Fourier coefficient of the actual seed difference `M-I`.
This is not a freely supplied sequence. -/
def seedDeviationCell (rho alpha delta parameter : ℝ) (cell : ℤ) : OperatorValue 2 2 :=
  ((2 * Real.pi : ℝ)⁻¹ : ℂ) •
    ∫ coordinate in (0 : ℝ)..2 * Real.pi,
      Complex.exp (-Complex.I * (cell : ℂ) * coordinate) •
        (harmonicSeedOperator rho alpha delta parameter coordinate -
          ContinuousLinearMap.id ℂ (ComplexEuclidean 2))

/-- The exact cell derivative multiplier, including the zero cell. -/
def scaledSeedDerivativeCell (L ell rho alpha delta parameter : ℝ) (cell : ℤ) : OperatorValue 2 2 :=
  ((ell / L : ℝ) : ℂ) • (Complex.I * (cell : ℂ)) •
    seedDeviationCell rho alpha delta parameter cell

/-- Literal AP20 size of the original physical displacement and parameters. -/
def stateBudget {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 3 grade) (rho epsilon : ℝ) : ℝ :=
  ‖field‖ + |rho| + |epsilon|

/-- Actual AP21 outputs. Every coefficient value is tied to the prescribed
state/seed formula; no frame or seed coefficient hypothesis is supplied. -/
structure ActualFrameCoefficients {grade : ℕ} (parameters : PhaseParameters)
    (L ell rho alpha delta parameter epsilon : ℝ)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : GradeCore parameters 3 (grade + 4)) where
  frameDeviation : Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3
  seedDeviation : Coefficient L parameters.sigma0 parameters.gamma ell grade 2 2
  seedDerivative : Coefficient L parameters.sigma0 parameters.gamma ell grade 2 2
  frame_value : ∀ (cell : ℤ) (point : ClosedDisk),
    coefficientDerivative frameDeviation cell (zeroDerivativeIndexAt grade) point =
      frameDeviationCell parameters L epsilon field cell
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point)
  frame_derivative : ∀ (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
    coefficientDerivative frameDeviation cell index point =
      (ell ^ derivativeOrder index : ℂ) •
        frameDeviationMultiDerivative parameters L epsilon field cell (derivativeMultiIndex index)
          (physicalScaledPoint ell admissible.2.2.2.1.le
            (admissible.2.2.2.2.trans (min_le_left _ _)) point)
  seed_derivative : ∀ (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
    coefficientDerivative seedDeviation cell index point =
      if derivativeOrder index = 0 then seedDeviationCell rho alpha delta parameter cell else 0
  seed_cell_derivative : ∀ (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
    coefficientDerivative seedDerivative cell index point =
      if derivativeOrder index = 0 then scaledSeedDerivativeCell L ell rho alpha delta parameter cell else 0
  seed_fourier : ∀ coordinate : ℝ,
    (∑' cell : ℤ, cellExponential cell coordinate • seedDeviationCell rho alpha delta parameter cell) =
      harmonicSeedOperator rho alpha delta parameter coordinate -
        ContinuousLinearMap.id ℂ (ComplexEuclidean 2)
  seed_derivative_fourier : ∀ coordinate : ℝ,
    (∑' cell : ℤ, cellExponential cell coordinate •
      scaledSeedDerivativeCell L ell rho alpha delta parameter cell) =
        ((ell / L : ℝ) : ℂ) • deriv (harmonicSeedOperator rho alpha delta parameter) coordinate

/-- Exact AP20–AP21 statement on one fixed compact seed parameter patch. The
constant is independent of `ell`, the original state, and `rho,epsilon`.
The state is never replaced by an assumed coefficient frame. -/
def ActualFrameGoal : Prop :=
  ∀ (parameters : PhaseParameters) (L patchRadius : ℝ), 0 < L → 0 ≤ patchRadius →
    ∀ grade : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |rho| ≤ 1 → |alpha| ≤ patchRadius → |delta| ≤ patchRadius →
          |parameter| ≤ patchRadius → |epsilon| ≤ 1 →
        ∀ field : GradeCore parameters 3 (grade + 4), GradeCoreReality parameters field →
          ∃ coefficients : ActualFrameCoefficients parameters L ell rho alpha delta parameter epsilon
              admissible field,
            ‖coefficients.frameDeviation‖ + ‖coefficients.seedDeviation‖ +
              ‖coefficients.seedDerivative‖ ≤ constant * stateBudget parameters field rho epsilon

end Grad.GaugeCoefficients.Physical.Frame
