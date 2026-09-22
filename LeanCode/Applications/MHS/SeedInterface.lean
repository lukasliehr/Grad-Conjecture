import MultiplierConsumer
import GC14SeedDerivativeFourier

noncomputable section

open scoped BigOperators ContDiff Interval Matrix

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Frame
open Grad.GeometryClosure

/-- Coordinates are eccentricity, constant angle, angle amplitude and harmonic shape. -/
abbrev Parameters := Fin 4 → ℝ

def parameterDomain : Set Parameters := {parameter | |parameter 0| < 1}

def actualMatrix (parameter : Parameters) (angle : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  harmonicSeedMatrix (parameter 0) (parameter 1) (parameter 2) (parameter 3) angle

def actualInverse (parameter : Parameters) (angle : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  seedInverse (parameter 0) (seedAngle (parameter 1) (parameter 2) (parameter 3) angle)

def actualInverseOperator (parameter : Parameters) (angle : ℝ) : OperatorValue 2 2 :=
  matrixEmbedding 2 2 (WithLp.toLp 2 (fun index =>
    ((actualInverse parameter angle (finProdFinEquiv.symm index).2
      (finProdFinEquiv.symm index).1 : ℝ) : ℂ)))

/-- The three literal coefficient families: M-I, M⁻¹-I, and M'. -/
def actualCells (kind : Fin 3) (parameter : Parameters) (cell : ℤ) : OperatorValue 2 2 :=
  if kind = 0 then seedDeviationCell (parameter 0) (parameter 1) (parameter 2) (parameter 3) cell
  else if kind = 1 then
    ((2 * Real.pi : ℂ)⁻¹) • ∫ angle in (0 : ℝ)..2 * Real.pi,
      Complex.exp (-Complex.I * (cell : ℂ) * angle) •
        (actualInverseOperator parameter angle - ContinuousLinearMap.id ℂ (ComplexEuclidean 2))
  else (Complex.I * (cell : ℂ)) •
    seedDeviationCell (parameter 0) (parameter 1) (parameter 2) (parameter 3) cell

def AlgebraGoal : Prop :=
  ∀ parameter ∈ parameterDomain, ∀ angle : ℝ,
    ((actualMatrix parameter angle)ᵀ * actualMatrix parameter angle).trace = 2 ∧
    (actualMatrix parameter angle).det = Real.sqrt (1 - parameter 0 ^ 2) ∧
    0 < (actualMatrix parameter angle).det ∧
    actualMatrix parameter angle * actualInverse parameter angle = 1 ∧
    actualInverse parameter angle * actualMatrix parameter angle = 1

def QuantitativeGoal : Prop :=
  ∀ (phase : PhaseParameters) (grade : ℕ) (eccentricity radius : ℝ),
    0 ≤ eccentricity → eccentricity < 1 → 0 ≤ radius →
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter : Parameters,
      |parameter 0| ≤ eccentricity → (∀ index : Fin 3, |parameter index.succ| ≤ radius) →
      (∀ kind : Fin 3, Summable (Multipliers.envelopeTerm phase grade (actualCells kind parameter))) ∧
      (∑ kind : Fin 3, Multipliers.envelope phase grade (actualCells kind parameter)) ≤
        constant * |parameter 0|

/-- The literal c_q Banach carrier, not pointwise differentiability alone. -/
abbrev WeightedSequence := lp (fun _ : ℤ => OperatorValue 2 2) 1

def ParameterGoal : Prop :=
  ∀ (phase : PhaseParameters) (grade : ℕ),
    ∃ families : Fin 3 → Parameters → WeightedSequence,
      (∀ kind parameter, parameter ∈ parameterDomain → ∀ cell : ℤ,
        families kind parameter cell =
          ((Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade : ℝ) : ℂ) •
            actualCells kind parameter cell) ∧
      (∀ kind, ContDiffOn ℝ ∞ (families kind) parameterDomain) ∧
      (∀ compact : Set Parameters, IsCompact compact → compact ⊆ parameterDomain →
        ∀ order : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
          ∀ kind parameter, parameter ∈ compact → ‖iteratedFDeriv ℝ order (families kind) parameter‖ ≤ constant)

def SeedGoal : Prop := AlgebraGoal ∧ QuantitativeGoal ∧ ParameterGoal

end Grad.Constraints.Seed
