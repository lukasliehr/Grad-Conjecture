import SeedParameterFamily

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame

/-- Immediate N7 consumer, with one small multiplier bound for each actual
seed deviation, inverse deviation and derivative. -/
theorem actual_seed_small_multipliers (phase : PhaseParameters) (grade : ℕ)
    {eccentricity radius : ℝ} (nonnegative : 0 ≤ eccentricity) (small : eccentricity < 1)
    (radiusNonnegative : 0 ≤ radius) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter : Parameters,
      |parameter 0| ≤ eccentricity → (∀ index : Fin 3, |parameter index.succ| ≤ radius) →
      ∀ kind : Fin 3, ∃ mapping : AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade,
        (∀ field, ‖mapping field‖ ≤ constant * |parameter 0| * ‖field‖) ∧
        (∀ (field : GradeCore phase 2 grade) (output : ℤ),
          HasSum (Multipliers.multiplierRow phase (actualCells kind parameter) field output)
            (Multipliers.completedCoordinates phase (mapping (aGradeEta phase field)) output)) := by
  obtain ⟨seedConstant, seedNonnegative, seedBound⟩ := actualSeedQuantitative phase grade eccentricity radius
    nonnegative small radiusNonnegative
  obtain ⟨multiplierConstant, multiplierNonnegative, multiplierBound⟩ := Multipliers.sameGradeMultiplier grade
    phase.gamma phase.gamma_pos (lt_of_lt_of_le phase.gamma_lt_min (min_le_left _ _))
  refine ⟨multiplierConstant * seedConstant, mul_nonneg multiplierNonnegative seedNonnegative, ?_⟩
  intro parameter rhoBound otherSmall kind
  obtain ⟨summable, totalBound⟩ := seedBound parameter rhoBound otherSmall
  obtain ⟨mapping, normBound, cells⟩ := multiplierBound phase rfl 2 2 (actualCells kind parameter) (summable kind)
  refine ⟨mapping, ?_, cells⟩
  intro field
  have singleBound : Multipliers.envelope phase grade (actualCells kind parameter) ≤
      ∑ index : Fin 3, Multipliers.envelope phase grade (actualCells index parameter) := by
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun index : Fin 3 => Multipliers.envelope phase grade (actualCells index parameter))
    · intro index _
      apply tsum_nonneg
      intro cell
      unfold Multipliers.envelopeTerm
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
        (pow_nonneg (by rw [cellPolynomialWeight_formula]; positivity) _)) (norm_nonneg _)
    · exact Finset.mem_univ kind
  exact (normBound field).trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (singleBound.trans totalBound) multiplierNonnegative)
    (norm_nonneg field)).trans_eq (by ring))

theorem actual_seed_fourier (phase : PhaseParameters) (parameter : Parameters)
    (inside : parameter ∈ parameterDomain) (angle : ℝ) :
    ((∑' cell : ℤ, cellExponential cell angle • actualCells 0 parameter cell) =
      harmonicSeedOperator (parameter 0) (parameter 1) (parameter 2) (parameter 3) angle -
        ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) ∧
    ((∑' cell : ℤ, cellExponential cell angle • actualCells 1 parameter cell) =
      actualInverseOperator parameter angle - ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) ∧
    ((∑' cell : ℤ, cellExponential cell angle • actualCells 2 parameter cell) =
      deriv (harmonicSeedOperator (parameter 0) (parameter 1) (parameter 2) (parameter 3)) angle) := by
  constructor
  · change (∑' cell : ℤ, cellExponential cell angle •
      seedDeviationCell (parameter 0) (parameter 1) (parameter 2) (parameter 3) cell) = _
    exact seedValue_fourier (seedAdmissible phase) (parameter 0) (parameter 1) (parameter 2) (parameter 3) angle
  constructor
  · have reconstruction := inverseDeviation_fourier phase parameter inside angle seedOrigin
    change (∑' cell : ℤ, cellExponential cell angle •
      coefficientDerivative (inverseDeviationCoefficient phase 0 parameter) cell (zeroDerivativeIndexAt 0) seedOrigin) = _ at reconstruction
    simpa only [inverseDeviation_cell phase 0 parameter inside] using reconstruction
  · have reconstruction := seedDerivativeValue_fourier (seedAdmissible phase)
      (parameter 0) (parameter 1) (parameter 2) (parameter 3) angle
    change (∑' cell : ℤ, cellExponential cell angle •
      ((Complex.I * (cell : ℂ)) • seedDeviationCell (parameter 0) (parameter 1) (parameter 2) (parameter 3) cell)) = _
    simpa only [scaledSeedDerivativeCell, div_self one_ne_zero, Complex.ofReal_one, one_smul] using reconstruction

end Grad.Constraints.Seed
