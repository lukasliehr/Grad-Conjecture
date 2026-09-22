import AngularProjectionMaps
import OrthogonalGradeBound

noncomputable section

open Set MeasureTheory
open scoped BigOperators Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Radial

theorem angular_grade_coordinate_bound {dimension grade : ℕ}
    (parameters : PhaseParameters) (cell mode : ℤ) (field : ClosedJet dimension)
    (index : GradeMultiIndex grade) :
    ‖cellGradeRowLinear parameters cell (angularClosedJet mode field) index‖ ≤
      (2 : ℝ) ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  let word := cartesianMultiIndexWord index.toCartesian
  let scalar : ℂ := (cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian)
  let family : ℝ → C(ClosedDisk, ComplexEuclidean dimension) := fun angle =>
    scalar • angularDerivativeFamily mode (phaseWeightedJet parameters cell field) word angle
  have familyContinuous : Continuous family :=
    (continuous_const (y := scalar)).smul
      (angularDerivativeFamily_continuous mode (phaseWeightedJet parameters cell field) word)
  have familyBound (angle : ℝ) (_angleIn : angle ∈ Icc (0 : ℝ) (2 * Real.pi)) :
      ‖closedContinuousToDiskL2 (family angle)‖ ≤
        (2 : ℝ) ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
    change ‖closedContinuousToDiskL2 (scalar •
      (angularCharacter mode angle • orthogonalDerivative (planeRotationEquiv angle)
        (phaseWeightedJet parameters cell field) _ word))‖ ≤ _
    rw [closedContinuousToDiskL2_smul, closedContinuousToDiskL2_smul,
      norm_smul, norm_smul, angularCharacter_norm, one_mul]
    have rotationBound := weighted_orthogonal_word_norm_le
      (order := cartesianOrder index.toCartesian) parameters cell
      (planeRotationEquiv angle) field index.property word
    rw [← orthogonalJet_phaseWeighted, orthogonalJet_derivative] at rotationBound
    simpa only [scalar, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (cellFrequency_pos cell)] using rotationBound
  have integralBound := closedValueL2_normalized_integral_norm_le familyContinuous familyBound
  rw [cellGradeRowLinear_apply, ← angularClosedJet_phaseWeighted]
  change ‖scalar • closedContinuousToDiskL2
    (closedDerivative (angularClosedJet mode (phaseWeightedJet parameters cell field)) _ word)‖ ≤ _
  rw [← closedContinuousToDiskL2_smul, angularClosedJet_derivative_continuousMap]
  have equality : scalar • (((2 * Real.pi)⁻¹ : ℝ) •
        ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
          angularDerivativeFamily mode (phaseWeightedJet parameters cell field) word angle) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in Icc (0 : ℝ) (2 * Real.pi), family angle := by
    rw [smul_comm scalar ((2 * Real.pi)⁻¹ : ℝ), ← integral_smul]
  rw [equality]
  exact integralBound

theorem angular_grade_row_bound {dimension grade : ℕ}
    (parameters : PhaseParameters) (cell mode : ℤ) (field : ClosedJet dimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell (angularClosedJet mode field)‖ ≤
      orthogonalGradeConstant grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  let row := cellGradeRowLinear (grade := grade) parameters cell (angularClosedJet mode field)
  let bound := (2 : ℝ) ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖
  have squareBound : ‖row‖ ^ 2 ≤ (Fintype.card (GradeMultiIndex grade) : ℝ) * bound ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _index : GradeMultiIndex grade, bound ^ 2 := by
        apply Finset.sum_le_sum
        intro index _
        exact pow_le_pow_left₀ (norm_nonneg (row index))
          (angular_grade_coordinate_bound parameters cell mode field index) 2
      _ = _ := by simp
  have rootSquare := Real.sq_sqrt
    (show (0 : ℝ) ≤ Fintype.card (GradeMultiIndex grade) by positivity)
  have rootNonnegative := Real.sqrt_nonneg (Fintype.card (GradeMultiIndex grade) : ℝ)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (orthogonalGradeConstant_nonnegative grade)
    (norm_nonneg _))).mp
  unfold orthogonalGradeConstant
  dsimp [row, bound] at squareBound
  nlinarith [squareBound]

end Grad.Constraints
