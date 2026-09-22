import SCC8CellBudgets

noncomputable section
open Set
open scoped BigOperators ContDiff

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarDivision Grad.SourceCollarRestriction

def coefficientPolarConstant (grade : ℕ) : ℝ :=
  1 + ∑ order ∈ Finset.range (grade + 1),
    Real.sqrt (polarOrderConstant order * (Fintype.card (GradeMultiIndex grade) : ℝ))

theorem coefficientPolarConstant_nonnegative (grade : ℕ) : 0 ≤ coefficientPolarConstant grade := by
  unfold coefficientPolarConstant
  positivity

theorem coefficientPolarConstant_dominates {grade order : ℕ} (upper : order ≤ grade) :
    Real.sqrt (polarOrderConstant order * (Fintype.card (GradeMultiIndex grade) : ℝ)) ≤
      coefficientPolarConstant grade := by
  have bound := Finset.single_le_sum
    (f := fun index => Real.sqrt (polarOrderConstant index * (Fintype.card (GradeMultiIndex grade) : ℝ)))
    (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le upper))
  exact bound.trans (by unfold coefficientPolarConstant; linarith)

theorem coefficientColumnJet_polar_sq {input output grade order : ℕ}
    (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (cell : ℤ) (column : PhysicalValue input)
    (upper : order ≤ grade) (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    originalEnvelope parameters.sigma0 parameters.gamma 1 cell (polarPlane point) ^ 2 *
      (cellFrequency cell ^ (2 * (grade - order)) *
        ‖iteratedFDeriv ℝ order
          (originalPolarValue (coefficientColumnJet parameters family coherent cell column)) point‖ ^ 2) ≤
      (polarOrderConstant order * (Fintype.card (GradeMultiIndex grade) : ℝ)) *
        (coefficientCellBudget (family grade) cell * ‖column‖) ^ 2 := by
  have polar := weighted_polar_derivative_sq_le_density (cellFrequency cell) (cellFrequency_one_le cell)
    upper (coefficientColumnJet parameters family coherent cell column) point inside
  have weighted := mul_le_mul_of_nonneg_left polar
    (sq_nonneg (originalEnvelope parameters.sigma0 parameters.gamma 1 cell (polarPlane point)))
  have density := coefficientColumnJet_density_bound parameters family coherent grade cell column
    (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2)
  have densityBound := mul_le_mul_of_nonneg_left density (polarOrderConstant_nonnegative order)
  change polarOrderConstant order *
    (originalEnvelope parameters.sigma0 parameters.gamma 1 cell (polarPlane point) ^ 2 * _) ≤ _ at densityBound
  exact weighted.trans (by simpa only [mul_left_comm, mul_assoc] using densityBound)

theorem coefficientColumnJet_mixed_bound {input output grade radial angular power : ℕ}
    (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (cell : ℤ) (column : PhysicalValue input)
    (paid : angular + radial + power ≤ grade)
    (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    originalEnvelope parameters.sigma0 parameters.gamma 1 cell (polarPlane point) *
      cellFrequency cell ^ power *
        ‖angularJet angular (radialIter radial
          (originalPolarValue (coefficientColumnJet parameters family coherent cell column))) point‖ ≤
      coefficientPolarConstant grade * (coefficientCellBudget (family grade) cell * ‖column‖) := by
  let field := coefficientColumnJet parameters family coherent cell column
  let amplitude := originalEnvelope parameters.sigma0 parameters.gamma 1 cell (polarPlane point)
  let budget := coefficientCellBudget (family grade) cell * ‖column‖
  have amplitudePositive : 0 < amplitude := Real.exp_pos _
  have budgetNonnegative : 0 ≤ budget :=
    mul_nonneg (coefficientCellBudget_nonnegative _ _) (norm_nonneg _)
  have tensorBound := radialAngular_norm_le radial angular (originalPolarValue field)
    (originalPolarValue_smooth field) point
  have frequencyBound : cellFrequency cell ^ (2 * power) ≤
      cellFrequency cell ^ (2 * (grade - (angular + radial))) :=
    pow_le_pow_right₀ (cellFrequency_one_le cell) (by omega)
  have mixed := mul_le_mul frequencyBound
    (pow_le_pow_left₀ (norm_nonneg _) tensorBound 2) (sq_nonneg _)
    (pow_nonneg (cellFrequency_pos cell).le _)
  have squared := (mul_le_mul_of_nonneg_left mixed (sq_nonneg amplitude)).trans
    (coefficientColumnJet_polar_sq parameters family coherent cell column (by omega) point inside)
  have coefficientNonnegative : 0 ≤ polarOrderConstant (angular + radial) *
      (Fintype.card (GradeMultiIndex grade) : ℝ) :=
    mul_nonneg (polarOrderConstant_nonnegative _) (Nat.cast_nonneg _)
  have rooted : amplitude * cellFrequency cell ^ power *
      ‖angularJet angular (radialIter radial (originalPolarValue field)) point‖ ≤
      Real.sqrt (polarOrderConstant (angular + radial) *
        (Fintype.card (GradeMultiIndex grade) : ℝ)) * budget := by
    apply (sq_le_sq₀
      (mul_nonneg (mul_nonneg amplitudePositive.le (pow_nonneg (cellFrequency_pos cell).le _))
        (norm_nonneg _)) (mul_nonneg (Real.sqrt_nonneg _) budgetNonnegative)).mp
    simp only [mul_pow, Real.sq_sqrt coefficientNonnegative]
    rw [show 2 * power = power * 2 by omega, pow_mul] at squared
    simpa only [mul_assoc] using squared
  exact rooted.trans (mul_le_mul_of_nonneg_right
    (coefficientPolarConstant_dominates (by omega)) budgetNonnegative)

def coefficientRadialEnvelope (parameters : PhaseParameters) (cell : ℤ) (radius : ℝ) : ℝ :=
  Real.exp ((parameters.sigma0 - parameters.gamma * radius) * |(cell : ℝ)|)

theorem coefficientRadialEnvelope_pos (parameters : PhaseParameters) (cell : ℤ) (radius : ℝ) :
    0 < coefficientRadialEnvelope parameters cell radius := Real.exp_pos _

theorem originalEnvelope_polar (parameters : PhaseParameters) (cell : ℤ)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) :
    originalEnvelope parameters.sigma0 parameters.gamma 1 cell (polarPlane (radius, angle)) =
      coefficientRadialEnvelope parameters cell radius := by
  simp [originalEnvelope, coefficientRadialEnvelope, polarPlane_norm, abs_of_nonneg nonnegative]

end Grad.SourceCollarCoefficients
