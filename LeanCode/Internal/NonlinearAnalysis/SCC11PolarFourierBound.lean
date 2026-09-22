import SCC9AngularL1
import SCC10PolarCellBounds

noncomputable section
open Set
open scoped BigOperators ContDiff

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarDivision Grad.SourceCollarRestriction

theorem coefficient_angular_moment_finite {input output grade radial angular power : ℕ}
    (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (cell : ℤ) (column : PhysicalValue input)
    (paid : angular + radial + power + 1 ≤ grade)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (modes : Finset ℤ) :
    ∑ mode ∈ modes, coefficientRadialEnvelope parameters cell radius * cellFrequency cell ^ power *
      |(mode : ℝ)| ^ angular *
        ‖radialCoefficientJet (originalPolarValue
          (coefficientColumnJet parameters family coherent cell column)) mode radial radius‖ ≤
      angularL1Constant * (coefficientPolarConstant grade *
        (coefficientCellBudget (family grade) cell * ‖column‖)) := by
  let field := originalPolarValue (coefficientColumnJet parameters family coherent cell column)
  have smooth := radialIter_smooth radial field (originalPolarValue_smooth _)
  have periodic := radialIter_periodic radial field (originalPolarValue_periodic _)
  have pointBound : ∀ order : Fin 2, ∀ angle ∈ Icc (-Real.pi) Real.pi,
      (coefficientRadialEnvelope parameters cell radius * cellFrequency cell ^ power) *
        ‖angularJet (angular + order.val) (radialIter radial field) (radius, angle)‖ ≤
      coefficientPolarConstant grade * (coefficientCellBudget (family grade) cell * ‖column‖) := by
    intro order angle inside
    have estimate := coefficientColumnJet_mixed_bound parameters family coherent cell column
      (by omega : angular + order.val + radial + power ≤ grade)
      (radius, angle) ⟨⟨nonnegative, bounded⟩, inside⟩
    rw [originalEnvelope_polar parameters cell radius angle nonnegative] at estimate
    exact estimate
  have estimate := angular_l1_finite (radialIter radial field) smooth periodic angular radius
    (coefficientRadialEnvelope parameters cell radius * cellFrequency cell ^ power)
    (coefficientPolarConstant grade * (coefficientCellBudget (family grade) cell * ‖column‖))
    (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le (pow_nonneg (cellFrequency_pos cell).le _))
    (mul_nonneg (coefficientPolarConstant_nonnegative _) (mul_nonneg
      (coefficientCellBudget_nonnegative _ _) (norm_nonneg _))) pointBound modes
  apply le_trans (le_of_eq _) estimate
  apply Finset.sum_congr rfl
  intro mode _
  rw [angularCoefficient_angularJet angular (radialIter radial field) smooth periodic radius mode,
    norm_smul, norm_pow, norm_mul, Complex.norm_I, one_mul]
  have castNorm : ‖(mode : ℂ)‖ = |(mode : ℝ)| := by norm_cast
  rw [castNorm]
  dsimp only [radialCoefficientJet, field]
  ring

theorem annularFrequency_power_bound (mode cell : ℤ) (order : ℕ) :
    annularFrequency mode cell ^ order ≤ (4 : ℝ) ^ order *
      (cellFrequency cell ^ order + |(mode : ℝ)| ^ order) := by
  have cellBound : |(cell : ℝ)| ≤ cellFrequency cell := by
    rw [cellFrequency_formula]
    exact (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr (by nlinarith [sq_abs (cell : ℝ)])
  have bound : annularFrequency mode cell ≤ 2 * (cellFrequency cell + |(mode : ℝ)|) := by
    unfold annularFrequency
    linarith [cellFrequency_one_le cell, abs_nonneg (mode : ℝ)]
  calc
    _ ≤ (2 * (cellFrequency cell + |(mode : ℝ)|)) ^ order :=
      pow_le_pow_left₀ (annularFrequency_nonnegative _ _) bound _
    _ = (2 : ℝ) ^ order * (cellFrequency cell + |(mode : ℝ)|) ^ order := mul_pow _ _ _
    _ ≤ (2 : ℝ) ^ order * ((2 : ℝ) ^ order *
        (cellFrequency cell ^ order + |(mode : ℝ)| ^ order)) :=
      mul_le_mul_of_nonneg_left
        (two_term_pow_bound _ _ (cellFrequency_pos cell).le (abs_nonneg _) _) (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

def coefficientFourierConstant (tangential radial : ℕ) : ℝ :=
  (4 : ℝ) ^ tangential * 2 * angularL1Constant * coefficientPolarConstant (tangential + radial + 1)

theorem coefficientFourierConstant_nonnegative (tangential radial : ℕ) :
    0 ≤ coefficientFourierConstant tangential radial :=
  mul_nonneg (mul_nonneg (by positivity) angularL1Constant_nonnegative)
    (coefficientPolarConstant_nonnegative _)

def coefficientPolarFourier {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean output :=
  radialCoefficientJet (originalPolarValue
    (coefficientColumnJet parameters family coherent mode.2 column)) mode.1 radial radius

theorem coefficient_fourier_cell_finite {input output : ℕ}
    (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (tangential radial : ℕ) (cell : ℤ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (modes : Finset ℤ) :
    ∑ mode ∈ modes, coefficientRadialEnvelope parameters cell radius *
      annularFrequency mode cell ^ tangential *
        ‖coefficientPolarFourier parameters family coherent column radial radius (mode, cell)‖ ≤
      coefficientFourierConstant tangential radial *
        (coefficientCellBudget (family (tangential + radial + 1)) cell * ‖column‖) := by
  have low := coefficient_angular_moment_finite (grade := tangential + radial + 1)
    (radial := radial) (angular := 0) (power := tangential)
    parameters family coherent cell column (by omega) radius nonnegative bounded modes
  have high := coefficient_angular_moment_finite (grade := tangential + radial + 1)
    (radial := radial) (angular := tangential) (power := 0)
    parameters family coherent cell column (by omega) radius nonnegative bounded modes
  simp only [pow_zero, mul_one] at low high
  have combined := mul_le_mul_of_nonneg_left (add_le_add low high)
    (by positivity : 0 ≤ (4 : ℝ) ^ tangential)
  calc
    _ ≤ (4 : ℝ) ^ tangential *
        ((∑ mode ∈ modes, coefficientRadialEnvelope parameters cell radius * cellFrequency cell ^ tangential *
          ‖coefficientPolarFourier parameters family coherent column radial radius (mode, cell)‖) +
        ∑ mode ∈ modes, coefficientRadialEnvelope parameters cell radius * |(mode : ℝ)| ^ tangential *
          ‖coefficientPolarFourier parameters family coherent column radial radius (mode, cell)‖) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro mode _
      have bound := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (annularFrequency_power_bound mode cell tangential)
          (coefficientRadialEnvelope_pos parameters cell radius).le) (norm_nonneg
            (coefficientPolarFourier parameters family coherent column radial radius (mode, cell)))
      exact bound.trans_eq (by ring)
    _ ≤ _ := by
      exact combined.trans_eq (by unfold coefficientFourierConstant; ring)

end Grad.SourceCollarCoefficients
