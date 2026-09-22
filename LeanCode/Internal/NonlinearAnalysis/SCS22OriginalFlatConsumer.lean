import SCS21IndependentBaseGrade

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.GaugeCoefficients.Physical.Allocation

/-- Immediate original smooth source consumer: the flatness premises needed
by literal division are DERIVED from BS4. All n,m modes and the original
weighted radial L2(r dr) coefficients are retained. -/
theorem originalFlatSource_g3_coefficients
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (order : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters order lower
        (g3ValueRow parameters L rho epsilon field small lower positive bounded (le_refl _)
          (quotientEta parameters (order + 4) source)) radius mode =
        actualG3Coefficient parameters L rho epsilon field small (by omega)
          (quotientEta parameters (order + 4) source) radius (positive.le.trans inside.1) inside.2 mode ∧
      originalRowCoefficient parameters order lower
        (g3AngularRow parameters L rho epsilon field small lower positive bounded (le_refl _)
          (quotientEta parameters (order + 4) source)) radius mode =
        (Complex.I * (mode.1 : ℂ)) • actualG3Coefficient parameters L rho epsilon field small (by omega)
          (quotientEta parameters (order + 4) source) radius (positive.le.trans inside.1) inside.2 mode := by
  obtain ⟨planarFlat, fourthFlat⟩ := originalFlatSource_division_inputs (grade := order + 4) parameters (by omega) source flat
  exact g3Rows_actual_coefficients parameters L rho epsilon field small (le_refl _) lower positive bounded
    (quotientEta parameters (order + 4) source) planarFlat fourthFlat

/-- One high allocation, with the independent original G4 source as the
low factor. The high state norm is B(t+6), never a product of high norms. -/
theorem originalSource_oneHigh (parameters : PhaseParameters) (L rho epsilon : ℝ) (LPositive : 0 < L)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (order : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : SmoothQuotient parameters) :
    fullSourceNorm parameters L rho epsilon field small order lower positive bounded
      (quotientEta parameters (order + 4) source) ≤
      fullSourceHighConstant parameters L order * quotientNorm parameters (order + 4) source +
      fullSourceLowConstant parameters L order * physicalBudget parameters field rho epsilon (order + 6) *
        quotientNorm parameters 4 source := by
  have bound := fullSourceNorm_bound parameters L rho epsilon LPositive field small order lower positive bounded
    (quotientEta parameters (order + 4) source)
  rw [zLowering_core] at bound
  have low := zLowering_norm_le parameters (by norm_num : 3 ≤ 4) (quotientEta parameters 4 source)
  rw [zLowering_core] at low
  have allocated := mul_le_mul_of_nonneg_left low
    (mul_nonneg (fullSourceLowConstant_nonnegative parameters L order)
      (physicalBudget_nonnegative parameters field rho epsilon (order + 6)))
  exact bound.trans (add_le_add (le_refl _) allocated)

theorem originalSource_independentBase (parameters : PhaseParameters) (L rho epsilon : ℝ) (LPositive : 0 < L)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : SmoothQuotient parameters) :
    fullSourceNorm parameters L rho epsilon field small 0 lower positive bounded (quotientEta parameters 4 source) ≤
      fullSourceBaseConstant parameters L * quotientNorm parameters 4 source :=
  fullSourceNorm_base parameters L rho epsilon LPositive field small lower positive bounded (quotientEta parameters 4 source)

end Grad.SourceCollarFullSource
