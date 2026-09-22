import SCS16ActualSourceConvolution

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AxisCore Grad.GaugeCoefficients.Physical.Allocation

theorem originalRowCoefficient_project_four_ae {dimension : ℕ} (parameters : PhaseParameters)
    (power : ℕ) (lower : ℝ) (a b c d : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower (meanFreeRow lower (a + b - c - d)) radius mode =
        if mode.1 = 0 then 0 else
          originalRowCoefficient parameters power lower a radius mode +
          originalRowCoefficient parameters power lower b radius mode -
          originalRowCoefficient parameters power lower c radius mode -
          originalRowCoefficient parameters power lower d radius mode := by
  filter_upwards [originalRowCoefficient_meanFree_ae parameters power lower (a + b - c - d),
    originalRowCoefficient_sub_ae parameters power lower (a + b - c) d,
    originalRowCoefficient_sub_ae parameters power lower (a + b) c,
    originalRowCoefficient_add_ae parameters power lower a b] with radius projection first second third
  intro mode
  rw [projection, first, second, third]

theorem fullG3Row_decoded_algebra {grade power : ℕ}
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (paid : power + 3 ≤ grade) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : ZAmbient parameters grade) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower
        (fullG3Row parameters L rho epsilon field small lower positive bounded paid source) radius mode =
      originalRowCoefficient parameters power lower
        (scalarGRow parameters L lower positive bounded paid source) radius mode +
      if mode.1 = 0 then 0 else
        originalRowCoefficient parameters power lower
          (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 0) radius mode +
        originalRowCoefficient parameters power lower
          (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 1) radius mode -
        originalRowCoefficient parameters power lower
          (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 2) radius mode -
        originalRowCoefficient parameters power lower
          (dividedSourceRows lower positive bounded parameters L paid source 1) radius mode := by
  filter_upwards [originalRowCoefficient_add_ae parameters power lower
    (scalarGRow parameters L lower positive bounded paid source)
    (fullCorrectionRow parameters L rho epsilon field small lower positive bounded paid source),
    originalRowCoefficient_project_four_ae parameters power lower
      (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 0)
      (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 1)
      (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source 2)
      (dividedSourceRows lower positive bounded parameters L paid source 1)] with radius add formula
  intro mode
  rw [fullG3Row, add, fullCorrectionRow, formula]

end Grad.SourceCollarFullSource
