import SCS15OriginalSourceCoefficients

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.BoundaryTrace Grad.SourceCollarBulk Grad.AxisCore Grad.GaugeCoefficients.Physical.Allocation

theorem dividedSourceRows_original {grade power : ℕ}
    (parameters : PhaseParameters) (L : ℝ) (paid : power + 3 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (source : ZAmbient parameters grade)
    (planarFlat : OriginalValueFlat parameters (by omega) (originalSourcePlanar parameters grade source))
    (fourthFlat : OriginalValueFlat parameters (by omega) (source 3)) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
      ∀ (component : Fin 3) (mode : ℤ × ℤ),
        originalRowCoefficient parameters power lower
          (dividedSourceRows lower positive bounded parameters L paid source component) radius mode =
        angularCoefficient (originalDividedSourceCells parameters L (by omega) source mode.2 radius
          (positive.le.trans inside.1) inside.2 component) mode.1 := by
  have compatible := ae_all_iff.mpr (fun component : Fin 3 =>
    originalRow_compatible parameters power lower positive _ _
      (dividedSourceRows_compatible lower positive bounded parameters L paid source component))
  filter_upwards [compatible, dividedSourceRows_original_zero parameters L (by omega)
    lower positive bounded source planarFlat fourthFlat] with radius compatible literal
  intro inside component mode
  exact (compatible component mode).trans (literal inside component mode)

theorem coefficientSourceProduct_actual_convolution {grade power : ℕ}
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (paid : power + 3 ≤ grade) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : ZAmbient parameters grade)
    (planarFlat : OriginalValueFlat parameters (by omega) (originalSourcePlanar parameters grade source))
    (fourthFlat : OriginalValueFlat parameters (by omega) (source 3)) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
      ∀ (component : Fin 3) (mode : ℤ × ℤ),
      HasSum (fun shift : ℤ × ℤ => kappaScalar parameters L rho epsilon field small component 0 radius shift •
        angularCoefficient (originalDividedSourceCells parameters L (by omega) source (mode - shift).2 radius
          (positive.le.trans inside.1) inside.2 component) (mode - shift).1)
        (originalRowCoefficient parameters power lower
          (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source component) radius mode) := by
  have products := ae_all_iff.mpr (fun component : Fin 3 =>
    coefficientSourceProduct_literal parameters L rho epsilon field small lower positive bounded paid source component)
  filter_upwards [products, dividedSourceRows_original_zero parameters L (by omega)
    lower positive bounded source planarFlat fourthFlat] with radius products literal
  intro inside component mode
  exact (products component mode).congr_fun (fun shift => by rw [literal inside component (mode - shift)])

end Grad.SourceCollarFullSource
