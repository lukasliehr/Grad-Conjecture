import SCS17G3DecodedAlgebra

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarCoefficients Grad.BoundaryTrace Grad.SourceCollarBulk Grad.AxisCore
open Grad.GaugeCoefficients.Physical.Allocation

variable {grade : ℕ} (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
  (large : 3 ≤ grade) (source : ZAmbient parameters grade)

def actualSourceProductCoefficient (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (component : Fin 3) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  ∑' shift : ℤ × ℤ, kappaScalar parameters L rho epsilon field small component 0 radius shift •
    angularCoefficient (originalDividedSourceCells parameters L large source (mode - shift).2 radius
      nonnegative bounded component) (mode - shift).1

/-- Literal full-cell BS30 Fourier formula, including the circular term and
the projection AFTER all three actual-cofactor convolutions. -/
def actualG3Coefficient (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  (L : ℂ)⁻¹ • angularCoefficient (fun angle => completedOriginalCell parameters large mode.2 (source 2)
    (polarClosedPoint radius angle nonnegative bounded)) mode.1 +
  if mode.1 = 0 then 0 else
    actualSourceProductCoefficient parameters L rho epsilon field small large source radius nonnegative bounded 0 mode +
    actualSourceProductCoefficient parameters L rho epsilon field small large source radius nonnegative bounded 1 mode -
    actualSourceProductCoefficient parameters L rho epsilon field small large source radius nonnegative bounded 2 mode -
    angularCoefficient (originalDividedSourceCells parameters L large source mode.2 radius nonnegative bounded 1) mode.1

theorem fullG3Row_actual_coefficient {power : ℕ} (paid : power + 3 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (planarFlat : OriginalValueFlat parameters large (originalSourcePlanar parameters grade source))
    (fourthFlat : OriginalValueFlat parameters large (source 3)) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower
        (fullG3Row parameters L rho epsilon field small lower positive bounded paid source) radius mode =
      actualG3Coefficient parameters L rho epsilon field small large source radius
        (positive.le.trans inside.1) inside.2 mode := by
  have scalarLiteral := ae_all_iff.mpr (fun mode : ℤ × ℤ =>
    restrictedRow_original_coefficient (power := power) lower positive bounded parameters (by omega) large (source 2) mode)
  filter_upwards [fullG3Row_decoded_algebra parameters L rho epsilon field small paid lower positive bounded source,
    coefficientSourceProduct_actual_convolution parameters L rho epsilon field small paid lower positive bounded
      source planarFlat fourthFlat,
    dividedSourceRows_original parameters L paid lower positive bounded source planarFlat fourthFlat,
    originalRowCoefficient_smul_ae parameters power lower (L : ℂ)⁻¹
      (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters (by omega) (source 2)),
    scalarLiteral] with radius algebra products divided scalar restricted
  intro inside mode
  rw [algebra]
  have product (component : Fin 3) :
      originalRowCoefficient parameters power lower
        (coefficientSourceProduct parameters L rho epsilon field small lower positive bounded paid source component) radius mode =
      actualSourceProductCoefficient parameters L rho epsilon field small large source radius
        (positive.le.trans inside.1) inside.2 component mode := (products inside component mode).tsum_eq.symm
  unfold actualG3Coefficient
  rw [product 0, product 1, product 2, divided inside 1 mode, scalarGRow, scalar, restricted mode inside]

end Grad.SourceCollarFullSource
