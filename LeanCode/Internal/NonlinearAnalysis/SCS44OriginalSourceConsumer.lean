import SCS43LiteralG3

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarDivision Grad.QuotientProjection
open Grad.FlatSourceProjection Grad.BoundaryTrace Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Physical.Allocation

theorem doubleCoefficient_component {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field) (coordinate : Fin dimension) (mode : ℤ × ℤ) :
    doubleCoefficient field mode coordinate = doubleCoefficient (fun angles => field angles coordinate) mode := by
  unfold doubleCoefficient
  rw [angularCoefficient_component _ (angularCoefficient_continuous_parameter field continuousField mode.2)]
  congr 1
  funext polar
  exact angularCoefficient_component (fun axial => field (polar, axial))
    (continuousField.comp (continuous_const.prodMk continuous_id)) coordinate mode.2

theorem actualG3Coefficient_literal {grade : ℕ} (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (large : 3 ≤ grade) (source : SmoothQuotient parameters) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    actualG3Coefficient parameters L rho epsilon field small large (quotientEta parameters grade source)
      radius nonnegative bounded mode 0 =
    doubleCoefficient (fun angles => (actualAnnularBulkSource parameters L epsilon field radius
      (by rwa [abs_of_nonneg nonnegative]) angles.2 (spinToCartesian source)).G3 angles.1) mode := by
  rw [actualG3Coefficient_physical parameters L rho epsilon field small source radius nonnegative bounded large,
    doubleCoefficient_component _ (physicalG3_continuous parameters L rho epsilon field small source radius nonnegative bounded)]
  congr 1
  funext angles
  exact physicalG3_literal parameters L rho epsilon field small source radius nonnegative bounded angles.1 angles.2

/-- Immediate literal BS30/AH source consumer. Both stored rows realize the
original physical G3 and its exact im angular derivative on all Fourier cells.
Only the original source flatness is required; division premises are derived. -/
theorem originalFlatSource_physicalConsumer (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (order : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode : ℤ × ℤ,
      let literal := doubleCoefficient (fun angles => (actualAnnularBulkSource parameters L epsilon field radius
        (by rw [abs_of_nonneg (positive.le.trans inside.1)]; exact inside.2) angles.2 (spinToCartesian source)).G3 angles.1) mode
      originalRowCoefficient parameters order lower
        (g3ValueRow parameters L rho epsilon field small lower positive bounded (le_refl _)
          (quotientEta parameters (order + 4) source)) radius mode 0 = literal ∧
      originalRowCoefficient parameters order lower
        (g3AngularRow parameters L rho epsilon field small lower positive bounded (le_refl _)
          (quotientEta parameters (order + 4) source)) radius mode 0 = (Complex.I * (mode.1 : ℂ)) * literal := by
  filter_upwards [originalFlatSource_g3_coefficients parameters L rho epsilon field small order lower positive bounded source flat]
    with radius realized
  intro inside mode
  dsimp only
  have literal := actualG3Coefficient_literal (grade := order + 4) parameters L rho epsilon field small (by omega)
    source radius (positive.le.trans inside.1) inside.2 mode
  constructor
  · exact (congrArg (fun value : ComplexEuclidean 1 => value 0) (realized inside mode).1).trans literal
  · have angular := congrArg (fun value : ComplexEuclidean 1 => value 0) (realized inside mode).2
    simpa only [PiLp.smul_apply, smul_eq_mul, literal] using angular

end Grad.SourceCollarFullSource
