import BKB25RowMultiplicationKernel
import ACP16ForceCoefficientConsumer

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualCurrentPrimitives

def actualForceBoundaryCoefficients (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (component : Fin 3) (mode : ℤ × ℤ) : ℂ :=
  forceScalar parameters L rho epsilon field kind low component 0 1 mode

theorem actualForceBoundaryCoefficients_moments (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (component : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (actualForceBoundaryCoefficients parameters L rho epsilon field kind low component)) :=
  forceScalarMoment_summable parameters L rho epsilon field kind low component
    moment 0 1 zero_le_one le_rfl

/-- The actual AD10 force row, with its circular reference row removed,
as a genuine full two-frequency multiplication kernel. -/
def actualForceBoundaryKernel (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (actualForceBoundaryCoefficients parameters L rho epsilon field kind low)
    (actualForceBoundaryCoefficients_moments parameters L rho epsilon field kind low)

theorem actualForceBoundaryKernel_entry_apply (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (shift input : ℤ × ℤ) (value : ComplexEuclidean 3) :
    (actualForceBoundaryKernel parameters L rho epsilon field kind low).entry
        shift input value =
      (∑ component : Fin 3,
        forceScalar parameters L rho epsilon field kind low component 0 1 shift *
          value component) •
        Grad.GaugeCoefficients.Physical.Ledger.operatorBasis (0 : Fin 1) :=
  boundaryRowMultiplicationKernel_entry_apply parameters 3
    (actualForceBoundaryCoefficients parameters L rho epsilon field kind low)
    (actualForceBoundaryCoefficients_moments parameters L rho epsilon field kind low)
    shift input value

theorem actualForceBoundaryKernel_moment_le (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (moment : ℕ) :
    fullKernelMoment parameters moment
        (actualForceBoundaryKernel parameters L rho epsilon field kind low) ≤
      3 * Real.exp (parameters.sigma0 + parameters.gamma) *
        forceFourierConstant parameters L kind moment 0 *
          physicalBudget parameters field rho epsilon (moment + 6) := by
  apply (boundaryRowMultiplicationKernel_moment_le parameters 3 moment
    (actualForceBoundaryCoefficients parameters L rho epsilon field kind low)
    (actualForceBoundaryCoefficients_moments parameters L rho epsilon field kind low)).trans
  have componentBound (component : Fin 3) :
      (∑' shift, productMoment parameters moment 1
        (actualForceBoundaryCoefficients parameters L rho epsilon field kind low component)
          shift) ≤
        forceFourierConstant parameters L kind moment 0 *
          physicalBudget parameters field rho epsilon (moment + 6) :=
    forceScalarMoment_bound parameters L rho epsilon field kind low component
      moment 0 1 zero_le_one le_rfl
  have summed' :
      (∑ component : Fin 3,
        ∑' shift, productMoment parameters moment 1
          (actualForceBoundaryCoefficients parameters L rho epsilon field kind low component)
            shift) ≤
        3 * (forceFourierConstant parameters L kind moment 0 *
          physicalBudget parameters field rho epsilon (moment + 6)) := by
    rw [Fin.sum_univ_three]
    linarith [componentBound 0, componentBound 1, componentBound 2]
  calc
    Real.exp (parameters.sigma0 + parameters.gamma) *
          ∑ component : Fin 3,
            ∑' shift, productMoment parameters moment 1
              (actualForceBoundaryCoefficients parameters L rho epsilon field kind low component)
                shift
        ≤ Real.exp (parameters.sigma0 + parameters.gamma) *
            (3 * (forceFourierConstant parameters L kind moment 0 *
              physicalBudget parameters field rho epsilon (moment + 6))) :=
          mul_le_mul_of_nonneg_left summed' (Real.exp_pos _).le
    _ = 3 * Real.exp (parameters.sigma0 + parameters.gamma) *
        forceFourierConstant parameters L kind moment 0 *
          physicalBudget parameters field rho epsilon (moment + 6) := by ring

def actualRotatedForceBoundaryCoefficients (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (component : Fin 3) : ℤ × ℤ → ℂ :=
  angularCoefficientSequence
    (actualForceBoundaryCoefficients parameters L rho epsilon field kind low component)

theorem actualRotatedForceBoundaryCoefficients_moments
    (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (component : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment 1
      (actualRotatedForceBoundaryCoefficients parameters L rho epsilon field kind low component)) :=
  (rotatedForceScalarMoment_bound parameters L rho epsilon field kind low component
    moment 0 1 zero_le_one le_rfl).1

/-- The R(delta r0) coefficient row is obtained by the genuine Fourier
angular derivative, never supplied as an independent row assumption. -/
def actualRotatedForceBoundaryKernel (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) :
    FullTwoFrequencyKernel parameters 3 1 :=
  boundaryRowMultiplicationKernel parameters 3
    (actualRotatedForceBoundaryCoefficients parameters L rho epsilon field kind low)
    (actualRotatedForceBoundaryCoefficients_moments
      parameters L rho epsilon field kind low)

theorem actualRotatedForceBoundaryKernel_entry_apply
    (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L)
    (shift input : ℤ × ℤ) (value : ComplexEuclidean 3) :
    (actualRotatedForceBoundaryKernel parameters L rho epsilon field kind low).entry
        shift input value =
      (∑ component : Fin 3,
        angularCoefficientSequence
            (forceScalar parameters L rho epsilon field kind low component 0 1)
            shift * value component) •
        Grad.GaugeCoefficients.Physical.Ledger.operatorBasis (0 : Fin 1) :=
  boundaryRowMultiplicationKernel_entry_apply parameters 3
    (actualRotatedForceBoundaryCoefficients parameters L rho epsilon field kind low)
    (actualRotatedForceBoundaryCoefficients_moments
      parameters L rho epsilon field kind low) shift input value

theorem actualRotatedForceBoundaryKernel_moment_le
    (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤
      originalCoefficientLowRadius parameters L) (moment : ℕ) :
    fullKernelMoment parameters moment
        (actualRotatedForceBoundaryKernel parameters L rho epsilon field kind low) ≤
      3 * Real.exp (parameters.sigma0 + parameters.gamma) *
        forceFourierConstant parameters L kind (moment + 1) 0 *
          physicalBudget parameters field rho epsilon (moment + 7) := by
  apply (boundaryRowMultiplicationKernel_moment_le parameters 3 moment
    (actualRotatedForceBoundaryCoefficients parameters L rho epsilon field kind low)
    (actualRotatedForceBoundaryCoefficients_moments
      parameters L rho epsilon field kind low)).trans
  have componentBound (component : Fin 3) :
      (∑' shift, productMoment parameters moment 1
        (actualRotatedForceBoundaryCoefficients parameters L rho epsilon field kind low component)
          shift) ≤
        forceFourierConstant parameters L kind (moment + 1) 0 *
          physicalBudget parameters field rho epsilon (moment + 7) :=
    (rotatedForceScalarMoment_bound parameters L rho epsilon field kind low component
      moment 0 1 zero_le_one le_rfl).2
  have summed' :
      (∑ component : Fin 3,
        ∑' shift, productMoment parameters moment 1
          (actualRotatedForceBoundaryCoefficients parameters L rho epsilon field kind low component)
            shift) ≤
        3 * (forceFourierConstant parameters L kind (moment + 1) 0 *
          physicalBudget parameters field rho epsilon (moment + 7)) := by
    rw [Fin.sum_univ_three]
    linarith [componentBound 0, componentBound 1, componentBound 2]
  calc
    Real.exp (parameters.sigma0 + parameters.gamma) *
          ∑ component : Fin 3,
            ∑' shift, productMoment parameters moment 1
              (actualRotatedForceBoundaryCoefficients parameters L rho epsilon field kind low component)
                shift
        ≤ Real.exp (parameters.sigma0 + parameters.gamma) *
            (3 * (forceFourierConstant parameters L kind (moment + 1) 0 *
              physicalBudget parameters field rho epsilon (moment + 7))) :=
          mul_le_mul_of_nonneg_left summed' (Real.exp_pos _).le
    _ = 3 * Real.exp (parameters.sigma0 + parameters.gamma) *
        forceFourierConstant parameters L kind (moment + 1) 0 *
          physicalBudget parameters field rho epsilon (moment + 7) := by ring

end Grad.BoundaryKernelAction
