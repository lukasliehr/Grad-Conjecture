import BKB24ScalarMultiplicationKernel
import GC17MatrixOperators

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Ledger

theorem operatorBasis_norm {dimension : ℕ} (row : Fin dimension) :
    ‖operatorBasis row‖ = 1 := by
  rw [PiLp.norm_eq_of_L2]
  simp only [operatorBasis]
  rw [Finset.sum_eq_single row]
  · simp
  · intro other _ distinct
    simp only [if_neg distinct, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  · simp

theorem matrixUnit_norm_le {input output : ℕ} (row : Fin output)
    (column : Fin input) :
    ‖matrixUnit row column‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  rw [matrixUnit_apply, norm_smul, operatorBasis_norm, mul_one]
  simpa only [one_mul] using PiLp.norm_apply_le value column

def rowMultiplicationEntry (inputDimension : ℕ)
    (coefficient : Fin inputDimension → ℤ × ℤ → ℂ)
    (shift _input : ℤ × ℤ) :
    ComplexEuclidean inputDimension →L[ℂ] ComplexEuclidean 1 :=
  ∑ component : Fin inputDimension,
    coefficient component shift • matrixUnit 0 component

theorem rowMultiplicationEntry_norm_le (inputDimension : ℕ)
    (coefficient : Fin inputDimension → ℤ × ℤ → ℂ)
    (shift input : ℤ × ℤ) :
    ‖rowMultiplicationEntry inputDimension coefficient shift input‖ ≤
      ∑ component : Fin inputDimension, ‖coefficient component shift‖ := by
  unfold rowMultiplicationEntry
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro component _
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (matrixUnit_norm_le (0 : Fin 1) component)
    (norm_nonneg (coefficient component shift))

theorem rowMultiplicationMoment_summable (parameters : PhaseParameters)
    (inputDimension moment : ℕ)
    (coefficient : Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ component order,
      Summable (productMoment parameters order 1 (coefficient component))) :
    Summable (fun shift : ℤ × ℤ =>
      boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ moment *
          ∑ component : Fin inputDimension, ‖coefficient component shift‖) := by
  have componentSummable (component : Fin inputDimension) :
      Summable (fun shift : ℤ × ℤ =>
        boundaryCoefficientPhaseCost parameters shift *
          annularFrequency shift.1 shift.2 ^ moment *
            ‖coefficient component shift‖) := by
    apply ((moments component moment).mul_left
      (Real.exp (parameters.sigma0 + parameters.gamma))).congr
    intro shift
    exact (boundaryCoefficientPhaseCost_productMoment parameters moment
      (coefficient component) shift).symm
  simpa only [Finset.mul_sum] using
    (summable_sum (s := Finset.univ)
      (fun component _ => componentSummable component))

/-- A full vector row of physical Fourier coefficients gives an exact
input-mode-independent AE7 kernel from that vector to a scalar. -/
def boundaryRowMultiplicationKernel (parameters : PhaseParameters)
    (inputDimension : ℕ)
    (coefficient : Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ component moment,
      Summable (productMoment parameters moment 1 (coefficient component))) :
    FullTwoFrequencyKernel parameters inputDimension 1 :=
  fullKernelOfEntries parameters
    (rowMultiplicationEntry inputDimension coefficient)
    (fun shift => ∑ component : Fin inputDimension,
      ‖coefficient component shift‖)
    (rowMultiplicationEntry_norm_le inputDimension coefficient)
    (fun moment => rowMultiplicationMoment_summable parameters inputDimension
      moment coefficient moments)

@[simp] theorem boundaryRowMultiplicationKernel_entry
    (parameters : PhaseParameters) (inputDimension : ℕ)
    (coefficient : Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ component moment,
      Summable (productMoment parameters moment 1 (coefficient component)))
    (shift input : ℤ × ℤ) :
    (boundaryRowMultiplicationKernel parameters inputDimension coefficient moments).entry
        shift input = rowMultiplicationEntry inputDimension coefficient shift input := rfl

theorem boundaryRowMultiplicationKernel_entry_apply
    (parameters : PhaseParameters) (inputDimension : ℕ)
    (coefficient : Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ component moment,
      Summable (productMoment parameters moment 1 (coefficient component)))
    (shift input : ℤ × ℤ) (value : ComplexEuclidean inputDimension) :
    (boundaryRowMultiplicationKernel parameters inputDimension coefficient moments).entry
        shift input value =
      (∑ component : Fin inputDimension,
        coefficient component shift * value component) • operatorBasis (0 : Fin 1) := by
  rw [boundaryRowMultiplicationKernel_entry]
  unfold rowMultiplicationEntry
  rw [sum_apply]
  simp_rw [smul_apply, matrixUnit_apply, smul_smul]
  rw [Finset.sum_smul]

theorem boundaryRowMultiplicationKernel_entryNorm_le
    (parameters : PhaseParameters) (inputDimension : ℕ)
    (coefficient : Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ component moment,
      Summable (productMoment parameters moment 1 (coefficient component)))
    (shift : ℤ × ℤ) :
    (boundaryRowMultiplicationKernel parameters inputDimension coefficient moments).entryNorm
        shift ≤
      ∑ component : Fin inputDimension, ‖coefficient component shift‖ :=
  fullKernelOfEntries_entryNorm_le parameters
    (rowMultiplicationEntry inputDimension coefficient)
    (fun current => ∑ component : Fin inputDimension,
      ‖coefficient component current‖)
    (rowMultiplicationEntry_norm_le inputDimension coefficient)
    (fun moment => rowMultiplicationMoment_summable parameters inputDimension
      moment coefficient moments)
    shift

theorem boundaryRowMultiplicationKernel_moment_le
    (parameters : PhaseParameters) (inputDimension moment : ℕ)
    (coefficient : Fin inputDimension → ℤ × ℤ → ℂ)
    (moments : ∀ component order,
      Summable (productMoment parameters order 1 (coefficient component))) :
    fullKernelMoment parameters moment
        (boundaryRowMultiplicationKernel parameters inputDimension coefficient moments) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ component : Fin inputDimension,
          ∑' shift, productMoment parameters moment 1
            (coefficient component) shift := by
  unfold fullKernelMoment
  have leftSummable :=
    (boundaryRowMultiplicationKernel parameters inputDimension coefficient moments).moments
      moment
  have componentSummable (component : Fin inputDimension) :
      Summable (fun shift : ℤ × ℤ =>
        Real.exp (parameters.sigma0 + parameters.gamma) *
          productMoment parameters moment 1 (coefficient component) shift) :=
    (moments component moment).mul_left _
  have rightSummable : Summable (fun shift : ℤ × ℤ =>
      ∑ component : Fin inputDimension,
        Real.exp (parameters.sigma0 + parameters.gamma) *
          productMoment parameters moment 1 (coefficient component) shift) :=
    summable_sum (s := Finset.univ)
      (fun component _ => componentSummable component)
  calc
    _ ≤ ∑' shift : ℤ × ℤ,
        ∑ component : Fin inputDimension,
          Real.exp (parameters.sigma0 + parameters.gamma) *
            productMoment parameters moment 1
              (coefficient component) shift := by
      apply leftSummable.tsum_le_tsum (fun shift => ?_) rightSummable
      calc
        boundaryCoefficientPhaseCost parameters shift *
              annularFrequency shift.1 shift.2 ^ moment *
                (boundaryRowMultiplicationKernel parameters inputDimension
                  coefficient moments).entryNorm shift
            ≤ boundaryCoefficientPhaseCost parameters shift *
                annularFrequency shift.1 shift.2 ^ moment *
                  ∑ component : Fin inputDimension,
                    ‖coefficient component shift‖ :=
          mul_le_mul_of_nonneg_left
            (boundaryRowMultiplicationKernel_entryNorm_le
              parameters inputDimension coefficient moments shift)
            (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
              (pow_nonneg (annularFrequency_pos shift).le moment))
        _ = ∑ component : Fin inputDimension,
              Real.exp (parameters.sigma0 + parameters.gamma) *
                productMoment parameters moment 1
                  (coefficient component) shift := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro component _
          exact boundaryCoefficientPhaseCost_productMoment parameters moment
            (coefficient component) shift
    _ = Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑ component : Fin inputDimension,
          ∑' shift, productMoment parameters moment 1
            (coefficient component) shift := by
      rw [Summable.tsum_finsetSum
        (fun component _ => componentSummable component)]
      simp only [tsum_mul_left, Finset.mul_sum]

end Grad.BoundaryKernelAction
