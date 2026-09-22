import BL14ModeCharacter

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

local instance liftParsevalPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem finiteFourier_coefficient {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (frequency : ℤ) :
    fourierCoeff (fun angle : CellCircle => ∑ mode ∈ modes, fourier mode angle • values mode) frequency =
      if frequency ∈ modes then values frequency else 0 := by
  classical
  have integrable (mode : ℤ) : Integrable (fun angle : CellCircle => fourier mode angle • values mode)
      AddCircle.haarAddCircle :=
    (integrable_const (values mode)).fourier_smul mode
  have equality := congrFun (fourierCoeff.sum modes
    (fun mode (angle : CellCircle) => fourier mode angle • values mode) (fun mode _ => integrable mode)) frequency
  have expression : (∑ mode ∈ modes, fun angle : CellCircle => fourier mode angle • values mode) =
      fun angle => ∑ mode ∈ modes, fourier mode angle • values mode := by
    funext angle
    simp only [Finset.sum_apply]
  rw [expression] at equality
  simpa only [Finset.sum_apply, fourierCoeff_scalar_smul_const, fourierCoeff_fourier,
    Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq] using equality

theorem finiteFourier_integral_norm_sq {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) :
    (∫ angle in -Real.pi..Real.pi,
      ‖∑ mode ∈ modes, fourier mode (angle : CellCircle) • values mode‖ ^ 2) =
        (2 * Real.pi) * ∑ mode ∈ modes, ‖values mode‖ ^ 2 := by
  let field : CellCircle → ComplexEuclidean dimension :=
    fun angle => ∑ mode ∈ modes, fourier mode angle • values mode
  have fieldContinuous : Continuous field := by
    apply continuous_finsetSum
    intro mode _
    exact (fourier mode).continuous.smul continuous_const
  have coefficient : ∀ frequency : ℤ,
      angularCoefficient (fun angle : ℝ => field angle) frequency =
        if frequency ∈ modes then values frequency else 0 := by
    intro frequency
    rw [angularCoefficient_circle]
    exact finiteFourier_coefficient modes values frequency
  have sum := angular_hasSum_sq (fun angle : ℝ => field angle)
    (fieldContinuous.comp (AddCircle.continuous_mk' _))
  have identity := sum.tsum_eq
  rw [tsum_eq_sum (s := modes) (fun frequency notIn => by rw [coefficient frequency, if_neg notIn, norm_zero, zero_pow (by norm_num)])] at identity
  have finiteIdentity : (∑ frequency ∈ modes,
      ‖angularCoefficient (fun angle : ℝ => field angle) frequency‖ ^ 2) =
        ∑ frequency ∈ modes, ‖values frequency‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro frequency member
    rw [coefficient frequency, if_pos member]
  rw [finiteIdentity] at identity
  have periodNonzero : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  change (∫ angle in -Real.pi..Real.pi, ‖field angle‖ ^ 2) = _
  calc
    _ = (2 * Real.pi) * ((2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, ‖field angle‖ ^ 2) := by
      rw [← mul_assoc, mul_inv_cancel₀ periodNonzero, one_mul]
    _ = _ := by rw [← identity]

theorem finitePolarField_word_integral {dimension order : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension)
    (word : CartesianWord order) (time : ℝ) :
    (∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) (time, angle)
          (fun position => productBasis (word position))‖ ^ 2) =
      (2 * Real.pi) * ∑ mode ∈ modes,
        ‖iteratedFDeriv ℝ order (polarModeField parameters (mode, cell) (values mode)) (time, 0)
          (fun position => productBasis (word position))‖ ^ 2 := by
  simp_rw [finitePolarField_word_expansion]
  exact finiteFourier_integral_norm_sq modes _

end Grad.BoundaryLift
