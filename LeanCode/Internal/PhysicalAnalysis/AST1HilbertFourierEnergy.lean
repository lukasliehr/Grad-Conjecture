import AOG3ActualFiniteGlobalConsumer

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace Grad.AngularSobolevTruncation
open Grad.ClosedJets Grad.CartesianState
local instance periodPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

theorem circleContinuous_integrable {V : Type*} [NormedAddCommGroup V]
    {field : CellCircle → V} (continuousField : Continuous field) :
    Integrable field AddCircle.haarAddCircle :=
  continuousField.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem hilbertFourier_smul (field : CellCircle → ℂ) (value : E) (mode : ℤ) :
    fourierCoeff (fun angle => field angle • value) mode = fourierCoeff field mode • value := by
  simp only [fourierCoeff, smul_smul, smul_eq_mul]
  exact integral_smul_const _ _

def hilbertFourierSum (modes : Finset ℤ) (values : ℤ → E) (angle : CellCircle) : E :=
  ∑ mode ∈ modes, fourier mode angle • values mode

omit [CompleteSpace E] in
theorem hilbertFourierSum_continuous (modes : Finset ℤ) (values : ℤ → E) :
    Continuous (hilbertFourierSum modes values) := by
  apply continuous_finsetSum
  intro mode _
  exact (fourier mode).continuous.smul continuous_const

theorem hilbertFourierSum_coefficient (modes : Finset ℤ) (values : ℤ → E) (frequency : ℤ) :
    fourierCoeff (hilbertFourierSum modes values) frequency =
      if frequency ∈ modes then values frequency else 0 := by
  have integrable (mode : ℤ) : Integrable (fun angle : CellCircle => fourier mode angle • values mode)
      AddCircle.haarAddCircle := (integrable_const _).fourier_smul mode
  have equality := congrFun (fourierCoeff.sum modes
    (fun mode (angle : CellCircle) => fourier mode angle • values mode) (fun mode _ => integrable mode)) frequency
  have expression : (∑ mode ∈ modes, fun angle : CellCircle => fourier mode angle • values mode) =
      hilbertFourierSum modes values := by funext angle; simp only [Finset.sum_apply, hilbertFourierSum]
  rw [expression] at equality
  simpa only [Finset.sum_apply, hilbertFourier_smul, fourierCoeff_fourier,
    Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq] using equality

theorem hilbertFourier_inner (mode : ℤ) (value : E) (field : CellCircle → E)
    (integrable : Integrable field AddCircle.haarAddCircle) :
    (∫ angle : CellCircle, inner ℂ (fourier mode angle • value) (field angle) ∂AddCircle.haarAddCircle) =
      inner ℂ value (fourierCoeff field mode) := by
  have integrand (angle : CellCircle) : inner ℂ (fourier mode angle • value) (field angle) =
      inner ℂ value (fourier (-mode) angle • field angle) := by
    rw [inner_smul_left, inner_smul_right, fourier_neg]
  simp_rw [integrand]
  exact integral_inner (integrable.fourier_smul (-mode)) value

theorem hilbertFourierSum_inner (modes : Finset ℤ) (values : ℤ → E) (field : CellCircle → E)
    (continuousField : Continuous field) :
    (∫ angle : CellCircle, inner ℂ (hilbertFourierSum modes values angle) (field angle) ∂AddCircle.haarAddCircle) =
      ∑ mode ∈ modes, inner ℂ (values mode) (fourierCoeff field mode) := by
  simp only [hilbertFourierSum, sum_inner]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun mode _ => hilbertFourier_inner mode (values mode) field
      (circleContinuous_integrable continuousField))
  · intro mode _
    exact circleContinuous_integrable (((fourier mode).continuous.smul continuous_const).inner continuousField)

theorem hilbertFourierSum_energy (modes : Finset ℤ) (values : ℤ → E) :
    (∫ angle : CellCircle, ‖hilbertFourierSum modes values angle‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ mode ∈ modes, ‖values mode‖ ^ 2 := by
  have equality := hilbertFourierSum_inner modes values (hilbertFourierSum modes values)
    (hilbertFourierSum_continuous modes values)
  have coefficients : (∑ mode ∈ modes, inner ℂ (values mode)
      (fourierCoeff (hilbertFourierSum modes values) mode)) =
      ∑ mode ∈ modes, (‖values mode‖ : ℂ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro mode member
    simp [hilbertFourierSum_coefficient, member, inner_self_eq_norm_sq_to_K]
  rw [coefficients] at equality
  have realPart := congrArg Complex.re equality
  have realIntegral : (∫ angle : CellCircle, (inner ℂ (hilbertFourierSum modes values angle)
      (hilbertFourierSum modes values angle)).re ∂AddCircle.haarAddCircle) =
      (∫ angle : CellCircle, inner ℂ (hilbertFourierSum modes values angle)
        (hilbertFourierSum modes values angle) ∂AddCircle.haarAddCircle).re := by
    simpa only [RCLike.re_to_complex] using integral_re (circleContinuous_integrable
      ((hilbertFourierSum_continuous modes values).inner (𝕜 := ℂ) (hilbertFourierSum_continuous modes values)))
  simpa [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re] using realIntegral.trans realPart

end Hilbert
end Grad.AngularSobolevTruncation
