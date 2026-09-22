import AST1HilbertFourierEnergy

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace Grad.AngularSobolevTruncation
open Grad.ClosedJets Grad.CartesianState
local instance besselPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem hilbertFourier_projection_pairing (modes : Finset ℤ) (field : CellCircle → E)
    (continuousField : Continuous field) :
    (∫ angle : CellCircle, (inner ℂ (hilbertFourierSum modes (fourierCoeff field) angle) (field angle)).re
      ∂AddCircle.haarAddCircle) = ∑ mode ∈ modes, ‖fourierCoeff field mode‖ ^ 2 := by
  have equality := congrArg Complex.re
    (hilbertFourierSum_inner modes (fourierCoeff field) field continuousField)
  have realIntegral : (∫ angle : CellCircle,
      (inner ℂ (hilbertFourierSum modes (fourierCoeff field) angle) (field angle)).re ∂AddCircle.haarAddCircle) =
      (∫ angle : CellCircle, inner ℂ (hilbertFourierSum modes (fourierCoeff field) angle) (field angle)
        ∂AddCircle.haarAddCircle).re := by
    simpa only [RCLike.re_to_complex] using integral_re (circleContinuous_integrable
      ((hilbertFourierSum_continuous modes (fourierCoeff field)).inner (𝕜 := ℂ) continuousField))
  simpa [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re] using realIntegral.trans equality

/-- Finite Bessel inequality for the genuine Bochner Fourier coefficients
in any complex Hilbert space, with its original Hilbert norm. -/
theorem hilbertFourier_bessel (modes : Finset ℤ) (field : CellCircle → E)
    (continuousField : Continuous field) :
    (∑ mode ∈ modes, ‖fourierCoeff field mode‖ ^ 2) ≤
      ∫ angle : CellCircle, ‖field angle‖ ^ 2 ∂AddCircle.haarAddCircle := by
  let polynomial := hilbertFourierSum modes (fourierCoeff field)
  have polynomialContinuous : Continuous polynomial := hilbertFourierSum_continuous _ _
  have firstIntegrable : Integrable (fun angle : CellCircle => ‖field angle‖ ^ 2) AddCircle.haarAddCircle :=
    circleContinuous_integrable (continuousField.norm.pow 2)
  have secondIntegrable : Integrable (fun angle : CellCircle => ‖polynomial angle‖ ^ 2) AddCircle.haarAddCircle :=
    circleContinuous_integrable (polynomialContinuous.norm.pow 2)
  have pairingIntegrable : Integrable (fun angle : CellCircle =>
      (inner ℂ (polynomial angle) (field angle)).re) AddCircle.haarAddCircle := circleContinuous_integrable
    (Complex.reCLM.continuous.comp (polynomialContinuous.inner (𝕜 := ℂ) continuousField))
  have nonnegative : 0 ≤ ∫ angle : CellCircle, ‖field angle - polynomial angle‖ ^ 2 ∂AddCircle.haarAddCircle :=
    integral_nonneg (fun _ => sq_nonneg _)
  have expansion : (∫ angle : CellCircle, ‖field angle - polynomial angle‖ ^ 2 ∂AddCircle.haarAddCircle) =
      (∫ angle : CellCircle, ‖field angle‖ ^ 2 ∂AddCircle.haarAddCircle) -
        2 * (∑ mode ∈ modes, ‖fourierCoeff field mode‖ ^ 2) +
        ∑ mode ∈ modes, ‖fourierCoeff field mode‖ ^ 2 := by
    have pointwise (angle : CellCircle) : ‖field angle - polynomial angle‖ ^ 2 =
        ‖field angle‖ ^ 2 - 2 * (inner ℂ (polynomial angle) (field angle)).re + ‖polynomial angle‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), inner_re_symm]
      rfl
    simp_rw [pointwise]
    have addition := integral_add (firstIntegrable.sub (pairingIntegrable.const_mul 2)) secondIntegrable
    simp only [Pi.sub_apply] at addition
    rw [addition, integral_sub firstIntegrable (pairingIntegrable.const_mul 2), integral_const_mul]
    change (∫ angle : CellCircle, ‖field angle‖ ^ 2 ∂AddCircle.haarAddCircle) -
      2 * (∫ angle : CellCircle, (inner ℂ (hilbertFourierSum modes (fourierCoeff field) angle)
        (field angle)).re ∂AddCircle.haarAddCircle) +
      (∫ angle : CellCircle, ‖hilbertFourierSum modes (fourierCoeff field) angle‖ ^ 2 ∂AddCircle.haarAddCircle) = _
    rw [hilbertFourier_projection_pairing modes field continuousField, hilbertFourierSum_energy]
  linarith

end Hilbert
end Grad.AngularSobolevTruncation
