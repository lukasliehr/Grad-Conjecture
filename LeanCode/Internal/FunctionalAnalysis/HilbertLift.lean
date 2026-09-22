import FiniteRowMultiplier

noncomputable section

namespace Grad.TensorBootstrap

variable {Scalar Input Output Further Index : Type*} [NontriviallyNormedField Scalar]
  [NormedAddCommGroup Input] [NormedAddCommGroup Output] [NormedAddCommGroup Further]
  [NormedSpace Scalar Input] [NormedSpace Scalar Output] [NormedSpace Scalar Further]
  [Fintype Index]

def hilbertLiftLinear (operator : Input →L[Scalar] Output) :
    PiLp 2 (fun _ : Index => Input) →ₗ[Scalar] PiLp 2 (fun _ : Index => Output) where
  toFun field := WithLp.toLp 2 (fun index => operator (field index))
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact map_add operator (first index) (second index)
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact map_smul operator scalar (field index)

theorem hilbertLiftLinear_norm_le (operator : Input →L[Scalar] Output)
    (field : PiLp 2 (fun _ : Index => Input)) :
    ‖hilbertLiftLinear operator field‖ ≤ ‖operator‖ * ‖field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index membership
  change ‖operator (field index)‖ ^ 2 ≤ ‖operator‖ ^ 2 * ‖field index‖ ^ 2
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (operator.le_opNorm (field index)) 2

def hilbertLift (operator : Input →L[Scalar] Output) :
    PiLp 2 (fun _ : Index => Input) →L[Scalar] PiLp 2 (fun _ : Index => Output) :=
  (hilbertLiftLinear (Index := Index) operator).mkContinuous ‖operator‖ (by
    intro field
    exact hilbertLiftLinear_norm_le operator field)

theorem hilbertLift_apply (operator : Input →L[Scalar] Output)
    (field : PiLp 2 (fun _ : Index => Input)) (index : Index) :
    hilbertLift operator field index = operator (field index) := rfl

theorem hilbertLift_opNorm_le (operator : Input →L[Scalar] Output) :
    ‖hilbertLift (Index := Index) operator‖ ≤ ‖operator‖ :=
  LinearMap.mkContinuous_norm_le (hilbertLiftLinear (Index := Index) operator) (norm_nonneg _)
    (fun field => hilbertLiftLinear_norm_le operator field)

theorem hilbertLift_norm_le (operator : Input →L[Scalar] Output) (bound : ‖operator‖ ≤ 1)
    (field : PiLp 2 (fun _ : Index => Input)) : ‖hilbertLift operator field‖ ≤ ‖field‖ := by
  exact (hilbertLiftLinear_norm_le operator field).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right bound (norm_nonneg field))

theorem hilbertLift_comp (first : Input →L[Scalar] Output) (second : Output →L[Scalar] Further) :
    hilbertLift (Index := Index) (second ∘L first) = hilbertLift second ∘L hilbertLift first := by
  apply ContinuousLinearMap.ext
  intro field
  apply PiLp.ext
  intro index
  rfl

end Grad.TensorBootstrap
