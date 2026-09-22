import TensorAngleRigidityProof

noncomputable section

namespace Grad.MainAssembly.TensorAngleRigidity.Consumer

open Grad.MainAssembly.TensorAngleRigidity
open Matrix

/-- Immediate `NG_R17` consumer: signed normal-frame covariance of the two
literal normalized tensors yields exactly the pi-lattice angle congruence
required by the accepted harmonic block. -/
theorem angle_congruence_of_signed_tensor_covariance
    (rho sourceAngle targetAngle normalSign : ℝ)
    (rhoPositive : 0 < rho)
    (normalSignValue : normalSign = 1 ∨ normalSign = -1)
    (tensorCovariance :
      normalizedShape rho targetAngle =
        normalSignMatrix normalSign * normalizedShape rho sourceAngle *
          (normalSignMatrix normalSign)ᵀ) :
    ∃ integer : ℤ,
      targetAngle - normalSign * sourceAngle = (integer : ℝ) * Real.pi := by
  rw [normalSign_conjugation rho sourceAngle normalSign normalSignValue] at tensorCovariance
  exact (normalizedShape_eq_iff_piLattice rho
    (normalSign * sourceAngle) targetAngle rhoPositive).mp tensorCovariance

end Grad.MainAssembly.TensorAngleRigidity.Consumer
