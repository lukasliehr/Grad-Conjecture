import QR9SeedReality

noncomputable section

open scoped ComplexConjugate

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra

theorem physicalConjugation_complex_smul (dimension : ℕ) (scalar : ℂ)
    (vector : ComplexEuclidean dimension) :
    cartesianPhysicalConjugation dimension (scalar • vector) =
      conj scalar • cartesianPhysicalConjugation dimension vector := by
  apply PiLp.ext
  intro coordinate
  exact map_mul (starRingEnd ℂ) scalar (vector coordinate)

def operatorConjugate {inputDimension outputDimension : ℕ}
    (mapping : OperatorValue inputDimension outputDimension) :
    OperatorValue inputDimension outputDimension :=
  LinearMap.toContinuousLinearMap
    { toFun := fun vector => cartesianPhysicalConjugation outputDimension
        (mapping (cartesianPhysicalConjugation inputDimension vector))
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro scalar vector
        simp only [physicalConjugation_complex_smul, map_smul, RingHom.id_apply,
          starRingEnd_self_apply] }

theorem operatorConjugate_apply {inputDimension outputDimension : ℕ}
    (mapping : OperatorValue inputDimension outputDimension)
    (vector : ComplexEuclidean inputDimension) :
    operatorConjugate mapping vector = cartesianPhysicalConjugation outputDimension
      (mapping (cartesianPhysicalConjugation inputDimension vector)) := rfl

theorem operatorConjugate_involutive {inputDimension outputDimension : ℕ} :
    Function.Involutive (@operatorConjugate inputDimension outputDimension) := by
  intro mapping
  apply ContinuousLinearMap.ext
  intro vector
  rw [operatorConjugate_apply, operatorConjugate_apply,
    cartesianPhysicalConjugation_involutive, cartesianPhysicalConjugation_involutive]

theorem operatorConjugate_norm_le {inputDimension outputDimension : ℕ}
    (mapping : OperatorValue inputDimension outputDimension) :
    ‖operatorConjugate mapping‖ ≤ ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro vector
  rw [operatorConjugate_apply, (cartesianPhysicalConjugation outputDimension).norm_map]
  simpa only [(cartesianPhysicalConjugation inputDimension).norm_map] using
    mapping.le_opNorm (cartesianPhysicalConjugation inputDimension vector)

def operatorConjugation (inputDimension outputDimension : ℕ) :
    OperatorValue inputDimension outputDimension ≃ₗᵢ[ℝ]
      OperatorValue inputDimension outputDimension where
  toFun := operatorConjugate
  invFun := operatorConjugate
  left_inv := operatorConjugate_involutive
  right_inv := operatorConjugate_involutive
  map_add' first second := by ext vector; simp only [operatorConjugate_apply, add_apply, map_add]
  map_smul' scalar mapping := by
    ext vector
    simp only [operatorConjugate_apply, smul_apply, map_smul, RingHom.id_apply]
  norm_map' mapping := le_antisymm (operatorConjugate_norm_le mapping) (by
    change ‖mapping‖ ≤ ‖operatorConjugate mapping‖
    have bound := operatorConjugate_norm_le (operatorConjugate mapping)
    rw [operatorConjugate_involutive] at bound
    exact bound)

theorem operatorConjugation_complex_smul (inputDimension outputDimension : ℕ)
    (scalar : ℂ) (mapping : OperatorValue inputDimension outputDimension) :
    operatorConjugation inputDimension outputDimension (scalar • mapping) =
      conj scalar • operatorConjugation inputDimension outputDimension mapping := by
  apply ContinuousLinearMap.ext
  intro vector
  exact physicalConjugation_complex_smul outputDimension scalar
    (mapping (cartesianPhysicalConjugation inputDimension vector))

end Grad.CompletedReality
