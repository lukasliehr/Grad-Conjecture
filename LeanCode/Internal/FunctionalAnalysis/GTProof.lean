import GTInterface

noncomputable section

open Grad.PDEBootstrap
open Grad.GenericCarriers (Tensor)
open scoped BigOperators

namespace Grad.TensorAction.Generic

universe valueUniverse targetUniverse

variable (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]

theorem covectorAction_norm_sq (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (tensor : Tensor rank Value) : ‖covectorAction Value rank orthogonal tensor‖ ^ 2 = ‖tensor‖ ^ 2 := by
  let := InnerProductSpace.rclikeToReal ℂ Value
  change ‖HilbertMixing.mix (fun input output =>
    TensorCoefficients.tensorCoefficient rank (OrthogonalCoefficients.coefficient orthogonal)
      output input) tensor‖ ^ 2 = ‖tensor‖ ^ 2
  apply HilbertMixing.norm_sq
  intro first second
  exact TensorCoefficients.tensorCoefficient_orthogonality rank
    (OrthogonalCoefficients.coefficient orthogonal)
    (OrthogonalCoefficients.rowOrthogonality orthogonal) first second

theorem covectorAction_norm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (tensor : Tensor rank Value) : ‖covectorAction Value rank orthogonal tensor‖ = ‖tensor‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (covectorAction_norm_sq Value rank orthogonal tensor)

theorem covectorAction_add (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (first second : Tensor rank Value) :
    covectorAction Value rank orthogonal (first + second) =
      covectorAction Value rank orthogonal first + covectorAction Value rank orthogonal second := by
  apply PiLp.ext
  intro output
  change (∑ input, (TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input : ℂ) • (first input + second input)) =
    (∑ input, (TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input : ℂ) • first input) +
    (∑ input, (TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input : ℂ) • second input)
  simp only [smul_add, Finset.sum_add_distrib]

theorem covectorAction_smul (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (scalar : ℂ) (tensor : Tensor rank Value) :
    covectorAction Value rank orthogonal (scalar • tensor) =
      scalar • covectorAction Value rank orthogonal tensor := by
  apply PiLp.ext
  intro output
  change (∑ input, (TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input : ℂ) • (scalar • tensor input)) =
    scalar • (∑ input, (TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient orthogonal) output input : ℂ) • tensor input)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro input _membership
  exact smul_comm _ scalar (tensor input)

theorem covectorAction_refl (rank : ℕ) (tensor : Tensor rank Value) :
    covectorAction Value rank (LinearIsometryEquiv.refl ℝ Spatial) tensor = tensor := by
  have coefficients : OrthogonalCoefficients.coefficient (LinearIsometryEquiv.refl ℝ Spatial) =
      TensorCoefficients.Identity.identityCoefficients := by
    funext input output
    exact Pi.single_apply output (1 : ℝ) input
  apply PiLp.ext
  intro output
  change (∑ input, (TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient (LinearIsometryEquiv.refl ℝ Spatial))
        output input : ℂ) • tensor input) = tensor output
  rw [coefficients]
  simp [TensorCoefficients.Identity.tensorCoefficient_identity, ite_smul]

theorem covectorAction_trans (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial)
    (tensor : Tensor rank Value) :
    covectorAction Value rank (first.trans second) tensor =
      covectorAction Value rank first (covectorAction Value rank second tensor) := by
  have coefficients : OrthogonalCoefficients.coefficient (first.trans second) =
      TensorCoefficients.Composition.productCoefficients
        (OrthogonalCoefficients.coefficient first) (OrthogonalCoefficients.coefficient second) := by
    funext input output
    exact OrthogonalCoefficients.Composition.coefficientComposition first second input output
  apply PiLp.ext
  intro output
  change (∑ input, (TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient (first.trans second)) output input : ℂ) • tensor input) =
    ∑ middleWord, (TensorCoefficients.tensorCoefficient rank
      (OrthogonalCoefficients.coefficient first) output middleWord : ℂ) •
        (∑ input, (TensorCoefficients.tensorCoefficient rank
          (OrthogonalCoefficients.coefficient second) middleWord input : ℂ) • tensor input)
  rw [coefficients]
  simp_rw [TensorCoefficients.Composition.tensorCoefficient_composition, Complex.ofReal_sum,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum, Complex.ofReal_mul, mul_smul]

theorem covectorAction_symm_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (tensor : Tensor rank Value) :
    covectorAction Value rank orthogonal.symm (covectorAction Value rank orthogonal tensor) = tensor := by
  rw [← covectorAction_trans, LinearIsometryEquiv.symm_trans_self]
  exact covectorAction_refl Value rank tensor

theorem covectorAction_apply_symm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (tensor : Tensor rank Value) :
    covectorAction Value rank orthogonal (covectorAction Value rank orthogonal.symm tensor) = tensor := by
  rw [← covectorAction_trans, LinearIsometryEquiv.self_trans_symm]
  exact covectorAction_refl Value rank tensor

def covectorEquivalence (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    Tensor rank Value ≃ₗᵢ[ℂ] Tensor rank Value where
  toFun := covectorAction Value rank orthogonal
  invFun := covectorAction Value rank orthogonal.symm
  map_add' := covectorAction_add Value rank orthogonal
  map_smul' := covectorAction_smul Value rank orthogonal
  norm_map' := covectorAction_norm Value rank orthogonal
  left_inv := covectorAction_symm_apply Value rank orthogonal
  right_inv := covectorAction_apply_symm Value rank orthogonal

theorem covectorEquivalence_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (tensor : Tensor rank Value) :
    covectorEquivalence Value rank orthogonal tensor = covectorAction Value rank orthogonal tensor := rfl

theorem covectorEquivalence_symm_apply (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (tensor : Tensor rank Value) :
    (covectorEquivalence Value rank orthogonal).symm tensor =
      covectorAction Value rank orthogonal.symm tensor := rfl

theorem covectorEquivalence_coordinate (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (tensor : Tensor rank Value) (output : Fin rank → Fin 2) :
    covectorEquivalence Value rank orthogonal tensor output =
      ∑ input : Fin rank → Fin 2, ((∏ position : Fin rank,
        orthogonal (spatialDirection (output position)) (input position)) : ℂ) • tensor input := by
  change (∑ input, (TensorCoefficients.tensorCoefficient rank
    (OrthogonalCoefficients.coefficient orthogonal) output input : ℂ) • tensor input) = _
  simp only [TensorCoefficients.tensorCoefficient, OrthogonalCoefficients.coefficient, Complex.ofReal_prod]

theorem covectorEquivalence_refl (rank : ℕ) :
    covectorEquivalence Value rank (LinearIsometryEquiv.refl ℝ Spatial) =
      LinearIsometryEquiv.refl ℂ (Tensor rank Value) := by
  apply LinearIsometryEquiv.ext
  exact covectorAction_refl Value rank

theorem covectorEquivalence_trans (rank : ℕ) (first second : Spatial ≃ₗᵢ[ℝ] Spatial) :
    covectorEquivalence Value rank (first.trans second) =
      (covectorEquivalence Value rank second).trans (covectorEquivalence Value rank first) := by
  apply LinearIsometryEquiv.ext
  exact covectorAction_trans Value rank first second

theorem covectorEquivalence_symm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    (covectorEquivalence Value rank orthogonal).symm =
      covectorEquivalence Value rank orthogonal.symm := by
  apply LinearIsometryEquiv.ext
  intro tensor
  rfl

theorem covectorAction_zero (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (tensor : Tensor 0 Value) :
    covectorAction Value 0 orthogonal tensor = tensor := by
  apply PiLp.ext
  intro output
  simp [covectorAction, TensorCoefficients.tensorCoefficient, Finset.univ_unique]
  exact congrArg (fun word : Fin 0 → Fin 2 => tensor word) (Subsingleton.elim _ _)

theorem covectorEquivalence_zero (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    covectorEquivalence Value 0 orthogonal = LinearIsometryEquiv.refl ℂ (Tensor 0 Value) := by
  apply LinearIsometryEquiv.ext
  exact covectorAction_zero Value orthogonal

theorem constructor_consumer : ConstructorGoal Value := by
  intro rank orthogonal
  exact ⟨covectorEquivalence Value rank orthogonal,
    covectorEquivalence_coordinate Value rank orthogonal,
    covectorEquivalence_coordinate Value rank orthogonal.symm⟩

theorem block_consumer : BlockGoal Value :=
  ⟨constructor_consumer Value, covectorAction_norm Value, covectorAction_trans Value,
    covectorAction_zero Value⟩

variable {Target : Type targetUniverse} [NormedAddCommGroup Target] [InnerProductSpace ℂ Target]

theorem covectorAction_map (mapping : Value →L[ℂ] Target) (rank : ℕ)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (tensor : Tensor rank Value) (output : Fin rank → Fin 2) :
    mapping (covectorAction Value rank orthogonal tensor output) =
      covectorAction Target rank orthogonal (WithLp.toLp 2 (fun input => mapping (tensor input))) output := by
  change mapping (∑ input, (TensorCoefficients.tensorCoefficient rank
    (OrthogonalCoefficients.coefficient orthogonal) output input : ℂ) • tensor input) = _
  simp only [map_sum, map_smul]
  rfl

end Grad.TensorAction.Generic
