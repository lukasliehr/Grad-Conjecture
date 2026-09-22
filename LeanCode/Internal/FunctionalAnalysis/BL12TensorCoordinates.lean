import BL11ReverseRotation

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
open Grad.DiskExtension.Operator

def planePairEquiv : SpatialPlane ≃L[ℝ] ℝ × ℝ where
  toFun point := (point 0, point 1)
  invFun point := WithLp.toLp 2 ![point.1, point.2]
  left_inv point := by apply PiLp.ext; intro coordinate; fin_cases coordinate <;> rfl
  right_inv point := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have smooth : ContDiff ℝ ∞ (fun point : ℝ × ℝ => WithLp.toLp 2 ![point.1, point.2]) := by
      rw [contDiff_piLp]
      intro coordinate
      fin_cases coordinate <;> simp <;> fun_prop
    exact smooth.continuous

def productBasis (coordinate : Fin 2) : ℝ × ℝ := planePairEquiv (spatialBasis coordinate)

theorem productBasis_norm (coordinate : Fin 2) : ‖productBasis coordinate‖ = 1 := by
  fin_cases coordinate
  · change ‖((1, 0) : ℝ × ℝ)‖ = 1
    norm_num [Prod.norm_def]
  · change ‖((0, 1) : ℝ × ℝ)‖ = 1
    norm_num [Prod.norm_def]

def productWordCoefficient {order : ℕ} (word : CartesianWord order) :
    (ℝ × ℝ) [×order]→L[ℝ] ℝ :=
  (spatialPlaneWordCoefficient word).compContinuousLinearMap (fun _ => planePairEquiv.symm.toContinuousLinearMap)

theorem productWordCoefficient_basis {order : ℕ} (coefficientWord word : CartesianWord order) :
    productWordCoefficient coefficientWord (fun position => productBasis (word position)) =
      if coefficientWord = word then 1 else 0 := by
  simp only [productWordCoefficient, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    productBasis, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    spatialPlaneWordCoefficient_basis]

theorem continuousMultilinearMap_ext_productBasis {dimension order : ℕ}
    (first second : (ℝ × ℝ) [×order]→L[ℝ] ComplexEuclidean dimension)
    (basisEquality : ∀ word : CartesianWord order,
      first (fun position => productBasis (word position)) =
        second (fun position => productBasis (word position))) : first = second := by
  have pulledEquality : first.compContinuousLinearMap (fun _ => planePairEquiv.toContinuousLinearMap) =
      second.compContinuousLinearMap (fun _ => planePairEquiv.toContinuousLinearMap) := by
    apply continuousMultilinearMap_ext_spatialPlaneBasis
    exact basisEquality
  apply ContinuousMultilinearMap.ext
  intro directions
  have equality := congrArg (fun tensor => tensor (fun position => planePairEquiv.symm (directions position)))
    pulledEquality
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using equality

theorem productTensor_expansion {dimension order : ℕ}
    (tensor : (ℝ × ℝ) [×order]→L[ℝ] ComplexEuclidean dimension) :
    tensor = ∑ word : CartesianWord order,
      (productWordCoefficient word).smulRight (tensor (fun position => productBasis (word position))) := by
  classical
  apply continuousMultilinearMap_ext_productBasis
  intro word
  rw [sum_apply, Finset.sum_eq_single word]
  · rw [ContinuousMultilinearMap.smulRight_apply, productWordCoefficient_basis, if_pos rfl, one_smul]
  · intro other _ otherNe
    rw [ContinuousMultilinearMap.smulRight_apply, productWordCoefficient_basis, if_neg otherNe, zero_smul]
  · simp

def productWordCoefficientSum (order : ℕ) : ℝ :=
  ∑ word : CartesianWord order, ‖productWordCoefficient word‖

theorem productWordCoefficientSum_nonnegative (order : ℕ) : 0 ≤ productWordCoefficientSum order :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem productTensor_norm_bound {dimension order : ℕ}
    (tensor : (ℝ × ℝ) [×order]→L[ℝ] ComplexEuclidean dimension) :
    ‖tensor‖ ≤ ∑ word : CartesianWord order,
      ‖productWordCoefficient word‖ * ‖tensor (fun position => productBasis (word position))‖ := by
  calc
    _ = ‖∑ word : CartesianWord order,
        (productWordCoefficient word).smulRight (tensor (fun position => productBasis (word position)))‖ :=
      congrArg norm (productTensor_expansion tensor)
    _ ≤ _ := by
      apply (norm_sum_le _ _).trans_eq
      simp only [ContinuousMultilinearMap.norm_smulRight]

theorem productTensor_squared_bound {dimension order : ℕ}
    (tensor : (ℝ × ℝ) [×order]→L[ℝ] ComplexEuclidean dimension) :
    ‖tensor‖ ^ 2 ≤ productWordCoefficientSum order *
      ∑ word : CartesianWord order, ‖productWordCoefficient word‖ *
        ‖tensor (fun position => productBasis (word position))‖ ^ 2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (productTensor_norm_bound tensor) 2).trans
  exact weighted_cauchy_finset Finset.univ (fun word : CartesianWord order => ‖productWordCoefficient word‖)
    (fun word => ‖tensor (fun position => productBasis (word position))‖) (fun _ _ => norm_nonneg _)

theorem productTensor_word_bound {dimension order : ℕ}
    (tensor : (ℝ × ℝ) [×order]→L[ℝ] ComplexEuclidean dimension) (word : CartesianWord order) :
    ‖tensor (fun position => productBasis (word position))‖ ≤ ‖tensor‖ := by
  simpa only [productBasis_norm, Finset.prod_const_one, mul_one] using
    tensor.le_opNorm (fun position => productBasis (word position))

end Grad.BoundaryLift
