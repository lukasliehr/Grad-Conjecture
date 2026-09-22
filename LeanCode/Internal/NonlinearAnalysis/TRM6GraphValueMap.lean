import TRM5CosSinGraph
import GaugeCoordinateCore

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision Grad.ClosedJets

variable {sourceDimension targetDimension : ℕ}

def radialValueMap (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    RadialL2 sourceDimension lower →L[ℂ] RadialL2 targetDimension lower :=
  mapping.compLpL 2 (volume.restrict (Icc lower 1))

theorem radialValueMap_norm_le (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    ‖radialValueMap lower mapping‖ ≤ ‖mapping‖ :=
  ContinuousLinearMap.norm_compLpL_le mapping

theorem radialPairing_valueMap (lower : ℝ) (positive : 0 < lower)
    (test : ℝ → ℝ) (continuousTest : Continuous test)
    (vector : ComplexEuclidean targetDimension)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : RadialL2 sourceDimension lower) :
    radialPairing lower positive test continuousTest vector (radialValueMap lower mapping field) =
      radialPairing lower positive test continuousTest (mapping.adjoint vector) field := by
  change inner ℂ (radialTestLp lower positive test continuousTest vector)
      (radialValueMap lower mapping field) =
    inner ℂ (radialTestLp lower positive test continuousTest (mapping.adjoint vector)) field
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (radial_test_memLp lower positive test continuousTest vector).coeFn_toLp,
    (radial_test_memLp lower positive test continuousTest (mapping.adjoint vector)).coeFn_toLp,
    mapping.coeFn_compLpL field] with radius targetTest sourceTest mapped
  dsimp only [radialTestLp, radialValueMap]
  rw [targetTest, sourceTest, mapped, inner_smul_left_eq_smul,
    inner_smul_left_eq_smul, mapping.adjoint_inner_left]

theorem HasWeakRadialDerivative.valueMap {lower : ℝ} {positive : 0 < lower}
    {field derivative : RadialL2 sourceDimension lower}
    (weak : HasWeakRadialDerivative lower positive field derivative)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    HasWeakRadialDerivative lower positive (radialValueMap lower mapping field)
      (radialValueMap lower mapping derivative) := by
  intro test vector
  rw [radialPairing_valueMap, radialPairing_valueMap, weak test (mapping.adjoint vector)]

def divisionRowValueMapFun (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : DivisionRow sourceDimension lower) (mode : ℤ × ℤ) :
    RadialL2 targetDimension lower := radialValueMap lower mapping (field mode)

theorem divisionRowValueMapFun_memlp (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : DivisionRow sourceDimension lower) :
    Memℓp (divisionRowValueMapFun lower mapping field) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  exact Summable.of_nonneg_of_le (fun mode => sq_nonneg _)
    (fun mode => by
      have point : ‖radialValueMap lower mapping (field mode)‖ ≤
          ‖mapping‖ * ‖field mode‖ :=
        ((radialValueMap lower mapping).le_opNorm (field mode)).trans
          (mul_le_mul_of_nonneg_right (radialValueMap_norm_le lower mapping) (norm_nonneg _))
      exact (pow_le_pow_left₀ (norm_nonneg _)
        point 2).trans_eq (mul_pow _ _ _))
    ((divisionRow_sq_summable lower field).mul_left (‖mapping‖ ^ 2))

def divisionRowValueMapLinear (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    DivisionRow sourceDimension lower →ₗ[ℂ] DivisionRow targetDimension lower where
  toFun field := ⟨divisionRowValueMapFun lower mapping field,
    divisionRowValueMapFun_memlp lower mapping field⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact map_add (radialValueMap lower mapping) (first mode) (second mode)
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    exact map_smul (radialValueMap lower mapping) scalar (field mode)

theorem divisionRowValueMapLinear_norm_le (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : DivisionRow sourceDimension lower) :
    ‖divisionRowValueMapLinear lower mapping field‖ ≤ ‖mapping‖ * ‖field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [divisionRow_norm_sq_raw, mul_pow, divisionRow_norm_sq_raw]
  have targetSummable := divisionRow_sq_summable lower
    (divisionRowValueMapLinear lower mapping field)
  have sourceSummable := divisionRow_sq_summable lower field
  calc
    ∑' mode : ℤ × ℤ, ‖divisionRowValueMapLinear lower mapping field mode‖ ^ 2
        ≤ ∑' mode : ℤ × ℤ, ‖mapping‖ ^ 2 * ‖field mode‖ ^ 2 :=
      targetSummable.tsum_le_tsum
        (fun mode => by
          have point : ‖radialValueMap lower mapping (field mode)‖ ≤
              ‖mapping‖ * ‖field mode‖ :=
            ((radialValueMap lower mapping).le_opNorm (field mode)).trans
              (mul_le_mul_of_nonneg_right (radialValueMap_norm_le lower mapping) (norm_nonneg _))
          exact (pow_le_pow_left₀ (norm_nonneg _) point 2).trans_eq (mul_pow _ _ _))
        (sourceSummable.mul_left (‖mapping‖ ^ 2))
    _ = ‖mapping‖ ^ 2 * ∑' mode : ℤ × ℤ, ‖field mode‖ ^ 2 := tsum_mul_left

def divisionRowValueMap (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    DivisionRow sourceDimension lower →L[ℂ] DivisionRow targetDimension lower :=
  LinearMap.mkContinuous (divisionRowValueMapLinear lower mapping) ‖mapping‖
    (divisionRowValueMapLinear_norm_le lower mapping)

@[simp] theorem divisionRowValueMap_apply (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : DivisionRow sourceDimension lower) (mode : ℤ × ℤ) :
    divisionRowValueMap lower mapping field mode = radialValueMap lower mapping (field mode) := rfl

def divisionArrayValueMapLinear {radial : ℕ} (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    DivisionJetArray sourceDimension lower radial →ₗ[ℂ]
      DivisionJetArray targetDimension lower radial where
  toFun field := WithLp.toLp 1 (fun index => divisionRowValueMap lower mapping (field index))
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact map_add (divisionRowValueMap lower mapping) (first index) (second index)
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact map_smul (divisionRowValueMap lower mapping) scalar (field index)

theorem divisionArrayValueMapLinear_norm_le {radial : ℕ} (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : DivisionJetArray sourceDimension lower radial) :
    ‖divisionArrayValueMapLinear lower mapping field‖ ≤ ‖mapping‖ * ‖field‖ := by
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  calc
    ∑ index : Fin (radial + 1), ‖divisionArrayValueMapLinear lower mapping field index‖ ≤
        ∑ index : Fin (radial + 1), ‖mapping‖ * ‖field index‖ :=
      Finset.sum_le_sum (fun index _ => divisionRowValueMapLinear_norm_le lower mapping (field index))
    _ = ‖mapping‖ * ∑ index : Fin (radial + 1), ‖field index‖ := by
      rw [Finset.mul_sum]

def divisionArrayValueMap {radial : ℕ} (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    DivisionJetArray sourceDimension lower radial →L[ℂ]
      DivisionJetArray targetDimension lower radial :=
  LinearMap.mkContinuous (divisionArrayValueMapLinear lower mapping) ‖mapping‖
    (divisionArrayValueMapLinear_norm_le lower mapping)

theorem divisionArrayValueMap_mem_graph {radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : annularDerivativeGraph sourceDimension lower positive radial) :
    divisionArrayValueMap lower mapping field.val ∈
      annularDerivativeGraph targetDimension lower positive radial := by
  apply (annularDerivativeGraph_mem_iff lower positive radial _).mpr
  intro index mode
  change HasWeakRadialDerivative lower positive
    (radialValueMap lower mapping (field.val index.castSucc mode))
    (radialValueMap lower mapping (field.val index.succ mode))
  exact HasWeakRadialDerivative.valueMap
    ((annularDerivativeGraph_mem_iff lower positive radial field.val).mp field.property
      index mode) mapping

/-- A constant value operator, applied to every Fourier and weak radial
coordinate of the complete annular graph. -/
def annularGraphValueMap {radial : ℕ} (lower : ℝ) (positive : 0 < lower)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    annularDerivativeGraph sourceDimension lower positive radial →L[ℂ]
      annularDerivativeGraph targetDimension lower positive radial :=
  ((divisionArrayValueMap lower mapping).comp
    (annularDerivativeGraph sourceDimension lower positive radial).subtypeL).codRestrict
      (annularDerivativeGraph targetDimension lower positive radial)
      (divisionArrayValueMap_mem_graph lower positive mapping)

@[simp] theorem annularGraphValueMap_apply {radial : ℕ} (lower : ℝ) (positive : 0 < lower)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : annularDerivativeGraph sourceDimension lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularGraphValueMap lower positive mapping field).val index mode =
      radialValueMap lower mapping (field.val index mode) := rfl

theorem annularGraphValueMap_apply_norm_le {radial : ℕ} (lower : ℝ) (positive : 0 < lower)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : annularDerivativeGraph sourceDimension lower positive radial) :
    ‖annularGraphValueMap lower positive mapping field‖ ≤ ‖mapping‖ * ‖field‖ :=
  divisionArrayValueMapLinear_norm_le lower mapping field.val

theorem annularGraphValueMap_norm_le {radial : ℕ} (lower : ℝ) (positive : 0 < lower)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    ‖annularGraphValueMap (radial := radial) lower positive mapping‖ ≤ ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact annularGraphValueMap_apply_norm_le lower positive mapping

end Grad.SourceCollarAngular
