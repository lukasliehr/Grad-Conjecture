import WT1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Function
open scoped ContDiff

namespace Grad.WeakTesting

theorem scalarLift_norm (dimension : ℕ) (cell : ℤ) (vector : Values dimension) :
    ‖scalarLift dimension cell vector‖ = ‖vector‖ := by
  change ‖(ContinuousLinearMap.id ℝ ℝ).smulRight
    (lp.single 2 cell vector : Cells dimension)‖ = ‖vector‖
  rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_id,
    one_mul, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

theorem pairing_integrand_ae (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (membership : MemLp test 2 (volume.restrict domain)) (field : Fields dimension domain) :
    (fun point => inner ℂ
      (((scalarLift dimension cell vector).compLp (membership.toLp test)) point) (field point))
      =ᵐ[volume.restrict domain]
        fun point => test point • inner ℂ vector (field point cell) := by
  filter_upwards [(scalarLift dimension cell vector).coeFn_compLp (membership.toLp test),
    membership.coeFn_toLp] with point lifted scalar
  rw [lifted, scalar]
  change inner ℂ (test point • (lp.single 2 cell vector : Cells dimension)) (field point) =
    test point • inner ℂ vector (field point cell)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (test point)
    (lp.single 2 cell vector : Cells dimension), inner_smul_real_left, lp.inner_single_left]

theorem pairing_integrable (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (membership : MemLp test 2 (volume.restrict domain)) (field : Fields dimension domain) :
    Integrable (fun point => test point • inner ℂ vector (field point cell))
      (volume.restrict domain) :=
  (L2.integrable_inner
    ((scalarLift dimension cell vector).compLp (membership.toLp test)) field).congr
      (pairing_integrand_ae dimension domain cell vector test membership field)

theorem pairingOfMemLp_apply (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (membership : MemLp test 2 (volume.restrict domain)) (field : Fields dimension domain) :
    pairingOfMemLp dimension domain cell vector test membership field =
      ∫ point in domain, test point • inner ℂ vector (field point cell) := by
  rw [pairingOfMemLp, innerSL_apply_apply, L2.inner_def]
  exact integral_congr_ae (pairing_integrand_ae dimension domain cell vector test membership field)

theorem pairingOfMemLp_norm_le (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (membership : MemLp test 2 (volume.restrict domain)) :
    ‖pairingOfMemLp dimension domain cell vector test membership‖ ≤
      (eLpNorm test 2 (volume.restrict domain)).toReal * ‖vector‖ := by
  rw [pairingOfMemLp, innerSL_apply_norm]
  calc
    ‖(scalarLift dimension cell vector).compLp (membership.toLp test)‖ ≤
        ‖scalarLift dimension cell vector‖ * ‖membership.toLp test‖ :=
      (scalarLift dimension cell vector).norm_compLp_le (membership.toLp test)
    _ = (eLpNorm test 2 (volume.restrict domain)).toReal * ‖vector‖ := by
      rw [scalarLift_norm, Lp.norm_toLp, mul_comm]

theorem pairing : PairingGoal := by
  intro dimension domain cell vector test membership
  exact ⟨pairingOfMemLp_apply dimension domain cell vector test membership,
    pairingOfMemLp_norm_le dimension domain cell vector test membership⟩

theorem compactPairing_apply (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (field : Fields dimension domain) :
    compactPairing dimension domain cell vector test smoothness compactSupport field =
      ∫ point in domain, test point • inner ℂ vector (field point cell) :=
  pairingOfMemLp_apply dimension domain cell vector test
    (smoothness.continuous.memLp_of_hasCompactSupport compactSupport) field

theorem compactPairing_norm_le (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test) :
    ‖compactPairing dimension domain cell vector test smoothness compactSupport‖ ≤
      (eLpNorm test 2 (volume.restrict domain)).toReal * ‖vector‖ :=
  pairingOfMemLp_norm_le dimension domain cell vector test
    (smoothness.continuous.memLp_of_hasCompactSupport compactSupport)

theorem orderedTestDerivative_continuous (rank : ℕ) (word : Fin rank → Fin 2)
    (test : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ test) :
    Continuous (orderedTestDerivative rank word test) := by
  change Continuous ((fun tensor : ContinuousMultilinearMap ℝ (fun _ : Fin rank => Spatial) ℝ =>
    tensor (fun position => spatialDirection (word position))) ∘ iteratedFDeriv ℝ rank test)
  exact (continuous_eval_const _).comp
    (ContDiff.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl rank) smoothness)

theorem orderedTestDerivative_hasCompactSupport (rank : ℕ) (word : Fin rank → Fin 2)
    (test : Spatial → ℝ) (compactSupport : HasCompactSupport test) :
    HasCompactSupport (orderedTestDerivative rank word test) :=
  (compactSupport.iteratedFDeriv (𝕜 := ℝ) rank).comp_left
    (g := fun tensor : ContinuousMultilinearMap ℝ (fun _ : Fin rank => Spatial) ℝ =>
      tensor (fun position => spatialDirection (word position))) rfl

theorem orderedTestDerivative_support_subset (rank : ℕ) (word : Fin rank → Fin 2)
    (test : Spatial → ℝ) : tsupport (orderedTestDerivative rank word test) ⊆ tsupport test :=
  (tsupport_comp_subset
    (g := fun tensor : ContinuousMultilinearMap ℝ (fun _ : Fin rank => Spatial) ℝ =>
      tensor (fun position => spatialDirection (word position))) rfl
    (iteratedFDeriv ℝ rank test)).trans (tsupport_iteratedFDeriv_subset rank)

theorem orderedTestDerivative_memLp (domain : Set Spatial) (rank : ℕ) (word : Fin rank → Fin 2)
    (test : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test) :
    MemLp (orderedTestDerivative rank word test) 2 (volume.restrict domain) :=
  (orderedTestDerivative_continuous rank word test smoothness).memLp_of_hasCompactSupport
    (orderedTestDerivative_hasCompactSupport rank word test compactSupport)

theorem derivativeTests : DerivativeTestGoal := by
  intro domain test smoothness compactSupport supported rank word
  exact ⟨orderedTestDerivative_memLp domain rank word test smoothness compactSupport,
    (orderedTestDerivative_support_subset rank word test).trans supported⟩

def orderedDerivativePairing (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (rank : ℕ) (word : Fin rank → Fin 2) : Fields dimension domain →L[ℂ] ℂ :=
  pairingOfMemLp dimension domain cell vector (orderedTestDerivative rank word test)
    (orderedTestDerivative_memLp domain rank word test smoothness compactSupport)

theorem orderedDerivativePairing_apply (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (rank : ℕ) (word : Fin rank → Fin 2) (field : Fields dimension domain) :
    orderedDerivativePairing dimension domain cell vector test smoothness compactSupport rank word
      field = ∫ point in domain,
        orderedTestDerivative rank word test point • inner ℂ vector (field point cell) :=
  pairingOfMemLp_apply dimension domain cell vector (orderedTestDerivative rank word test)
    (orderedTestDerivative_memLp domain rank word test smoothness compactSupport) field

theorem orderedDerivativePairing_norm_le (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (rank : ℕ) (word : Fin rank → Fin 2) :
    ‖orderedDerivativePairing dimension domain cell vector test smoothness compactSupport rank word‖ ≤
      (eLpNorm (orderedTestDerivative rank word test) 2 (volume.restrict domain)).toReal * ‖vector‖ :=
  pairingOfMemLp_norm_le dimension domain cell vector (orderedTestDerivative rank word test)
    (orderedTestDerivative_memLp domain rank word test smoothness compactSupport)

theorem orderedTestDerivative_zero (word : Fin 0 → Fin 2) (test : Spatial → ℝ) :
    orderedTestDerivative 0 word test = test := rfl

theorem orderedDerivativePairing_zero (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (word : Fin 0 → Fin 2) :
    orderedDerivativePairing dimension domain cell vector test smoothness compactSupport 0 word =
      compactPairing dimension domain cell vector test smoothness compactSupport := rfl

end Grad.WeakTesting
