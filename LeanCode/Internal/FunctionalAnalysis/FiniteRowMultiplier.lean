import NegativeResolvent

noncomputable section

namespace Grad.TensorBootstrap

open Grad.PDEBootstrap Grad.SobolevBridge MeasureTheory FourierTransform

abbrev FiniteL2 (Index : Type*) := PiLp 2 (fun _ : Index => FieldL2)

theorem finite_smul_sum_sq {Index : Type*} [Fintype Index]
    (coefficients : Index → ℂ) (values : Index → CellValues)
    (bound : ∑ index, ‖coefficients index‖ ^ 2 ≤ 1) :
    ‖∑ index, coefficients index • values index‖ ^ 2 ≤ ∑ index, ‖values index‖ ^ 2 := by
  have triangle : ‖∑ index, coefficients index • values index‖ ≤
      ∑ index, ‖coefficients index‖ * ‖values index‖ := by
    simpa only [norm_smul] using norm_sum_le Finset.univ (fun index => coefficients index • values index)
  calc
    _ ≤ (∑ index, ‖coefficients index‖ * ‖values index‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) triangle 2
    _ ≤ (∑ index, ‖coefficients index‖ ^ 2) * ∑ index, ‖values index‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ ≤ 1 * ∑ index, ‖values index‖ ^ 2 :=
      mul_le_mul_of_nonneg_right bound (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := one_mul _

def l2Row {Index : Type*} [Fintype Index] (symbols : Index → Spatial → ℂ)
    (bounded : ∀ index, MemLp (symbols index) ⊤ (volume : Measure Spatial)) :
    FiniteL2 Index →L[ℂ] FieldL2 :=
  ∑ index, l2Multiplier ((bounded index).toLp (symbols index)) ∘L
    PiLp.proj 2 (fun _ : Index => FieldL2) index

theorem l2Row_apply {Index : Type*} [Fintype Index] (symbols : Index → Spatial → ℂ)
    (bounded : ∀ index, MemLp (symbols index) ⊤ (volume : Measure Spatial)) (field : FiniteL2 Index) :
    l2Row symbols bounded field = ∑ index, l2Multiplier ((bounded index).toLp (symbols index)) (field index) := by
  simp [l2Row]

theorem l2Row_norm_sq_le {Index : Type*} [Fintype Index] (symbols : Index → Spatial → ℂ)
    (bounded : ∀ index, MemLp (symbols index) ⊤ (volume : Measure Spatial))
    (rowBound : ∀ frequency, ∑ index, ‖symbols index frequency‖ ^ 2 ≤ 1) (field : FiniteL2 Index) :
    ‖l2Row symbols bounded field‖ ^ 2 ≤ ‖field‖ ^ 2 := by
  let transformed : Index → FieldL2 := fun index => 𝓕 (field index)
  let pieces : Index → FieldL2 := fun index => (bounded index).toLp (symbols index) • transformed index
  have piecesAe (index : Index) :
      ∀ᵐ frequency, pieces index frequency = symbols index frequency • transformed index frequency := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) ((bounded index).toLp (symbols index)) (transformed index),
      (bounded index).coeFn_toLp] with frequency action representative
    change (((bounded index).toLp (symbols index) • transformed index : FieldL2) frequency) = _
    rw [action, Pi.smul_apply', representative]
  have rowIdentity : l2Row symbols bounded field =
      (Lp.fourierTransformₗᵢ Spatial CellValues).symm (∑ index, pieces index) := by
    rw [l2Row_apply, map_sum]
    rfl
  have sumAe : (∑ index, pieces index : FieldL2) =ᵐ[volume] fun frequency => ∑ index, pieces index frequency := by
    exact Lp.coeFn_fun_finsetSum Finset.univ pieces
  calc
    _ = ‖∑ index, pieces index‖ ^ 2 := by rw [rowIdentity, LinearIsometryEquiv.norm_map]
    _ = ∫ frequency, ‖(∑ index, pieces index : FieldL2) frequency‖ ^ 2 := l2_norm_sq_integral _
    _ ≤ ∫ frequency, ∑ index, ‖transformed index frequency‖ ^ 2 := by
      apply integral_mono_ae
        ((Lp.memLp (∑ index, pieces index : FieldL2)).integrable_norm_pow (by decide))
        (integrable_finsetSum _ (fun index _ => (Lp.memLp (transformed index)).integrable_norm_pow (by decide)))
      filter_upwards [sumAe, ae_all_iff.mpr piecesAe] with frequency sumEquality pieceEqualities
      rw [sumEquality]
      simp_rw [pieceEqualities]
      exact finite_smul_sum_sq _ _ (rowBound frequency)
    _ = ∑ index, ‖transformed index‖ ^ 2 := by
      rw [integral_finsetSum _ (fun index _ => (Lp.memLp (transformed index)).integrable_norm_pow (by decide))]
      simp_rw [← l2_norm_sq_integral]
    _ = ∑ index, ‖field index‖ ^ 2 := by simp only [transformed, Lp.norm_fourier_eq]
    _ = ‖field‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ field).symm

theorem l2Row_norm_le {Index : Type*} [Fintype Index] (symbols : Index → Spatial → ℂ)
    (bounded : ∀ index, MemLp (symbols index) ⊤ (volume : Measure Spatial))
    (rowBound : ∀ frequency, ∑ index, ‖symbols index frequency‖ ^ 2 ≤ 1) (field : FiniteL2 Index) :
    ‖l2Row symbols bounded field‖ ≤ ‖field‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (l2Row_norm_sq_le symbols bounded rowBound field)

theorem l2Row_opNorm_le {Index : Type*} [Fintype Index] (symbols : Index → Spatial → ℂ)
    (bounded : ∀ index, MemLp (symbols index) ⊤ (volume : Measure Spatial))
    (rowBound : ∀ frequency, ∑ index, ‖symbols index frequency‖ ^ 2 ≤ 1) :
    ‖l2Row symbols bounded‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [one_mul] using l2Row_norm_le symbols bounded rowBound field

theorem l2Row_distribution {Index : Type*} [Fintype Index] (symbols : Index → Spatial → ℂ)
    (bounded : ∀ index, MemLp (symbols index) ⊤ (volume : Measure Spatial))
    (growth : ∀ index, (symbols index).HasTemperateGrowth) (field : FiniteL2 Index) :
    distributionEmbedding (l2Row symbols bounded field) =
      ∑ index, TemperedDistribution.fourierMultiplierCLM CellValues (symbols index)
        (distributionEmbedding (field index)) := by
  rw [l2Row_apply, map_sum]
  simp_rw [l2Multiplier_distribution (growth _) (bounded _)]

end Grad.TensorBootstrap
