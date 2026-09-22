import BesselWeights

noncomputable section

namespace Grad.SobolevBridge

open Grad.PDEBootstrap MeasureTheory FourierTransform

theorem l2_norm_sq_integral (field : FieldL2) :
    ‖field‖ ^ 2 = ∫ frequency, ‖field frequency‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem multiplier_partition_energy {Index : Type*} [Fintype Index]
    (symbols : Index → Spatial → ℂ)
    (bounded : ∀ coordinate, MemLp (symbols coordinate) ⊤ (volume : Measure Spatial))
    (partition : ∀ frequency, ∑ coordinate, ‖symbols coordinate frequency‖ ^ 2 = 1)
    (field : FieldL2) :
    ∑ coordinate, ‖l2Multiplier ((bounded coordinate).toLp (symbols coordinate)) field‖ ^ 2 =
      ‖field‖ ^ 2 := by
  let transformed : FieldL2 := 𝓕 field
  let pieces : Index → FieldL2 := fun coordinate =>
    (bounded coordinate).toLp (symbols coordinate) • transformed
  have piecesAe (coordinate : Index) :
      ∀ᵐ frequency, pieces coordinate frequency = symbols coordinate frequency • transformed frequency := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) ((bounded coordinate).toLp (symbols coordinate)) transformed,
      (bounded coordinate).coeFn_toLp] with frequency action representative
    change (((bounded coordinate).toLp (symbols coordinate) • transformed : FieldL2) frequency) = _
    rw [action, Pi.smul_apply', representative]
  calc
    _ = ∑ coordinate, ‖pieces coordinate‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro coordinate membership
      change ‖(Lp.fourierTransformₗᵢ Spatial CellValues).symm (pieces coordinate)‖ ^ 2 = _
      rw [LinearIsometryEquiv.norm_map]
    _ = ∫ frequency, ∑ coordinate, ‖pieces coordinate frequency‖ ^ 2 := by
      rw [integral_finsetSum _ (fun coordinate _ => (Lp.memLp (pieces coordinate)).integrable_norm_pow (by decide))]
      simp_rw [l2_norm_sq_integral]
    _ = ∫ frequency, ‖transformed frequency‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr piecesAe] with frequency identities
      simp only [identities, norm_smul, mul_pow, ← Finset.sum_mul, partition, one_mul]
    _ = ‖transformed‖ ^ 2 := (l2_norm_sq_integral transformed).symm
    _ = ‖field‖ ^ 2 := by rw [Lp.norm_fourier_eq]

end Grad.SobolevBridge
