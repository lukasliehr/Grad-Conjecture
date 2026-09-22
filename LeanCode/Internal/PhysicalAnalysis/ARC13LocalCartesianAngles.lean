import ARC12LocalFourierRows

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

theorem localCartesian_angular_bound {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (fieldSmooth : ContDiff ℝ ∞ field)
    (cutoff : ℝ × ℝ → ℝ) (cutoffSmooth : ContDiff ℝ ∞ cutoff)
    (polar : ℝ × ℝ → ComplexEuclidean dimension) (polarSmooth : ContDiffOn ℝ ∞ polar openHalfCollar)
    (modes : Finset ℤ)
    (rows : (order : ℕ) → CartesianWord order → ℤ → ℝ → ComplexEuclidean dimension)
    (grade : ℕ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (cutoffBounds : ∀ order, order ≤ grade → ∀ point ∈ halfCollarRectangle,
      ‖iteratedFDeriv ℝ order cutoff point‖ ≤ bound)
    (time : ℝ) (timeIn : time ∈ Ioo (0 : ℝ) (1 / 2))
    (representation : ∀ angle, (field ∘ collarPlane) =ᶠ[𝓝 (time, angle)]
      (fun point => cutoff point • polar point))
    (expansion : ∀ order, order ≤ grade → ∀ angle word,
      iteratedFDeriv ℝ order polar (time, angle) (fun position => productBasis (word position)) =
        ∑ mode ∈ modes, fourier mode (angle : CellCircle) • rows order word mode time) :
    (∫ angle in -Real.pi..Real.pi, ‖iteratedFDeriv ℝ grade field (collarPlane (time, angle))‖ ^ 2) ≤
      (halfReverseConstant grade * cutoffDensityConstant bound grade) * mixedRowsDensity modes rows grade time := by
  have sourceContinuous : Continuous (fun angle : ℝ =>
      ‖iteratedFDeriv ℝ grade field (collarPlane (time, angle))‖ ^ 2) :=
    ((((fieldSmooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (grade : ℕ∞) ≤ ⊤))).comp collarPlane_smooth.continuous).comp
      (continuous_const.prodMk continuous_id)).norm).pow 2
  have densityContinuous : Continuous (fun angle => polarJetSquaredDensity polar grade (time, angle)) := by
    apply continuous_finsetSum
    intro order _
    exact (localPolarTensor_continuous_angle polar polarSmooth order time timeIn).norm.pow 2
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (neg_le_self Real.pi_pos.le)
    (sourceContinuous.intervalIntegrable _ _)
    ((continuous_const.mul densityContinuous).intervalIntegrable _ _) (by
      intro angle angleIn
      have reverse := reverseCollar_derivative_sq_bound field fieldSmooth grade grade le_rfl
        (time, angle) ⟨timeIn.1.le, timeIn.2.le⟩
      have equality : polarJetSquaredDensity (field ∘ collarPlane) grade (time, angle) =
          polarJetSquaredDensity (fun point => cutoff point • polar point) grade (time, angle) := by
        apply Finset.sum_congr rfl
        intro order _
        rw [((representation angle).iteratedFDeriv (𝕜 := ℝ) order).eq_of_nhds]
      rw [equality] at reverse
      have product := cutoff_density_bound_on cutoff openHalfCollar openHalfCollar_open
        cutoffSmooth.contDiffOn polar polarSmooth grade bound boundNonnegative (time, angle)
        ⟨timeIn, mem_univ _⟩ (fun order upper => cutoffBounds order upper (time, angle)
          ⟨⟨timeIn.1.le, timeIn.2.le⟩, angleIn⟩)
      exact reverse.trans ((mul_le_mul_of_nonneg_left product (halfReverseConstant_nonnegative grade)).trans_eq
        (by change _ = (halfReverseConstant grade * cutoffDensityConstant bound grade) * _; ring)))
  simp only [Pi.mul_apply] at comparison
  rw [intervalIntegral.integral_const_mul] at comparison
  exact comparison.trans (mul_le_mul_of_nonneg_left
    (localPolarDensity_angular_bound polar polarSmooth modes rows grade time timeIn expansion)
    (mul_nonneg (halfReverseConstant_nonnegative grade) (cutoffDensityConstant_nonnegative bound grade)))

end Grad.CollarCartesian
