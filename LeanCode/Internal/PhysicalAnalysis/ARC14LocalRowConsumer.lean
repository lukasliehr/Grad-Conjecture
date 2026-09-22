import ARC13LocalCartesianAngles

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

/-- Local collar row estimate. Smoothness and Fourier identities are required only
at strictly interior radii; the actual endpoint derivative rows enter as continuous
amplitudes, and no global smooth radial-profile extension is required. -/
theorem localRows_cartesian_bound {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (fieldSmooth : ContDiff ℝ ∞ field)
    (vanishes : ∀ point, ‖point‖ < (7 / 12 : ℝ) → field point = 0)
    (cutoff : ℝ × ℝ → ℝ) (cutoffSmooth : ContDiff ℝ ∞ cutoff)
    (polar : ℝ × ℝ → ComplexEuclidean dimension) (polarSmooth : ContDiffOn ℝ ∞ polar openHalfCollar)
    (modes : Finset ℤ)
    (rows : (order : ℕ) → CartesianWord order → ℤ → ℝ → ComplexEuclidean dimension)
    (rowsContinuous : ∀ order word mode, ContinuousOn (rows order word mode) (Icc (0 : ℝ) (1 / 2)))
    (index : CartesianMultiIndex) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (cutoffBounds : ∀ order, order ≤ cartesianOrder index → ∀ point ∈ halfCollarRectangle,
      ‖iteratedFDeriv ℝ order cutoff point‖ ≤ bound)
    (representation : ∀ point ∈ openHalfCollar, (field ∘ collarPlane) =ᶠ[𝓝 point]
      (fun point => cutoff point • polar point))
    (expansion : ∀ order, order ≤ cartesianOrder index → ∀ time ∈ Ioo (0 : ℝ) (1 / 2), ∀ angle word,
      iteratedFDeriv ℝ order polar (time, angle) (fun position => productBasis (word position)) =
        ∑ mode ∈ modes, fourier mode (angle : CellCircle) • rows order word mode time) :
    ‖closedDerivativeL2 index (globalClosedJet field fieldSmooth)‖ ^ 2 ≤
      (halfReverseConstant (cartesianOrder index) * cutoffDensityConstant bound (cartesianOrder index)) *
        ∫ time in (0 : ℝ)..(1 / 2 : ℝ), mixedRowsDensity modes rows (cartesianOrder index) time := by
  let grade := cartesianOrder index
  let constant := halfReverseConstant grade * cutoffDensityConstant bound grade
  let density := fun point : ℝ × ℝ => ‖iteratedFDeriv ℝ grade field (collarPlane point)‖ ^ 2
  have densityContinuous : Continuous density :=
    (((fieldSmooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (grade : ℕ∞) ≤ ⊤))).comp collarPlane_smooth.continuous).norm).pow 2
  have angularContinuous : Continuous (fun time : ℝ => ∫ angle in -Real.pi..Real.pi, density (time, angle)) :=
    timeIntegral_continuous _ (densityContinuous.comp continuous_swap)
      (-Real.pi) Real.pi (neg_le_self Real.pi_pos.le)
  have rightContinuous : ContinuousOn (fun time => constant * mixedRowsDensity modes rows grade time)
      (Icc (0 : ℝ) (1 / 2)) :=
    continuousOn_const.mul (mixedRowsDensity_continuousOn modes rows rowsContinuous grade)
  have radialComparison :
      (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ∫ angle in -Real.pi..Real.pi, density (time, angle)) ≤
        ∫ time in (0 : ℝ)..(1 / 2 : ℝ), constant * mixedRowsDensity modes rows grade time := by
    simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc.trans Ioo_ae_eq_Icc.symm)]
    apply integral_mono_ae
    · exact (angularContinuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    · exact (rightContinuous.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time timeIn
      exact localCartesian_angular_bound field fieldSmooth cutoff cutoffSmooth polar polarSmooth modes rows
        grade bound boundNonnegative cutoffBounds time timeIn
        (fun angle => representation (time, angle) ⟨timeIn, mem_univ _⟩)
        (fun order upper => expansion order upper time timeIn)
  rw [halfCollarIntegral_swap density densityContinuous, intervalIntegral.integral_const_mul] at radialComparison
  have tensorContinuous : Continuous (fun point => ‖iteratedFDeriv ℝ grade field point‖ ^ 2) :=
    ((fieldSmooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (grade : ℕ∞) ≤ ⊤))).norm).pow 2
  have diskBound := disk_integral_le_halfCollar _ tensorContinuous (fun _ => sq_nonneg _) (by
    intro point inside
    rw [derivative_zero_inner field vanishes grade point inside, norm_zero, zero_pow (by norm_num)])
  exact (globalClosedDerivative_energy_bound field fieldSmooth index).trans (diskBound.trans radialComparison)

/-- Direct arbitrary-family consumer: one cutoff/Cartesian-row constant works in
all dimensions and on every finite Fourier support, using local polar data only. -/
theorem localRows_cartesian_consumer (cutoff : ℝ × ℝ → ℝ)
    (cutoffSmooth : ContDiff ℝ ∞ cutoff) (index : CartesianMultiIndex) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (dimension : ℕ)
      (field : SpatialPlane → ComplexEuclidean dimension) (fieldSmooth : ContDiff ℝ ∞ field),
      (∀ point, ‖point‖ < (7 / 12 : ℝ) → field point = 0) →
      ∀ (polar : ℝ × ℝ → ComplexEuclidean dimension), ContDiffOn ℝ ∞ polar openHalfCollar →
      ∀ (modes : Finset ℤ)
      (rows : (order : ℕ) → CartesianWord order → ℤ → ℝ → ComplexEuclidean dimension),
      (∀ order word mode, ContinuousOn (rows order word mode) (Icc (0 : ℝ) (1 / 2))) →
      (∀ point ∈ openHalfCollar, (field ∘ collarPlane) =ᶠ[𝓝 point]
        (fun point => cutoff point • polar point)) →
      (∀ order, order ≤ cartesianOrder index → ∀ time ∈ Ioo (0 : ℝ) (1 / 2), ∀ angle word,
        iteratedFDeriv ℝ order polar (time, angle) (fun position => productBasis (word position)) =
          ∑ mode ∈ modes, fourier mode (angle : CellCircle) • rows order word mode time) →
      ‖closedDerivativeL2 index (globalClosedJet field fieldSmooth)‖ ^ 2 ≤
        constant * ∫ time in (0 : ℝ)..(1 / 2 : ℝ), mixedRowsDensity modes rows (cartesianOrder index) time := by
  obtain ⟨bound, boundNonnegative, cutoffBounds⟩ :=
    exists_polarCutoffBound cutoff cutoffSmooth (cartesianOrder index)
  refine ⟨halfReverseConstant (cartesianOrder index) * cutoffDensityConstant bound (cartesianOrder index),
    mul_nonneg (halfReverseConstant_nonnegative _) (cutoffDensityConstant_nonnegative _ _), ?_⟩
  intro dimension field fieldSmooth vanishes polar polarSmooth modes rows rowsContinuous representation expansion
  exact localRows_cartesian_bound field fieldSmooth vanishes cutoff cutoffSmooth polar polarSmooth modes rows
    rowsContinuous index bound boundNonnegative cutoffBounds representation expansion

end Grad.CollarCartesian
