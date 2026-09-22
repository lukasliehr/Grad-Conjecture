import ANH3DiskNorm

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Unweighted normalized Fourier coordinates of the actual boundary. -/
abbrev BoundaryFourierL2 := lp (fun _ : ℤ × ℤ => PhysicalValue 1) 2

theorem unweightedBoundaryWeight_one_le (mode : ℤ × ℤ) :
    1 ≤ apBoundaryWeight 1 0 0 1 1 mode := by
  have frequency := apBoundaryFrequency_one_le 1 1 mode
  have root := Real.sqrt_le_sqrt frequency
  simpa [apBoundaryWeight, apBoundaryPhase, Grad.AnalyticWeights.phase] using root

theorem boundaryCoefficient_norm_le (field : APBoundaryGrade 1 0 0 1 1 1)
    (mode : ℤ × ℤ) :
    ‖apBoundaryCoefficient 1 0 0 1 1 field mode‖ ≤ ‖field mode‖ := by
  rw [apBoundaryCoefficient, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (apBoundaryWeight_pos 1 0 0 1 1 mode)]
  exact (mul_le_mul_of_nonneg_right
    (inv_le_one_of_one_le₀ (unweightedBoundaryWeight_one_le mode)) (norm_nonneg _)).trans_eq
      (one_mul _)

def boundaryUnweightLinear : APBoundaryGrade 1 0 0 1 1 1 →ₗ[ℂ] BoundaryFourierL2 where
  toFun field := ⟨apBoundaryCoefficient 1 0 0 1 1 field,
    field.property.mono' (boundaryCoefficient_norm_le field)⟩
  map_add' first second := by
    apply lp.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply lp.ext
    funext mode
    change ((apBoundaryWeight 1 0 0 1 1 mode : ℂ)⁻¹) • (scalar • field mode) =
      scalar • (((apBoundaryWeight 1 0 0 1 1 mode : ℂ)⁻¹) • field mode)
    exact smul_comm _ _ _

def boundaryUnweight : APBoundaryGrade 1 0 0 1 1 1 →L[ℂ] BoundaryFourierL2 :=
  boundaryUnweightLinear.mkContinuous 1 (fun field => by
    rw [one_mul]
    exact lp.norm_mono (by norm_num) (boundaryCoefficient_norm_le field))

def diskBoundaryFourier : diskGrade →L[ℂ] BoundaryFourierL2 :=
  boundaryUnweight.comp diskTrace

theorem diskBoundaryFourier_coefficient (field : ClosedJet 1) (mode : ℤ × ℤ) :
    diskBoundaryFourier (diskCoreInto field) mode =
      apCoreBoundaryCoefficient (Finsupp.single 0 field) mode := by
  change apBoundaryCoefficient 1 0 0 1 1 (diskTrace (diskCoreInto field)) mode = _
  rw [diskTrace_core, apCoreTraceLinear_coefficient]

theorem diskBoundaryFourier_bound (field : diskGrade) :
    ‖diskBoundaryFourier field‖ ≤ Real.sqrt (traceCellConstant 1) * ‖field‖ :=
  (lp.norm_mono (by norm_num) (boundaryCoefficient_norm_le (diskTrace field))).trans
    (diskTrace_bound field)

theorem diskBoundaryFourier_core_zero (field : ClosedJet 1) (mode cell : ℤ)
    (different : cell ≠ 0) :
    diskBoundaryFourier (diskCoreInto field) (mode, cell) = 0 := by
  rw [diskBoundaryFourier_coefficient, apCoreBoundaryCoefficient,
    Finsupp.single_eq_of_ne different]
  simp [fourierCoeff]

theorem diskBoundaryFourier_core_cell (field : ClosedJet 1) (mode : ℤ) :
    diskBoundaryFourier (diskCoreInto field) (mode, 0) =
      fourierCoeff (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode := by
  rw [diskBoundaryFourier_coefficient, apCoreBoundaryCoefficient, Finsupp.single_eq_same]

theorem diskBoundaryFourier_core_norm_sq (field : ClosedJet 1) :
    ‖diskBoundaryFourier (diskCoreInto field)‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi,
        ‖field.value (boundaryDiskPoint (angle : CellCircle))‖ ^ 2 := by
  let trace := diskBoundaryFourier (diskCoreInto field)
  have sum : Summable (fun mode : ℤ × ℤ => ‖trace mode‖ ^ 2) := by
    have member := lp.memℓp trace
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at member
    simpa using member
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) trace
  norm_num at normFormula
  rw [normFormula, sum.tsum_prod]
  have reduction (mode : ℤ) :
      (∑' cell : ℤ, ‖trace (mode, cell)‖ ^ 2) =
        ‖fourierCoeff (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode‖ ^ 2 := by
    rw [tsum_eq_single 0, diskBoundaryFourier_core_cell]
    intro cell different
    rw [diskBoundaryFourier_core_zero field mode cell different, norm_zero, zero_pow (by decide)]
  simp_rw [reduction]
  have continuousField : Continuous (fun angle : ℝ =>
      field.value (boundaryDiskPoint (angle : CellCircle))) :=
    field.value.continuous.comp (boundaryDiskPoint_continuous.comp (AddCircle.continuous_mk' _))
  have parseval := (angular_hasSum_sq _ continuousField).tsum_eq
  have coefficients (mode : ℤ) := angularCoefficient_circle
    (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode
  simp_rw [coefficients] at parseval
  exact parseval

end Grad.CircularHighWeak
