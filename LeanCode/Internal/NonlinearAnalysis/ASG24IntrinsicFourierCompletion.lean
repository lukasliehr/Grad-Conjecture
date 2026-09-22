import ASG23IntrinsicRadialEnergy

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction

def weakSourceMode (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (angular cell : ℕ) (value derivative : (ℤ × ℤ) → CollarL2 (ComplexEuclidean dimension) lower)
    (weak : ∀ mode, CollarWeakDerivative lower (value mode) (derivative mode)) (mode : ℤ × ℤ) :
    WeightedRadialH1 dimension lower :=
  splitTangentialWeight angular cell mode •
    weakRadialRealization dimension lower positive bounded (value mode) (derivative mode) (weak mode)

theorem weakSourceMode_norm_sq (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (angular cell : ℕ) (value derivative : (ℤ × ℤ) → CollarL2 (ComplexEuclidean dimension) lower)
    (weak : ∀ mode, CollarWeakDerivative lower (value mode) (derivative mode)) (mode : ℤ × ℤ) :
    ‖weakSourceMode dimension lower positive bounded angular cell value derivative weak mode‖ ^ 2 =
      splitTangentialWeight angular cell mode ^ 2 * weakRadialEnergy dimension lower (value mode) (derivative mode) := by
  rw [weakSourceMode, norm_smul, Real.norm_of_nonneg (splitTangentialWeight_pos angular cell mode).le,
    mul_pow, weakRadialRealization_norm_sq]

/-- Finite-norm intrinsic weak Fourier pairs are actual elements of the
original finite smooth Fourier completion. No new endpoint coordinate enters. -/
def weakSourceRealization (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : (ℤ × ℤ) → CollarL2 (ComplexEuclidean dimension) lower)
    (weak : ∀ mode, CollarWeakDerivative lower (value mode) (derivative mode))
    (finiteEnergy : Summable (fun mode : ℤ × ℤ =>
      splitTangentialWeight angular cell mode ^ 2 * weakRadialEnergy dimension lower (value mode) (derivative mode))) :
    AnnularSourceH1 parameters dimension lower angular cell :=
  ⟨weakSourceMode dimension lower positive bounded angular cell value derivative weak, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact finiteEnergy.congr (fun mode => (weakSourceMode_norm_sq dimension lower positive bounded angular cell value derivative weak mode).symm)⟩

theorem weakSourceRealization_value (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : (ℤ × ℤ) → CollarL2 (ComplexEuclidean dimension) lower)
    (weak : ∀ mode, CollarWeakDerivative lower (value mode) (derivative mode))
    (finiteEnergy : Summable (fun mode : ℤ × ℤ =>
      splitTangentialWeight angular cell mode ^ 2 * weakRadialEnergy dimension lower (value mode) (derivative mode)))
    (mode : ℤ × ℤ) :
    annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell
      (weakSourceRealization parameters dimension lower positive bounded angular cell value derivative weak finiteEnergy) mode 0 =
      value mode := by
  unfold annularConjugatedCoordinate annularConjugatedMode
  change collarH1Coordinate (ComplexEuclidean dimension) lower 0
    ((splitTangentialWeight angular cell mode)⁻¹ • weightedToOrdinary dimension lower positive bounded.le
      (splitTangentialWeight angular cell mode • weakRadialRealization dimension lower positive bounded (value mode) (derivative mode) (weak mode))) = _
  simp only [map_smul]
  rw [smul_smul, inv_mul_cancel₀ (splitTangentialWeight_pos angular cell mode).ne', one_smul,
    weakRadialRealization_value]

theorem weakSourceRealization_slope (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : (ℤ × ℤ) → CollarL2 (ComplexEuclidean dimension) lower)
    (weak : ∀ mode, CollarWeakDerivative lower (value mode) (derivative mode))
    (finiteEnergy : Summable (fun mode : ℤ × ℤ =>
      splitTangentialWeight angular cell mode ^ 2 * weakRadialEnergy dimension lower (value mode) (derivative mode)))
    (mode : ℤ × ℤ) :
    annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell
      (weakSourceRealization parameters dimension lower positive bounded angular cell value derivative weak finiteEnergy) mode 1 =
      derivative mode := by
  unfold annularConjugatedCoordinate annularConjugatedMode
  change collarH1Coordinate (ComplexEuclidean dimension) lower 1
    ((splitTangentialWeight angular cell mode)⁻¹ • weightedToOrdinary dimension lower positive bounded.le
      (splitTangentialWeight angular cell mode • weakRadialRealization dimension lower positive bounded (value mode) (derivative mode) (weak mode))) = _
  simp only [map_smul]
  rw [smul_smul, inv_mul_cancel₀ (splitTangentialWeight_pos angular cell mode).ne', one_smul,
    weakRadialRealization_slope]

/-- The reverse realization preserves the exact AH10 energy. -/
theorem weakSourceRealization_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : (ℤ × ℤ) → CollarL2 (ComplexEuclidean dimension) lower)
    (weak : ∀ mode, CollarWeakDerivative lower (value mode) (derivative mode))
    (finiteEnergy : Summable (fun mode : ℤ × ℤ =>
      splitTangentialWeight angular cell mode ^ 2 * weakRadialEnergy dimension lower (value mode) (derivative mode))) :
    ‖weakSourceRealization parameters dimension lower positive bounded angular cell value derivative weak finiteEnergy‖ ^ 2 =
      ∑' mode : ℤ × ℤ, splitTangentialWeight angular cell mode ^ 2 *
        weakRadialEnergy dimension lower (value mode) (derivative mode) := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (weakSourceRealization parameters dimension lower positive bounded angular cell value derivative weak finiteEnergy)
  norm_num at formula
  rw [formula]
  apply tsum_congr
  intro mode
  exact weakSourceMode_norm_sq dimension lower positive bounded angular cell value derivative weak mode

end Grad.AnnularSourceGraph
