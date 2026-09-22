import FP17M15
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.ContinuousMap.Compact

noncomputable section

set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

local instance fp17CellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

local instance fp17ReconstructionClosedDiskCompactSpace : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

/-- The literal cell Fourier character at period `2π`. -/
def cellCharacter (cell : ℤ) : C(CellCircle, ℂ) :=
  fourier cell

@[simp] theorem cellCharacter_norm (cell : ℤ) :
    ‖cellCharacter cell‖ = 1 := by
  exact fourier_norm cell

@[simp] theorem cellCharacter_apply_norm (cell : ℤ) (circle : CellCircle) :
    ‖cellCharacter cell circle‖ = 1 := by
  exact Circle.norm_coe _

/-- One Fourier term on the actual closed disk times cell circle. -/
def ordinaryDiskCellTerm {dimension : ℕ} (cell : ℤ)
    (field : ClosedJet dimension) :
    C(DiskCellDomain, ComplexEuclidean dimension) where
  toFun point := cellCharacter cell point.2 • field.value point.1
  continuous_toFun :=
    ((cellCharacter cell).continuous.comp continuous_snd).smul
      (field.value.continuous.comp continuous_fst)

@[simp] theorem ordinaryDiskCellTerm_apply {dimension : ℕ} (cell : ℤ)
    (field : ClosedJet dimension) (point : DiskCellDomain) :
    ordinaryDiskCellTerm cell field point =
      cellCharacter cell point.2 • field.value point.1 := rfl

theorem ordinaryDiskCellTerm_norm_le {dimension : ℕ} (cell : ℤ)
    (field : ClosedJet dimension) :
    ‖ordinaryDiskCellTerm cell field‖ ≤ ‖field.value‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro point
  rw [ordinaryDiskCellTerm_apply, norm_smul]
  calc
    ‖cellCharacter cell point.2‖ * ‖field.value point.1‖ ≤
        ‖cellCharacter cell‖ * ‖field.value‖ := by
      gcongr
      · exact (cellCharacter cell).norm_coe_le_norm point.2
      · exact field.value.norm_coe_le_norm point.1
    _ = ‖field.value‖ := by rw [cellCharacter_norm, one_mul]

theorem ordinaryDiskCellTerm_summable {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension) :
    Summable (fun cell : ℤ => ordinaryDiskCellTerm cell (coefficients.1 cell)) := by
  have coefficientNorms : Summable (fun cell : ℤ =>
      ‖(coefficients.1 cell).value‖) := by
    simpa [closedDerivative_zero_order] using
      physicalDerivative_series_summable coefficients
        emptyCartesianWord 0
  exact Summable.of_norm_bounded coefficientNorms
    (fun cell => ordinaryDiskCellTerm_norm_le cell (coefficients.1 cell))

/-- Uniform Fourier reconstruction on the actual compact disk×circle domain. -/
def ordinaryReconstructedValue {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension) :
    C(DiskCellDomain, ComplexEuclidean dimension) :=
  ∑' cell : ℤ, ordinaryDiskCellTerm cell (coefficients.1 cell)

theorem ordinaryReconstructedValue_apply {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (point : DiskCellDomain) :
    ordinaryReconstructedValue coefficients point =
      ∑' cell : ℤ,
        cellCharacter cell point.2 • (coefficients.1 cell).value point.1 := by
  symm
  simpa only [ordinaryReconstructedValue, ordinaryDiskCellTerm_apply] using
    ContinuousMap.tsum_apply (ordinaryDiskCellTerm_summable coefficients) point

theorem hasSum_ordinaryDiskCellTerm {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension) :
    HasSum (fun cell : ℤ => ordinaryDiskCellTerm cell (coefficients.1 cell))
      (ordinaryReconstructedValue coefficients) :=
  (ordinaryDiskCellTerm_summable coefficients).hasSum

/-- The exact scalar acquired after `cellOrder` derivatives in the cell
coordinate. -/
def cellDerivativeFactor (cell : ℤ) (cellOrder : ℕ) : ℂ :=
  (Complex.I * (cell : ℂ)) ^ cellOrder

@[simp] theorem cellDerivativeFactor_norm (cell : ℤ) (cellOrder : ℕ) :
    ‖cellDerivativeFactor cell cellOrder‖ = |(cell : ℝ)| ^ cellOrder := by
  simp [cellDerivativeFactor, Complex.norm_intCast]

/-- One term of an arbitrary planar-word/cell-order derivative series. -/
def ordinaryDerivativeDiskCellTerm {dimension order : ℕ}
    (word : CartesianWord order) (cellOrder : ℕ) (cell : ℤ)
    (field : ClosedJet dimension) :
    C(DiskCellDomain, ComplexEuclidean dimension) :=
  cellDerivativeFactor cell cellOrder •
    ordinaryDiskCellTerm cell (shiftedClosedJet field word)

@[simp] theorem ordinaryDerivativeDiskCellTerm_apply {dimension order : ℕ}
    (word : CartesianWord order) (cellOrder : ℕ) (cell : ℤ)
    (field : ClosedJet dimension) (point : DiskCellDomain) :
    ordinaryDerivativeDiskCellTerm word cellOrder cell field point =
      cellDerivativeFactor cell cellOrder •
        (cellCharacter cell point.2 •
          closedDerivative field order word point.1) := by
  rfl

theorem ordinaryDerivativeDiskCellTerm_norm_le {dimension order : ℕ}
    (word : CartesianWord order) (cellOrder : ℕ) (cell : ℤ)
    (field : ClosedJet dimension) :
    ‖ordinaryDerivativeDiskCellTerm word cellOrder cell field‖ ≤
      |(cell : ℝ)| ^ cellOrder * ‖closedDerivative field order word‖ := by
  rw [ordinaryDerivativeDiskCellTerm, norm_smul,
    cellDerivativeFactor_norm]
  exact mul_le_mul_of_nonneg_left
    (ordinaryDiskCellTerm_norm_le cell (shiftedClosedJet field word))
    (pow_nonneg (abs_nonneg _) _)

theorem ordinaryDerivativeDiskCellTerm_summable {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    Summable (fun cell : ℤ =>
      ordinaryDerivativeDiskCellTerm word cellOrder cell
        (coefficients.1 cell)) := by
  exact Summable.of_norm_bounded
    (physicalDerivative_series_summable coefficients word cellOrder)
    (fun cell => ordinaryDerivativeDiskCellTerm_norm_le word cellOrder cell
      (coefficients.1 cell))

/-- The uniformly convergent extension of every requested mixed derivative. -/
def ordinaryDerivativeExtension {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    C(DiskCellDomain, ComplexEuclidean dimension) :=
  ∑' cell : ℤ,
    ordinaryDerivativeDiskCellTerm word cellOrder cell
      (coefficients.1 cell)

theorem ordinaryDerivativeExtension_apply {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ)
    (point : DiskCellDomain) :
    ordinaryDerivativeExtension coefficients word cellOrder point =
      ∑' cell : ℤ,
        cellDerivativeFactor cell cellOrder •
          (cellCharacter cell point.2 •
            closedDerivative (coefficients.1 cell) order word point.1) := by
  symm
  simpa only [ordinaryDerivativeExtension,
    ordinaryDerivativeDiskCellTerm_apply] using
    ContinuousMap.tsum_apply
      (ordinaryDerivativeDiskCellTerm_summable coefficients word cellOrder)
      point

theorem hasSum_ordinaryDerivativeDiskCellTerm {dimension order : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (word : CartesianWord order) (cellOrder : ℕ) :
    HasSum (fun cell : ℤ =>
      ordinaryDerivativeDiskCellTerm word cellOrder cell
        (coefficients.1 cell))
      (ordinaryDerivativeExtension coefficients word cellOrder) :=
  (ordinaryDerivativeDiskCellTerm_summable coefficients word cellOrder).hasSum

theorem ordinaryDerivativeExtension_zero_zero {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension) :
    ordinaryDerivativeExtension coefficients emptyCartesianWord 0 =
      ordinaryReconstructedValue coefficients := by
  rw [ordinaryDerivativeExtension, ordinaryReconstructedValue]
  apply tsum_congr
  intro cell
  ext point
  simp [ordinaryDerivativeDiskCellTerm, cellDerivativeFactor,
    closedDerivative_zero_order]

/-- Fourier orthogonality for one vector-valued cell character. -/
theorem fourierCoeff_cellCharacter_smul {dimension : ℕ}
    (source target : ℤ) (value : ComplexEuclidean dimension) :
    fourierCoeff (T := 2 * Real.pi)
        (fun circle : CellCircle => cellCharacter source circle • value) target =
      if source = target then value else 0 := by
  have scalarCoefficient :
      fourierCoeff (T := 2 * Real.pi) (fourier source) target =
        if target = source then 1 else 0 := by
    have raw :=
      congrFun (fourierCoeff_fourier (T := 2 * Real.pi) source) target
    by_cases equality : target = source <;>
      simpa [Pi.single, equality] using raw
  rw [fourierCoeff]
  calc
    ∫ circle : CellCircle,
          fourier (-target) circle •
            (cellCharacter source circle • value)
          ∂AddCircle.haarAddCircle =
        (∫ circle : CellCircle,
          fourier (-target) circle * cellCharacter source circle
          ∂AddCircle.haarAddCircle) • value := by
      convert (integral_smul_const
          (μ := AddCircle.haarAddCircle)
          (fun circle : CellCircle =>
            fourier (-target) circle * cellCharacter source circle) value) using 1
      simp only [mul_smul]
    _ = (fourierCoeff (T := 2 * Real.pi) (fourier source) target) • value := by
      rfl
    _ = (if target = source then 1 else 0) • value :=
      congrArg (fun scalar : ℂ => scalar • value) scalarCoefficient
    _ = if source = target then value else 0 := by
      by_cases equality : source = target
      · rw [if_pos equality, if_pos equality.symm, one_smul]
      · rw [if_neg equality, if_neg (fun reverse => equality reverse.symm),
          zero_smul]

/-- The reconstructed continuous field has exactly the prescribed cell
Fourier coefficient at every closed-disk point. -/
theorem fourierCoeff_ordinaryReconstructedValue {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (point : ClosedDisk) (target : ℤ) :
    fourierCoeff (T := 2 * Real.pi)
        (fun circle : CellCircle =>
          ordinaryReconstructedValue coefficients (point, circle)) target =
      (coefficients.1 target).value point := by
  let term : ℤ → CellCircle → ComplexEuclidean dimension := fun source circle =>
    fourier (-target) circle •
      (cellCharacter source circle • (coefficients.1 source).value point)
  have termIntegrable : ∀ source : ℤ,
      Integrable (term source) AddCircle.haarAddCircle := by
    intro source
    have continuousTerm : Continuous (term source) :=
      (fourier (-target)).continuous.smul
        ((cellCharacter source).continuous.smul continuous_const)
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        continuousTerm.continuousOn)
  have coefficientNorms : Summable (fun source : ℤ =>
      ‖(coefficients.1 source).value point‖) := by
    have supNorms : Summable (fun source : ℤ =>
        ‖(coefficients.1 source).value‖) := by
      simpa [closedDerivative_zero_order] using
        physicalDerivative_series_summable coefficients
          emptyCartesianWord 0
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun source => (coefficients.1 source).value.norm_coe_le_norm point)
      supNorms
  have circleSeriesSummable : ∀ circle : CellCircle,
      Summable (fun source : ℤ =>
        cellCharacter source circle • (coefficients.1 source).value point) := by
    intro circle
    exact Summable.of_norm_bounded coefficientNorms (fun source => by
      rw [norm_smul, cellCharacter_apply_norm, one_mul])
  have distribute (circle : CellCircle) :
      fourier (-target) circle •
          (∑' source : ℤ,
            cellCharacter source circle •
              (coefficients.1 source).value point) =
        ∑' source : ℤ, term source circle := by
    have mapped :=
      (((fourier (-target) circle) •
        ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)).map_tsum
          (circleSeriesSummable circle))
    change fourier (-target) circle •
          (∑' source : ℤ,
            cellCharacter source circle •
              (coefficients.1 source).value point) =
        ∑' source : ℤ,
          fourier (-target) circle •
            (cellCharacter source circle •
              (coefficients.1 source).value point) at mapped
    exact mapped
  have integralNorms : Summable (fun source : ℤ =>
      ∫ circle : CellCircle, ‖term source circle‖
        ∂AddCircle.haarAddCircle) := by
    apply coefficientNorms.congr
    intro source
    have integrandIdentity :
        (fun circle : CellCircle => ‖term source circle‖) =
          fun _ => ‖(coefficients.1 source).value point‖ := by
      funext circle
      simp only [term, norm_smul, cellCharacter_apply_norm, one_mul]
      rw [show ‖fourier (-target) circle‖ = 1 by exact Circle.norm_coe _]
      exact one_mul _
    rw [integrandIdentity, integral_const]
    simp
  rw [fourierCoeff]
  simp_rw [ordinaryReconstructedValue_apply]
  simp_rw [distribute]
  change (∫ circle : CellCircle, ∑' source : ℤ, term source circle
      ∂AddCircle.haarAddCircle) = _
  rw [← integral_tsum_of_summable_integral_norm termIntegrable integralNorms]
  have termIntegral : ∀ source : ℤ,
      (∫ circle : CellCircle, term source circle
        ∂AddCircle.haarAddCircle) =
        if source = target then (coefficients.1 source).value point else 0 := by
    intro source
    simpa only [term, fourierCoeff] using
      fourierCoeff_cellCharacter_smul source target
        ((coefficients.1 source).value point)
  simp_rw [termIntegral]
  rw [tsum_ite_eq target]

end Grad.CartesianState
