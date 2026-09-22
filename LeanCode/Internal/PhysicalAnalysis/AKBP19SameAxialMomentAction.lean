import AKBP5SameRadialConjugation
import AKBH1GenericMomentMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets

theorem startupAxialRatio_bound (cell : ℤ) :
    |(cell : ℝ) / Grad.CellWeights.cellWeight cell| ≤ 1 := by
  rw [abs_div, abs_of_pos (Grad.CellWeights.cellWeight_pos cell),
    div_le_iff₀ (Grad.CellWeights.cellWeight_pos cell), one_mul]
  apply (sq_le_sq₀ (abs_nonneg _) (Grad.CellWeights.cellWeight_pos cell).le).mp
  rw [sq_abs, Grad.CellBinomial.cellWeight_sq]
  linarith

/-- One genuine cell moment pays the axial derivative. The normalized
diagonal is bounded; the unbounded factor is never called a bounded map. -/
def startupAxialField {dimension : ℕ} (scale : ℝ) (moment : StartupL2 dimension) : StartupL2 dimension :=
  ((scale : ℂ) * Complex.I) • startupMomentDiagonalField
    (fun cell _ => (cell : ℝ) / Grad.CellWeights.cellWeight cell) 1 zero_le_one
    (fun cell _ => startupAxialRatio_bound cell) (fun _ => aestronglyMeasurable_const) moment

theorem startupAxialField_ae {dimension : ℕ} (scale : ℝ)
    (moment field : StartupL2 dimension)
    (same : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) moment field) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupAxialField scale moment point cell = ((scale : ℂ) * (Complex.I * (cell : ℂ))) • field point cell := by
  filter_upwards [same,startupMomentDiagonalField_ae
    (fun cell _ => (cell : ℝ) / Grad.CellWeights.cellWeight cell) 1 zero_le_one
    (fun cell _ => startupAxialRatio_bound cell) (fun _ => aestronglyMeasurable_const) moment,
    Lp.coeFn_smul ((scale : ℂ) * Complex.I) (startupMomentDiagonalField
      (fun cell _ => (cell : ℝ) / Grad.CellWeights.cellWeight cell) 1 zero_le_one
      (fun cell _ => startupAxialRatio_bound cell) (fun _ => aestronglyMeasurable_const) moment)]
    with point same diagonal value
  intro cell
  change startupAxialField scale moment point = _ at value
  simp only [value,lp.coeFn_smul,Pi.smul_apply,diagonal cell,same cell,
    RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul]
  congr 1
  have castCell : ((cell : ℝ) : ℂ) = (cell : ℂ) := by norm_cast
  simp only [Complex.ofReal_div,castCell]
  have nonzero : (Grad.CellWeights.cellWeight cell : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Grad.CellWeights.cellWeight_pos cell).ne'
  simp only [RCLike.ofReal_eq_complex_ofReal]
  field_simp

theorem startupAxialField_pairing {dimension : ℕ} (scale : ℝ)
    (moment field : StartupL2 dimension)
    (same : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) moment field)
    (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test (startupAxialField scale moment) =
      ((scale : ℂ) * (Complex.I * (cell : ℂ))) * startupCoordinateTestPairing cell coordinate test field := by
  rw [startupCoordinateTestPairing_apply,startupCoordinateTestPairing_apply,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [startupAxialField_ae scale moment field same] with point value
  rw [value cell]
  simp only [PiLp.smul_apply,RCLike.real_smul_eq_coe_smul (K := ℂ),smul_eq_mul]
  ring

theorem StartupRadialRelated.axial {dimension : ℕ} {symbol : ℤ → Spatial → ℝ}
    {weighted original : StartupL2 dimension} (same : StartupRadialRelated symbol weighted original)
    (scale : ℝ) :
    StartupRadialRelated symbol (startupAxialField scale weighted) (startupAxialField scale original) := by
  filter_upwards [same,startupMomentDiagonalField_ae
    (fun cell _ => (cell : ℝ) / Grad.CellWeights.cellWeight cell) 1 zero_le_one
    (fun cell _ => startupAxialRatio_bound cell) (fun _ => aestronglyMeasurable_const) weighted,
    startupMomentDiagonalField_ae
    (fun cell _ => (cell : ℝ) / Grad.CellWeights.cellWeight cell) 1 zero_le_one
    (fun cell _ => startupAxialRatio_bound cell) (fun _ => aestronglyMeasurable_const) original,
    Lp.coeFn_smul ((scale : ℂ) * Complex.I) (startupMomentDiagonalField
      (fun cell _ => (cell : ℝ) / Grad.CellWeights.cellWeight cell) 1 zero_le_one
      (fun cell _ => startupAxialRatio_bound cell) (fun _ => aestronglyMeasurable_const) weighted),
    Lp.coeFn_smul ((scale : ℂ) * Complex.I) (startupMomentDiagonalField
      (fun cell _ => (cell : ℝ) / Grad.CellWeights.cellWeight cell) 1 zero_le_one
      (fun cell _ => startupAxialRatio_bound cell) (fun _ => aestronglyMeasurable_const) original)]
    with point same weightedValue originalValue weightedSmul originalSmul
  intro cell
  change startupAxialField scale weighted point = _ at weightedSmul
  change startupAxialField scale original point = _ at originalSmul
  simp only [weightedSmul,originalSmul,lp.coeFn_smul,Pi.smul_apply,weightedValue cell,originalValue cell,same cell]
  rw [smul_comm _ (symbol cell point),smul_comm _ (symbol cell point)]

end Grad.CartesianStartup
