import AXL6LinearTangential

noncomputable section

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange

def closedBasisPoint (coordinate : Fin 2) : ClosedDisk :=
  ⟨spatialBasis coordinate, spatialBasis_norm_le coordinate⟩

def complexDiskPoint (point : ClosedDisk) : ComplexEuclidean 2 :=
  WithLp.toLp 2 ![(point.val 0 : ℂ), (point.val 1 : ℂ)]

theorem complexDiskPoint_basis (coordinate : Fin 2) :
    complexDiskPoint (closedBasisPoint coordinate) = Gauges.planarBasis coordinate := by
  apply PiLp.ext
  intro index
  fin_cases coordinate <;> fin_cases index <;>
    simp [complexDiskPoint, closedBasisPoint, spatialBasis, Gauges.planarBasis_apply]

theorem complexDiskPoint_decomposition (point : ClosedDisk) :
    complexDiskPoint point = point.val 0 • Gauges.planarBasis 0 + point.val 1 • Gauges.planarBasis 1 := by
  apply PiLp.ext
  intro index
  fin_cases index <;> simp [complexDiskPoint, Gauges.planarBasis_apply]

theorem coreValue_coordinate_sum (parameters : PhaseParameters) (field : ACore parameters 2)
    (coordinate : Fin 2) (point : ClosedDisk) (angle : ℝ) :
    (∑' cell, axialPhase cell angle • ((field.val cell).value point coordinate)) =
      coreValue field point angle coordinate := by
  have mapped := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) coordinate).map_tsum
    (coreValue_summable field point angle)
  simpa only [map_smul, PiLp.proj_apply, coreValue] using mapped.symm

theorem cellValue_coordinate_norm_summable (parameters : PhaseParameters) (field : ACore parameters 2)
    (point : ClosedDisk) (coordinate : Fin 2) :
    Summable (fun cell => ‖(field.val cell).value point coordinate‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun cell => PiLp.norm_apply_le ((field.val cell).value point) coordinate)
    (Gauges.originalValueNorm_summable parameters field point)

/-- An exact Fourier coefficient descent of physical spatial linearity. -/
theorem cellLinear_of_physicalLinear (parameters : PhaseParameters) (field : ACore parameters 2)
    (operators : ℝ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (physical : ∀ point angle, coreValue field point angle = operators angle (complexDiskPoint point))
    (cell : ℤ) :
    field.val cell = linearColumnJet ((field.val cell).value (closedBasisPoint 0))
      ((field.val cell).value (closedBasisPoint 1)) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [linearColumnJet_value]
  have firstNorms := Gauges.originalValueNorm_summable parameters field (closedBasisPoint 0)
  have secondNorms := Gauges.originalValueNorm_summable parameters field (closedBasisPoint 1)
  have combinedNorms : Summable (fun index : ℤ => ‖point.val 0 • (field.val index).value (closedBasisPoint 0) +
      point.val 1 • (field.val index).value (closedBasisPoint 1)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun index => ?_) ((firstNorms.mul_left ‖point.val 0‖).add (secondNorms.mul_left ‖point.val 1‖))
    simpa only [norm_smul] using norm_add_le (point.val 0 • (field.val index).value (closedBasisPoint 0))
      (point.val 1 • (field.val index).value (closedBasisPoint 1))
  have equality := axialSeries_ext (fun index => (field.val index).value point)
    (fun index => point.val 0 • (field.val index).value (closedBasisPoint 0) +
      point.val 1 • (field.val index).value (closedBasisPoint 1))
    (Gauges.originalValueNorm_summable parameters field point) combinedNorms (fun angle => by
      simp only [smul_add, smul_comm (axialPhase _ angle) (point.val 0),
        smul_comm (axialPhase _ angle) (point.val 1)]
      rw [Summable.tsum_add ((coreValue_summable field (closedBasisPoint 0) angle).const_smul (point.val 0))
        ((coreValue_summable field (closedBasisPoint 1) angle).const_smul (point.val 1)),
        tsum_const_smul'', tsum_const_smul'']
      change coreValue field point angle = point.val 0 • coreValue field (closedBasisPoint 0) angle +
        point.val 1 • coreValue field (closedBasisPoint 1) angle
      rw [physical, physical, physical, complexDiskPoint_basis, complexDiskPoint_basis,
        complexDiskPoint_decomposition, map_add]
      exact congrArg₂ (· + ·) ((operators angle).map_smul_of_tower (point.val 0) _)
        ((operators angle).map_smul_of_tower (point.val 1) _))
  exact congrFun equality cell

/-- AL17 poloidal cancellation descends from the actual symmetric physical
matrix at each cell angle to every literal Fourier coefficient. -/
theorem tangentialCore_of_physical_symmetric (parameters : PhaseParameters) (field : ACore parameters 2)
    (operators : ℝ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (physical : ∀ point angle, coreValue field point angle = operators angle (complexDiskPoint point))
    (symmetric : ∀ angle, Gauges.operatorEntry (operators angle) 1 0 = Gauges.operatorEntry (operators angle) 0 1) :
    tangentialCore parameters field = 0 := by
  have entries := axialSeries_ext
    (fun cell => (field.val cell).value (closedBasisPoint 0) 1)
    (fun cell => (field.val cell).value (closedBasisPoint 1) 0)
    (cellValue_coordinate_norm_summable parameters field (closedBasisPoint 0) 1)
    (cellValue_coordinate_norm_summable parameters field (closedBasisPoint 1) 0) (fun angle => by
      rw [coreValue_coordinate_sum, coreValue_coordinate_sum, physical, physical,
        complexDiskPoint_basis, complexDiskPoint_basis]
      exact symmetric angle)
  apply Subtype.ext
  funext cell
  rw [tangentialCore_apply, cellLinear_of_physicalLinear parameters field operators physical cell]
  exact tangentialJet_linearColumn_zero _ _ (congrFun entries cell)

end Grad.ChartAxisLift
