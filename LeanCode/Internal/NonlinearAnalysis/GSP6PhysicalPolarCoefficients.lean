import GSP5PolarEntryCalculus

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1400000
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame

theorem polarEntryCellTerm_fourier (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (slot : Fin 2 × Fin 2) (radius polarAngle axialAngle : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasSum (fun cell => fourierPhase cell axialAngle *
      polarEntryCellTerm parameters family coherent row column slot cell (radius, polarAngle) 0)
      (cellExponential (polarEntryFrequency row column slot) polarAngle *
        matrixPairing (fun index => kappaLaurentRight row slot.1 index)
          (familyMatrix family 0 axialAngle (polarClosedPoint radius polarAngle nonnegative bounded))
          (fun index => kappaLaurentRight column slot.2 index)) := by
  have sum := (coefficientColumnJet_scalarFourier parameters (mappedMatrixFamily parameters family row slot.1)
    (mappedMatrixFamily_coherent parameters family coherent row slot.1) (kappaLaurentRight column slot.2)
    radius polarAngle axialAngle nonnegative bounded).mul_left
      (cellExponential (polarEntryFrequency row column slot) polarAngle)
  rw [mappedMatrixFamily_physicalValue parameters family coherent, ContinuousLinearMap.comp_apply,
    scalarRowMapping_pairing] at sum
  apply sum.congr_fun
  intro cell
  change fourierPhase cell axialAngle *
    (cellExponential (polarEntryFrequency row column slot) polarAngle * _) = _
  exact mul_left_comm _ _ _

theorem polarEntryCell_fourier (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (radius polarAngle axialAngle : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasSum (fun cell => fourierPhase cell axialAngle * polarEntryCell parameters family coherent row column cell (radius, polarAngle) 0)
      (polarMatrixEntry row column polarAngle
        (familyMatrix family 0 axialAngle (polarClosedPoint radius polarAngle nonnegative bounded))) := by
  have sum := hasSum_sum (s := Finset.univ) (fun slot _ =>
    polarEntryCellTerm_fourier parameters family coherent row column slot radius polarAngle axialAngle nonnegative bounded)
  rw [← polarMatrixEntry_laurent] at sum
  apply sum.congr_fun
  intro cell
  change fourierPhase cell axialAngle *
    (PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : PhysicalValue 1 →L[ℂ] ℂ)
      ((∑ slot, polarEntryCellTerm parameters family coherent row column slot cell) (radius, polarAngle)) = _
  rw [Finset.sum_apply, map_sum, Finset.mul_sum]
  rfl

theorem polarEntryCell_norm_summable (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (fun cell => ‖polarEntryCell parameters family coherent row column cell (radius, angle) 0‖) := by
  have each (slot : Fin 2 × Fin 2) :
      Summable (fun cell => ‖polarEntryCellTerm parameters family coherent row column slot cell (radius, angle)‖) := by
    simp only [polarEntryCellTerm, angularCharacterField, norm_smul, cellExponential_norm, one_mul,
      originalPolarValue_closed _ radius angle nonnegative bounded]
    exact coefficientColumnJet_norm_summable parameters _ (mappedMatrixFamily_coherent parameters family coherent row slot.1) _ _
  have norms := summable_sum (fun slot (_ : slot ∈ Finset.univ) => each slot)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ norms
  intro cell
  apply (PiLp.norm_apply_le _ 0).trans
  simpa only [polarEntryCell, Finset.sum_apply] using norm_sum_le Finset.univ
    (fun slot => polarEntryCellTerm parameters family coherent row column slot cell (radius, angle))

theorem polarEntry_axialCoefficient (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (cell : ℤ) :
    angularCoefficient (fun axialAngle => polarMatrixEntry row column angle
      (familyMatrix family 0 axialAngle (polarClosedPoint radius angle nonnegative bounded))) cell =
      polarEntryCell parameters family coherent row column cell (radius, angle) 0 :=
  angularCoefficient_of_axialSeries _
    (polarEntryCell_norm_summable parameters family coherent row column radius angle nonnegative bounded) _
    (polarEntryCell_fourier parameters family coherent row column radius angle · nonnegative bounded) cell

theorem polarEntry_doubleCoefficient (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle => polarMatrixEntry row column angle
      (familyMatrix family 0 axialAngle (polarClosedPoint radius angle nonnegative bounded))) mode.2) mode.1 =
      polarEntryFourier parameters family coherent row column 0 radius mode 0 := by
  simp_rw [polarEntry_axialCoefficient parameters family coherent row column radius _ nonnegative bounded mode.2]
  have projected := angularCoefficient_component
    (fun angle => polarEntryCell parameters family coherent row column mode.2 (radius, angle))
    ((polarEntryCell_smooth parameters family coherent row column mode.2).continuous.comp
      (continuous_const.prodMk continuous_id)) 0 mode.1
  exact projected.symm.trans (congrArg (fun value : ComplexEuclidean 1 => value 0)
    (polarEntryCell_coefficient parameters family coherent row column mode.2 mode.1 0 radius))

end Grad.ActualGaugeSigmaPrimitives
