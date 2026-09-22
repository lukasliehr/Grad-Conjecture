import AEM20LiteralFreeHighPhysicalPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularOmegaGraph Grad.AnnularTiltedReference Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.Ledger

/-- Physical high xi and x from the SAME W and Domega values. -/
def highCrossOriginalXi (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : CrossHighSpace lower length positive lengthPositive)
    (radius : ℝ) (mode : HighAnnularMode) : ComplexEuclidean 1 :=
  (lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ)⁻¹ •
    annularEnergyValue lower length positive (bEnergyDecode lower length positive
      (crossHighW lower length positive lengthPositive field)) mode radius

def highCrossOriginalX (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : CrossHighSpace lower length positive lengthPositive)
    (radius : ℝ) (mode : HighAnnularMode) : ComplexEuclidean 1 :=
  (lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ)⁻¹ •
    crossHighX lower length positive lengthPositive field mode radius

theorem highCrossOriginalXi_tilted (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : CrossHighSpace lower length positive lengthPositive)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : HighAnnularMode) :
    highCrossOriginalXi parameters lower length positive lengthPositive field radius mode =
      highTiltedRowCoefficient parameters 0 lower
        (highBulkIntoFull lower (annularEnergyValue lower length positive (bEnergyDecode lower length positive
          (crossHighW lower length positive lengthPositive field)))) radius mode.val := by
  rw [← crossPhysicalCoefficient_same parameters lower positive _ radius inside mode.val]
  unfold lowRhoPhysicalCoefficient
  rw [highBulkIntoFull_high]
  rfl

theorem highCrossOriginalX_tilted (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : CrossHighSpace lower length positive lengthPositive)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : HighAnnularMode) :
    highCrossOriginalX parameters lower length positive lengthPositive field radius mode =
      highTiltedRowCoefficient parameters 0 lower
        (highBulkIntoFull lower (crossHighX lower length positive lengthPositive field)) radius mode.val := by
  rw [← crossPhysicalCoefficient_same parameters lower positive _ radius inside mode.val]
  unfold lowRhoPhysicalCoefficient
  rw [highBulkIntoFull_high]
  rfl

def highCrossOriginalSeven (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : CrossHighSpace lower length positive lengthPositive)
    (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 7 :=
  if high : 3 ≤ |mode.1| then
    crossSevenSymbol radius mode
      (highCrossOriginalXi parameters lower length positive lengthPositive field radius ⟨mode, high⟩)
      (highCrossOriginalX parameters lower length positive lengthPositive field radius ⟨mode, high⟩)
  else 0

theorem highCrossSevenInput_physical (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (field : CrossHighSpace lower length positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive (highCrossSevenInput lower length positive lengthPositive field) radius mode =
        highCrossOriginalSeven parameters lower length positive lengthPositive field radius mode := by
  rw [ae_all_iff]
  intro mode
  by_cases high : 3 ≤ |mode.1|
  · filter_upwards [highCrossSevenInput_ae lower length positive lengthPositive field ⟨mode, high⟩] with radius actual
    unfold lowRhoPhysicalCoefficient
    rw [actual]
    simp only [highCrossOriginalSeven, dif_pos high, highCrossOriginalXi, highCrossOriginalX, crossSevenSymbol_smul]
  · filter_upwards [Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1))] with radius zero
    unfold lowRhoPhysicalCoefficient
    rw [highCrossSevenInput_outside lower length positive lengthPositive field mode high, zero]
    simp only [Pi.zero_apply, smul_zero, highCrossOriginalSeven, dif_neg high]

/-- The three actual physical j,c=Rb3,rV coefficients on arbitrary high
(W,Domega), before taking their low output and normalized derivatives. -/
def highCrossOriginalRow (parameters : PhaseParameters) (lower length compact : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (field : CrossHighSpace lower length positive lengthPositive)
    (row : Fin 3) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive bounded state row
      (highCrossSevenInput lower length positive lengthPositive field)) radius mode

theorem highCrossOriginalRow_hasSum (parameters : PhaseParameters) (lower length compact : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (field : CrossHighSpace lower length positive lengthPositive) (row : Fin 3) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (lowPhysicalRowKernel parameters length compact state row (collarRadius lower positive bounded radius)).entry
        shift (twoFrequencyTranslation shift mode)
        (highCrossOriginalSeven parameters lower length positive lengthPositive field radius (twoFrequencyTranslation shift mode)))
        (highCrossOriginalRow parameters lower length compact positive bounded lengthPositive state field row radius mode) := by
  filter_upwards [lowRegularAction_physical parameters lower positive bounded
    (lowPhysicalRowKernel parameters length compact state row) (lowPhysicalRowKernel_regular parameters length compact state row)
    (highCrossSevenInput lower length positive lengthPositive field),
    highCrossSevenInput_physical parameters lower length positive lengthPositive field] with radius actual packet
  intro mode
  apply (actual mode).congr_fun
  intro shift
  rw [packet]

end Grad.AnnularCrossMaps
