import AIR5ActualKnownLowDiagonalResponse
import AEM22LiteralHighToLowSourceRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKnownLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.PhaseAlgebra Grad.AnnularCrossMaps
open Grad.GaugeCoefficients.Physical.Ledger

/-- Literal physical known source with exactly the original zero homogeneous slots. -/
def knownLowPhysicalSeven (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (source : HighKnownSourceBulk lower) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 7 :=
  (lowRhoPhysicalCoefficient parameters lower positive (source 0) radius mode 0) • operatorBasis 4 +
  (lowRhoPhysicalCoefficient parameters lower positive (source 1) radius mode 0) • operatorBasis 5 +
  (lowRhoPhysicalCoefficient parameters lower positive (source 2) radius mode 0) • operatorBasis 6

theorem knownLowSevenPacket_physical (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (source : HighKnownSourceBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive (knownLowSevenPacket lower source) radius mode =
        knownLowPhysicalSeven parameters lower positive source radius mode := by
  filter_upwards [knownLowSevenPacket_ae lower source] with radius packet
  intro mode
  unfold knownLowPhysicalSeven lowRhoPhysicalCoefficient
  rw [packet mode]
  simp only [smul_add, smul_smul, PiLp.smul_apply, smul_eq_mul]

/-- Actual source response is the full physical convolution with this SAME source tuple. -/
theorem knownLowPhysicalRow_hasSum (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (row : Fin 3) (known : HighKnownSourceBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (lowPhysicalRowKernel parameters L compact state row (collarRadius lower positive bounded radius)).entry
        shift (twoFrequencyTranslation shift mode)
        (knownLowPhysicalSeven parameters lower positive known radius (twoFrequencyTranslation shift mode)))
        (lowRhoPhysicalCoefficient parameters lower positive
          (lowPhysicalRowAction parameters L compact lower positive bounded state row (knownLowSevenPacket lower known)) radius mode) := by
  filter_upwards [lowRegularAction_physical parameters lower positive bounded
    (lowPhysicalRowKernel parameters L compact state row) (lowPhysicalRowKernel_regular parameters L compact state row)
    (knownLowSevenPacket lower known), knownLowSevenPacket_physical parameters lower positive known] with radius actual packet
  intro mode
  apply (actual mode).congr_fun
  intro shift
  rw [packet]

/-- Literal normalized source coefficients, including the two negative output derivatives. -/
theorem knownLowForcing_stored_ae (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (known : HighKnownSourceBulk lower) (g : DivisionRow 1 lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      knownLowForcing parameters L compact lower positive bounded state known g index radius =
      crossLowSourceSymbol parameters L radius index
        ((lowPhysicalRowAction parameters L compact lower positive bounded state 0 (knownLowSevenPacket lower known) + highSourceF lower known) index.2.val radius)
        (lowPhysicalRowAction parameters L compact lower positive bounded state 1 (knownLowSevenPacket lower known) index.2.val radius)
        ((lowPhysicalRowAction parameters L compact lower positive bounded state 2 (knownLowSevenPacket lower known) - radialRadiusRow lower positive g) index.2.val radius) := by
  let packet := knownLowSevenPacket lower known
  let j := lowPhysicalRowAction parameters L compact lower positive bounded state 0 packet + highSourceF lower known
  let c := lowPhysicalRowAction parameters L compact lower positive bounded state 1 packet
  let rv := lowPhysicalRowAction parameters L compact lower positive bounded state 2 packet - radialRadiusRow lower positive g
  let first := lowFirstOutput parameters lower L j
  let second := lowCellOutput lower L positive c
  let third := lowAngularOutput lower L positive rv
  filter_upwards [lowFirstOutput_ae parameters lower L j index,
    lowCellOutput_ae lower L positive c index, lowAngularOutput_ae lower L positive rv index,
    Lp.coeFn_add (first index + second index) (third index), Lp.coeFn_add (first index) (second index)]
    with radius firstLaw secondLaw thirdLaw totalSum firstSum
  change (first index + second index + third index) radius = _
  rw [totalSum]
  simp only [Pi.add_apply]
  rw [firstSum]
  simp only [Pi.add_apply]
  exact congrArg₂ (fun x y : ComplexEuclidean 1 => x + y)
    (congrArg₂ (fun x y : ComplexEuclidean 1 => x + y) firstLaw secondLaw) thirdLaw

/-- Multiplication by r in the original g term is literal on every mode. -/
theorem radialRadiusRow_ae (lower : ℝ) (positive : 0 < lower) (g : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      radialRadiusRow lower positive g mode radius = radius • g mode radius := by
  rw [ae_all_iff]
  intro mode
  exact scalarRadialMap_ae lower ⟨fun radius => radius, continuous_id⟩ 1
    (fun radius inside => by
      change |radius| ≤ 1
      rw [abs_of_nonneg (positive.le.trans inside.1)]
      exact inside.2) (g mode)

end Grad.AnnularKnownLow
