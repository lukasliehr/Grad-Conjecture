import AKI7LiteralTupleCoefficientAlgebra
import AJP1FullPhysicalRowLinearity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualBoundaryPrimitives
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularKnownLow Grad.AnnularCurrentLow
open Grad.AnnularPhysicalReconstruction Grad.AnnularLowEnergy
open Grad.AnnularStrongOrbit Grad.AnnularCoupledInverse Grad.AnnularPhysicalFourier Grad.AnnularCurrentSource
open Grad.AnnularSmoothSources Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularWeightedSmoothCore
open scoped ContDiff

def rawOriginalKnownSevenVector (f0 rf0 f2 : ComplexEuclidean 1) : ComplexEuclidean 7 :=
  f0 0 • operatorBasis 4 + rf0 0 • operatorBasis 5 + f2 0 • operatorBasis 6

theorem knownPacket_physical_ae (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (known : HighKnownSourceBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive (knownLowSevenPacket lower known) radius mode =
        rawOriginalKnownSevenVector
          (lowRhoPhysicalCoefficient parameters lower positive (known 0) radius mode)
          (lowRhoPhysicalCoefficient parameters lower positive (known 1) radius mode)
          (lowRhoPhysicalCoefficient parameters lower positive (known 2) radius mode) := by
  filter_upwards [knownLowSevenPacket_ae lower known] with radius same
  intro mode
  unfold lowRhoPhysicalCoefficient
  rw [same mode]
  simp only [rawOriginalKnownSevenVector, smul_add, smul_smul, PiLp.smul_apply, smul_eq_mul]

/-- The actual stored unknown and once-only known packet are decoded with
one common original rho/phase weight. -/
theorem fullPacket_physical_ae (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowRhoPhysicalCoefficient parameters lower positive
        (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field) radius mode =
      rawPhysicalSevenVector radius mode
        (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode)
        (sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode) +
      rawOriginalKnownSevenVector
        (lowRhoPhysicalCoefficient parameters lower positive (strongKnownBulk parameters lower positive bounded.le data 0) radius mode)
        (lowRhoPhysicalCoefficient parameters lower positive (strongKnownBulk parameters lower positive bounded.le data 1) radius mode)
        (lowRhoPhysicalCoefficient parameters lower positive (strongKnownBulk parameters lower positive bounded.le data 2) radius mode) := by
  rw [fullStrongSevenInput_split]
  filter_upwards [lowRhoPhysicalCoefficient_add_ae parameters lower positive
      (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field)
      (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data)),
    homogeneousCoupledSevenInput_sameSections parameters lower length positive bounded lengthPositive field,
    knownPacket_physical_ae parameters lower positive (strongKnownBulk parameters lower positive bounded.le data)]
      with radius added unknown known
  intro mode
  rw [added mode, known mode]
  congr 1
  unfold lowRhoPhysicalCoefficient
  rw [unknown mode]
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne') _

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)
    (weightedSmooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade) (Icc lower 1))

private abbrev bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
private abbrev response := originalSmoothSourceResponse parameters length compact lower positive lowerHalf
  lengthPositive widthHalf widthLength state small core
private abbrev data := (strongSmoothDenseMap parameters lower length positive (bounded lower lowerHalf).le lengthPositive).mapping core
private abbrev actualTuple := sameResponseOriginalTuple parameters length compact lower positive lowerHalf lengthPositive
  widthHalf widthLength state small core weightedSmooth

/-- The literal tuple's input is the SAME original shared seven packet,
including the full copied F0 and its genuine angular derivative. -/
theorem sameResponseOriginalTuple_packet :
    ∀ᵐ location ∂volume.restrict (Icc lower 1), ∀ inside : location ∈ Icc lower 1, ∀ mode,
      originalTupleNormalizedCoefficient parameters lower
        (actualTuple parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core weightedSmooth)
        ⟨location, inside⟩ mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (fullStrongSevenInput parameters length lower lengthPositive positive (bounded lower lowerHalf).le
          (data parameters length lower positive lowerHalf lengthPositive core)
          (response parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)) location mode := by
  have sources := strongSmoothDenseMap_actual parameters lower length positive (bounded lower lowerHalf).le lengthPositive core
  filter_upwards [fullPacket_physical_ae parameters length lower lengthPositive positive (bounded lower lowerHalf)
      (data parameters length lower positive lowerHalf lengthPositive core)
      (response parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core),
    originalSmoothSourcePhysicalF0_actual parameters lower positive (bounded lower lowerHalf) core,
    originalSmoothSourcePhysicalF2_actual parameters lower positive (bounded lower lowerHalf) core,
    strongKnownBulk_genuineAngular parameters lower positive (bounded lower lowerHalf).le
      (data parameters length lower positive lowerHalf lengthPositive core)] with location packet f0 f2 rf0
  intro inside mode
  rw [packet mode, radialClamp_eq lower (bounded lower lowerHalf).le location inside]
  have f0Same : originalPhysicalCoefficient
      (originalSmoothSourcePhysicalF0 parameters lower positive (bounded lower lowerHalf) core) location mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (strongKnownBulk parameters lower positive (bounded lower lowerHalf).le
          (data parameters length lower positive lowerHalf lengthPositive core) 0) location mode := by
    rw [data, sources]
    exact f0 mode
  have f2Same : originalPhysicalCoefficient
      (originalSmoothSourcePhysicalF2 parameters lower positive (bounded lower lowerHalf) core) location mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (strongKnownBulk parameters lower positive (bounded lower lowerHalf).le
          (data parameters length lower positive lowerHalf lengthPositive core) 2) location mode := by
    rw [data, sources]
    exact f2 mode
  have rf0Same : lowRhoPhysicalCoefficient parameters lower positive
      (strongKnownBulk parameters lower positive (bounded lower lowerHalf).le
        (data parameters length lower positive lowerHalf lengthPositive core) 1) location mode =
      frequencyNumerator (some false) mode • lowRhoPhysicalCoefficient parameters lower positive
      (strongKnownBulk parameters lower positive (bounded lower lowerHalf).le
        (data parameters length lower positive lowerHalf lengthPositive core) 0) location mode := by
    unfold lowRhoPhysicalCoefficient
    rw [rf0 mode]
    exact smul_comm _ _ _
  have xiSame := originalSmoothResponsePhysicalXi_raw_coefficient parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core ⟨location, inside⟩ mode
  have pSame := (originalSmoothResponsePhysicalP_R_coefficient parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core ⟨location, inside⟩ mode).trans
      (originalSmoothResponsePhysicalX_raw_coefficient parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core ⟨location, inside⟩ mode)
  change frequencyNumerator (some false) mode • originalPhysicalCoefficient
    (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) location mode = _ at pSame
  change originalPhysicalCoefficient
    (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) location mode = _ at xiSame
  unfold originalTupleNormalizedCoefficient
  change WithLp.toLp 2 ![_, _, _, _, _, _, _] = _
  change (WithLp.toLp 2 ![(frequencyNumerator (some false) mode • originalPhysicalCoefficient
      (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) location mode) 0,
    ((location : ℂ)⁻¹ • (frequencyNumerator (some false) mode • originalPhysicalCoefficient
      (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) location mode)) 0,
    (frequencyNumerator (some true) mode • originalPhysicalCoefficient
      (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) location mode) 0,
    ((location : ℂ)⁻¹ • originalPhysicalCoefficient
      (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) location mode) 0,
    originalPhysicalCoefficient (originalSmoothSourcePhysicalF0 parameters lower positive (bounded lower lowerHalf) core) location mode 0,
    (frequencyNumerator (some false) mode • originalPhysicalCoefficient
      (originalSmoothSourcePhysicalF0 parameters lower positive (bounded lower lowerHalf) core) location mode) 0,
    originalPhysicalCoefficient (originalSmoothSourcePhysicalF2 parameters lower positive (bounded lower lowerHalf) core) location mode 0] : ComplexEuclidean 7) = _
  rw [pSame, xiSame, f0Same, f2Same, rf0Same]
  ext slot
  fin_cases slot <;> simp [rawPhysicalSevenVector, rawOriginalKnownSevenVector, matrixUnit_apply, operatorBasis]

end Grad.AnnularOriginalSmoothCore
