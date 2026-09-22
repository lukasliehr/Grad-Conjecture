import AID10ActualDomegaRealization
import AEH3ActualOuterRetainedTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph
open Grad.AnnularCurrentBoundary Grad.AnnularOmegaGraph Grad.AnnularUniformBoundary

theorem normalizedScalarTest_inner_zero (lower L : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < L) (mode : HighAnnularMode) (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (innerZero : profile lower = 0) (vector : ComplexEuclidean 1) :
    bEnergyNormalize lower L positive (annularScalarTest lower L positive mode profile smooth vector) ∈
      annularInnerZero lower L positive bounded lengthPositive :=
  bEnergyNormalize_inner_zero lower L positive bounded lengthPositive _
    (annularScalarTest_inner_zero lower L positive bounded lengthPositive mode profile smooth innerZero vector)

/-- Actual physical outer trace vanishes for the SAME normalized scalar test. -/
theorem normalizedScalarTest_outer_zero (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (angular cell : ℕ)
    (mode : HighAnnularMode) (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (outerZero : profile 1 = 0) (vector : ComplexEuclidean 1) :
    actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive angular cell
      (bEnergyNormalize lower L positive (annularScalarTest lower L positive mode profile smooth vector)) = 0 := by
  rw [actualCurrentHighOuterTrace_same, bEnergyDecode_normalize, annularScalarTest, annularEnergyTrace_single]
  change highBoundaryIntoPositive parameters angular cell
    (lp.single 2 mode ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
      (profile 1 • vector))) = 0
  rw [outerZero, zero_smul, smul_zero]
  have zero : (lp.single 2 mode (0 : ComplexEuclidean 1) : AnnularBoundary) = 0 :=
    map_zero (lp.singleContinuousLinearMap ℂ (fun _ : HighAnnularMode => ComplexEuclidean 1) 2 mode)
  rw [zero, map_zero]

/-- The actual zero-outer variational packet law supplies every genuine compact test needed by Domega. -/
theorem compactPhysicalPacketEquation_of_testLaw (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field : DivisionRow 3 lower)
    (law : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val = 0 →
      inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val) field = 0) :
    CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field := by
  intro mode profile smooth _compact supported vector
  let compactTest := collarCompactTest lower profile smooth supported
  exact law ⟨bEnergyNormalize lower L positive (annularScalarTest lower L positive mode profile smooth vector),
    normalizedScalarTest_inner_zero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive mode profile smooth compactTest.lowerZero vector⟩
    (normalizedScalarTest_outer_zero parameters lower L positive lowerHalf lengthPositive 0 0 mode profile smooth compactTest.upperZero vector)

/-- Immediate complete graph consumer of the actual high variational packet equation. -/
theorem actualPacketLaw_Domega (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field : DivisionRow 3 lower)
    (law : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val = 0 →
      inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val) field = 0) :
    physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field ∈
      annularOmegaGraph lower L positive lengthPositive ∧
    ‖physicalOmegaCoordinates parameters lower L positive lengthPositive widthHalf widthLength field‖ ≤ 4 * ‖field‖ :=
  ⟨physicalOmegaCoordinates_mem parameters lower L positive lengthPositive widthHalf widthLength
    (lowerHalf.trans_lt (by norm_num)) field
    (compactPhysicalPacketEquation_of_testLaw parameters lower L positive lowerHalf lengthPositive widthHalf widthLength field law),
    physicalOmegaCoordinates_bound parameters lower L positive lengthPositive widthHalf widthLength field⟩

end Grad.AnnularCurrentGreen
