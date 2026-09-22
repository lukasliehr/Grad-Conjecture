import AKAK3ActualPairPhysicalRadialPDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness

private theorem rawOriginalRHS_combine (length radius : ℝ) (mode : ℤ × ℤ)
    (x j c v kj kc kv f g : ComplexEuclidean 1) :
    rawOriginalUnknownRHS length radius mode x j c v + rawOriginalSourceRHS length radius mode kj kc kv f g =
      ((-((radius : ℂ)⁻¹)) • x - (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • (c+kc)) -
        (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • (v+kv)) + frequencyNumerator (some false) mode • g,
        (if mode.1=0 then (0 : ℂ) else 1) • ((j+kj)+f)) := by
  apply Prod.ext <;>
    simp only [rawOriginalUnknownRHS,rawOriginalSourceRHS,Prod.fst_add,Prod.snd_add,
      smul_add,neg_smul] <;> abel

private theorem rawOriginalRHS_combine_of_rows (length radius : ℝ) (mode : ℤ × ℤ)
    (x f g : ComplexEuclidean 1) (unknown known full : Fin 3 → ComplexEuclidean 1)
    (first : full 0 = unknown 0 + known 0) (second : full 1 = unknown 1 + known 1)
    (third : full 2 = unknown 2 + known 2) :
    rawOriginalUnknownRHS length radius mode x (unknown 0) (unknown 1) (unknown 2) +
        rawOriginalSourceRHS length radius mode (known 0) (known 1) (known 2) f g =
      ((-((radius : ℂ)⁻¹)) • x - (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • full 1) -
        (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • full 2) + frequencyNumerator (some false) mode • g,
        (if mode.1=0 then (0 : ℂ) else 1) • (full 0+f)) := by
  rw [first,second,third]
  exact rawOriginalRHS_combine length radius mode x _ _ _ _ _ _ f g

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : CoupledSpace lower length positive lengthPositive)

/-- Recombine the already proved unknown and source rows into the literal
full first and determinant radial equations; source data occur exactly once. -/
theorem generalOriginalFullRHS_literal :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      let full := fun index : Fin 3 => lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state index
          (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)) radius mode
      generalOriginalFullRHS parameters length compact lower positive lowerHalf lengthPositive state data field radius mode =
        ((-((radius : ℂ)⁻¹)) • sameCoupledXCoefficient parameters lower length positive
            (lowerHalf.trans_lt (by norm_num)) lengthPositive field 0 (radialClamp lower (lowerHalf.trans (by norm_num)) radius) mode -
          (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • full 1) -
          (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • full 2) +
          frequencyNumerator (some false) mode • lowRhoPhysicalCoefficient parameters lower positive
            (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2 radius mode,
        (if mode.1 = 0 then (0 : ℂ) else 1) •
          (full 0 + lowRhoPhysicalCoefficient parameters lower positive
            (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 3) radius mode)) := by
  filter_upwards [fullStrongPhysicalCoefficient_split parameters length compact lower lengthPositive positive
      (lowerHalf.trans (by norm_num)) state data field 0,
    fullStrongPhysicalCoefficient_split parameters length compact lower lengthPositive positive
      (lowerHalf.trans (by norm_num)) state data field 1,
    fullStrongPhysicalCoefficient_split parameters length compact lower lengthPositive positive
      (lowerHalf.trans (by norm_num)) state data field 2] with radius first second third
  intro mode
  let unknown := fun index : Fin 3 => lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state index
      (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field)) radius mode
  let known := fun index : Fin 3 => lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state index
      (knownLowSevenPacket lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data))) radius mode
  let full := fun index : Fin 3 => lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state index
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)) radius mode
  exact rawOriginalRHS_combine_of_rows length radius mode
    (sameCoupledXCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field 0
      (radialClamp lower (lowerHalf.trans (by norm_num)) radius) mode)
    (lowRhoPhysicalCoefficient parameters lower positive (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 3) radius mode)
    (lowRhoPhysicalCoefficient parameters lower positive (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2 radius mode)
    unknown known full (first mode) (second mode) (third mode)

def SmoothLowPhysicalRow.originalPhysicalRow {row : DivisionRow 7 lower}
    (seven : SmoothLowPhysicalRow parameters lower positive row) (index : Fin 3) :
    SmoothLowPhysicalRow parameters lower positive
      (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state index row) :=
  seven.action parameters lower positive (lowerHalf.trans_lt (by norm_num))
    (lowPhysicalRowKernel parameters length compact state index)
    (lowPhysicalRowKernel_regular parameters length compact state index)
    (originalPhysicalRowKernel_finiteOrder parameters length compact state lower positive (lowerHalf.trans_lt (by norm_num)) index)

def ActualSourceRadialCurves.forceRow
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data) :
    SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 3) where
  curve := curves.force
  smooth := curves.forceSmooth
  same := curves.forceSame

end Grad.ActualPolarEquations
