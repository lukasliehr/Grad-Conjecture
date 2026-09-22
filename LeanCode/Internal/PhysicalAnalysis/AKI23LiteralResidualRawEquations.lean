import AKI22ArbitraryOriginalTuplePacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularSourceGraph

/-- Reverse AH24 flux algebra retains c=Rb3 and the original +Rg sign. -/
theorem originalFluxResidual_reverse (length radius : ℝ) (mode : ℤ × ℤ)
    (p slope b v g : ComplexEuclidean 1)
    (residual : slope + (radius : ℂ)⁻¹ • p +
      (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • (angularMeanFreeMultiplier mode • b)) + v = g) :
    frequencyNumerator (some false) mode • slope =
      (-((radius : ℂ)⁻¹)) • (frequencyNumerator (some false) mode • p) -
        (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • (frequencyNumerator (some false) mode • b)) -
        frequencyNumerator (some false) mode • v + frequencyNumerator (some false) mode • g := by
  rw [← residual]
  by_cases zero : mode.1 = 0
  · simp [frequencyNumerator, zero]
  · ext slot
    simp only [frequencyNumerator, angularMeanFreeMultiplier, if_neg zero, one_smul,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (tuple : OriginalSmoothTuple parameters lower)
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (data,candidate)))

private abbrev rhsCandidate := originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive candidate
private abbrev rhsDatum := originalToStrong parameters lower length positive bounded.le lengthPositive 0 0 data

/-- Actual full physical j/c/rV rows of an arbitrary original candidate. -/
def originalCandidateRow (row : Fin 3) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le
        (rhsDatum parameters length lower positive bounded lengthPositive data)
        (rhsCandidate parameters length lower positive bounded lengthPositive candidate))) radius mode

include represented

/-- The literal first residual enforces the genuine raw xi equation for
arbitrary represented points; the only f is the original full coordinate. -/
theorem OriginalTupleObservation.rawFirst :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ _inside : radius ∈ Icc lower 1, ∀ mode,
      derivWithin (fun location => originalPhysicalCoefficient (tuple.val 1) location mode) (Icc lower 1) radius =
        angularMeanFreeMultiplier mode •
          (originalCandidateRow parameters length compact lower positive bounded lengthPositive state data candidate 0 radius mode +
            originalF1Coefficient parameters lower positive bounded.le data.val.ofLp.1.ofLp.2.ofLp.1 radius mode) := by
  filter_upwards [represented.firstResidual,
    represented.physicalRows parameters length compact lower positive bounded lengthPositive state data candidate tuple,
    originalF1Coefficient_meanFree parameters lower positive bounded.le data.val.ofLp.1.ofLp.2.ofLp.1
      (OriginalStrongCarrier.mean_free parameters lower 0 0 data).2.1] with radius residual rows mean
  intro inside mode
  have actual := rows inside 0 mode
  rw [tuplePhysicalRowTrace_first] at actual
  have equation := residual inside mode
  change _ - angularMeanFreeMultiplier mode • _ = _ at equation
  change _ = originalCandidateRow parameters length compact lower positive bounded lengthPositive state data candidate 0 radius mode at actual
  rw [actual] at equation
  have fixed : angularMeanFreeMultiplier mode • originalF1Coefficient parameters lower positive bounded.le data.val.ofLp.1.ofLp.2.ofLp.1 radius mode =
      originalF1Coefficient parameters lower positive bounded.le data.val.ofLp.1.ofLp.2.ofLp.1 radius mode := mean mode
  rw [smul_add,fixed]
  exact sub_eq_iff_eq_add.mp equation |>.trans (add_comm _ _)

/-- The literal pressure residual enforces the original raw X equation.
The physical c and rV are the completed full seven-input rows. -/
theorem OriginalTupleObservation.rawFlux :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
      frequencyNumerator (some false) mode •
        derivWithin (fun location => originalPhysicalCoefficient (tuple.val 0) location mode) (Icc lower 1) radius =
      (-((radius : ℂ)⁻¹)) • sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
        (rhsCandidate parameters length lower positive bounded lengthPositive candidate) 0 ⟨radius,inside⟩ mode -
      (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode •
        originalCandidateRow parameters length compact lower positive bounded lengthPositive state data candidate 1 radius mode) -
      (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode •
        originalCandidateRow parameters length compact lower positive bounded lengthPositive state data candidate 2 radius mode) +
      frequencyNumerator (some false) mode • originalG3Coefficient parameters lower positive bounded.le data.val.ofLp.1.ofLp.2.ofLp.2 radius mode := by
  filter_upwards [represented.thirdResidual,
    represented.physicalRows parameters length compact lower positive bounded lengthPositive state data candidate tuple] with radius residual rows
  intro inside mode
  have equation := originalFluxResidual_reverse length radius mode _ _ _ _ _ (residual inside mode)
  have cSame := (tuplePhysicalRowTrace_c_coefficient parameters length compact lower positive state tuple ⟨radius,inside⟩ mode).symm.trans (rows inside 1 mode)
  have vSame := (tuplePhysicalRowTrace_rV_coefficient parameters length compact lower positive state tuple ⟨radius,inside⟩ mode).symm.trans (rows inside 2 mode)
  have pSame := represented.pressure_R parameters length compact lower positive bounded lengthPositive state data candidate tuple ⟨radius,inside⟩ mode
  change frequencyNumerator (some false) mode • _ = originalCandidateRow parameters length compact lower positive bounded lengthPositive state data candidate 1 radius mode at cSame
  change (radius : ℂ) • _ = originalCandidateRow parameters length compact lower positive bounded lengthPositive state data candidate 2 radius mode at vSame
  rw [pSame,cSame] at equation
  rw [← vSame, smul_comm (frequencyNumerator (some false) mode), inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (positive.trans_le inside.1).ne')]
  exact equation

end Grad.AnnularOriginalSmoothCore
