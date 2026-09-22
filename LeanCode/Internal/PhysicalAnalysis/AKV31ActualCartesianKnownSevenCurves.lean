import AKV30ActualPrimitiveSourceRadialSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.SourceCollarBulk
open Grad.SourceCollarAngular Grad.AnnularSourceGraph Grad.AnnularCurrentSource Grad.AnnularSmoothCore
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.AnnularOriginalSmoothCore Grad.AnnularStrongOrbit Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

def actualCartesianWeightedDatum (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) : StrongDataCarrier parameters lower positive bounded.le 0 0 :=
  originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0
    (actualOriginalSourceDatum parameters length rho epsilon field small lower positive bounded 0 source flat)

def actualCartesianPrimitiveCurve (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters)
    (slot : Fin 4) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  (actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).curve grade radius

def actualCartesianKnownSevenCurve (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters) (grade : ℕ) (radius : ℝ) : CellL2 7 :=
  (hilbertSlotInjection parameters 4 (actualCartesianPrimitiveCurve parameters length lower positive bounded source 0 grade radius) +
    hilbertSlotInjection parameters 5 (actualCartesianPrimitiveCurve parameters length lower positive bounded source 1 grade radius)) +
    hilbertSlotInjection parameters 6 (actualCartesianPrimitiveCurve parameters length lower positive bounded source 2 grade radius)

theorem actualCartesianKnownSevenCurve_smooth (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (actualCartesianKnownSevenCurve parameters length lower positive bounded source grade) (Icc lower 1) := by
  have injected (slot : Fin 7) (sourceSlot : Fin 4) :=
    (hilbertSlotInjection parameters slot).restrictScalars ℝ |>.contDiff.comp_contDiffOn
      ((actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source sourceSlot).smooth grade)
  exact ((injected 4 0).add (injected 5 1)).add (injected 6 2)

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)

theorem actualCartesianKnownRow_stored (slot : Fin 4) :
    strongKnownBulk parameters lower positive bounded.le
      (actualCartesianWeightedDatum parameters length rho epsilon field small lower positive bounded lengthPositive source flat) slot =
      divisionHighWeight lower positive bounded.le (actualCartesianPrimitiveRows parameters length lower positive bounded source slot) := by
  unfold actualCartesianWeightedDatum
  rw [originalStrongWeightEquivalence_eq_reconstruction]
  fin_cases slot <;> rfl

theorem actualCartesianPrimitiveCurve_actual (slot : Fin 4) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      actualCartesianPrimitiveCurve parameters length lower positive bounded source slot grade radius mode =
        (annularFrequency mode.1 mode.2 : ℂ)^grade •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (strongKnownBulk parameters lower positive bounded.le
                (actualCartesianWeightedDatum parameters length rho epsilon field small lower positive bounded lengthPositive source flat) slot) radius mode) := by
  rw [actualCartesianKnownRow_stored parameters length rho epsilon field small lower positive bounded lengthPositive source flat slot]
  filter_upwards [(actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).same grade,
    originalF1Coefficient_eq_originalRow parameters lower positive bounded
      (actualCartesianPrimitiveRows parameters length lower positive bounded source slot)] with radius curve decoded
  intro mode
  change _ = (annularFrequency mode.1 mode.2 : ℂ)^grade •
    ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
      originalF1Coefficient parameters lower positive bounded.le (actualCartesianPrimitiveRows parameters length lower positive bounded source slot) radius mode)
  rw [decoded mode]
  exact curve mode

theorem actualCartesianKnownSevenCurve_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      actualCartesianKnownSevenCurve parameters length lower positive bounded source grade radius mode =
        (annularFrequency mode.1 mode.2 : ℂ)^grade •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le
                (actualCartesianWeightedDatum parameters length rho epsilon field small lower positive bounded lengthPositive source flat))) radius mode) := by
  filter_upwards [actualCartesianPrimitiveCurve_actual parameters length rho epsilon field small lower positive bounded lengthPositive source flat 0 grade,
    actualCartesianPrimitiveCurve_actual parameters length rho epsilon field small lower positive bounded lengthPositive source flat 1 grade,
    actualCartesianPrimitiveCurve_actual parameters length rho epsilon field small lower positive bounded lengthPositive source flat 2 grade,
    knownPacket_physical_ae parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        (actualCartesianWeightedDatum parameters length rho epsilon field small lower positive bounded lengthPositive source flat))] with radius f0 rf0 f2 packet
  intro mode
  have injection (slot : Fin 7) (input : CellL2 1) :
      hilbertSlotInjection parameters slot input mode = matrixUnit slot 0 (input mode) := rfl
  change (hilbertSlotInjection parameters 4 _ mode+hilbertSlotInjection parameters 5 _ mode)+hilbertSlotInjection parameters 6 _ mode=_
  rw [injection,injection,injection,f0 mode,rf0 mode,f2 mode,packet mode]
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [rawOriginalKnownSevenVector,matrixUnit_apply,operatorBasis,smul_smul] <;> ring

end Grad.AnnularGeneralSourceRegularity
