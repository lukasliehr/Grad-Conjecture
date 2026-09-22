import AJL4OnceOnlySmoothSevenPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularKnownLow Grad.AnnularCurrentLow Grad.AnnularLowEnergy

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (core : OriginalSmoothSourceCore parameters)

def smoothKnownSourceCurve (power : ℕ) : ℝ → CellL2 7 :=
  (smoothStrongSevenRow parameters lower length positive bounded lengthPositive core).physicalPolynomial parameters power

def smoothF1SourceCurve (power : ℕ) : ℝ → CellL2 1 :=
  (smoothStrongKnownRow parameters lower positive bounded core length lengthPositive 3).physicalPolynomial parameters power

def smoothGSourceCurve (power : ℕ) : ℝ → CellL2 1 :=
  (smoothStrongGRow parameters lower positive bounded core length lengthPositive).physicalPolynomial parameters power

def smoothG3SourceCurve (power : ℕ) : ℝ → CellL2 1 :=
  ((smoothStrongGRow parameters lower positive bounded core length lengthPositive).radius positive).physicalPolynomial parameters power

theorem smoothKnownSourceCurve_smooth (power : ℕ) :
    ContDiffOn ℝ ∞ (smoothKnownSourceCurve parameters lower length positive bounded lengthPositive core power) (Icc lower 1) :=
  FiniteSmoothStoredRow.physicalPolynomial_smooth _ parameters positive power

theorem smoothF1SourceCurve_smooth (power : ℕ) :
    ContDiffOn ℝ ∞ (smoothF1SourceCurve parameters lower length positive bounded lengthPositive core power) (Icc lower 1) :=
  FiniteSmoothStoredRow.physicalPolynomial_smooth _ parameters positive power

theorem smoothGSourceCurve_smooth (power : ℕ) :
    ContDiffOn ℝ ∞ (smoothGSourceCurve parameters lower length positive bounded lengthPositive core power) (Icc lower 1) :=
  FiniteSmoothStoredRow.physicalPolynomial_smooth _ parameters positive power

theorem smoothG3SourceCurve_smooth (power : ℕ) :
    ContDiffOn ℝ ∞ (smoothG3SourceCurve parameters lower length positive bounded lengthPositive core power) (Icc lower 1) :=
  FiniteSmoothStoredRow.physicalPolynomial_smooth _ parameters positive power

/-- SAME once-only known seven packet in the original AJG9/10 decoding. -/
theorem smoothKnownSourceCurve_actual (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      smoothKnownSourceCurve parameters lower length positive bounded lengthPositive core power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive
            (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded
              ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core))) radius mode :=
  FiniteSmoothStoredRow.physicalPolynomial_actual _ parameters positive power

theorem smoothF1SourceCurve_actual (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      smoothF1SourceCurve parameters lower length positive bounded lengthPositive core power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive
            (strongKnownBulk parameters lower positive bounded
              ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core) 3) radius mode :=
  FiniteSmoothStoredRow.physicalPolynomial_actual _ parameters positive power

theorem smoothGSourceCurve_actual (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      smoothGSourceCurve parameters lower length positive bounded lengthPositive core power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive
            ((strongToLow parameters lower positive bounded 0 0
              ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core)).ofLp.1.ofLp.2) radius mode :=
  FiniteSmoothStoredRow.physicalPolynomial_actual _ parameters positive power

/-- This is r*g; AIR7 subtracts exactly this third forcing. -/
theorem smoothG3SourceCurve_actual (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      smoothG3SourceCurve parameters lower length positive bounded lengthPositive core power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          (radius • lowRhoPhysicalCoefficient parameters lower positive
            ((strongToLow parameters lower positive bounded 0 0
              ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core)).ofLp.1.ofLp.2) radius mode) :=
  FiniteSmoothStoredRow.radius_physicalPolynomial_actual _ parameters positive power

end Grad.AnnularSmoothSources
