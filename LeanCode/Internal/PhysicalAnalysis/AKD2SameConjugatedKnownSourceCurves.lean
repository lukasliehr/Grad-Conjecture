import AKD1ExactConjugatedFinitePolynomial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.PhaseAlgebra Grad.BoundaryKernelAction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularKnownLow Grad.AnnularCurrentLow Grad.AnnularLowEnergy

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (core : OriginalSmoothSourceCore parameters)

/-- The once-only known source packet in original phase-conjugated radial
Hilbert coordinates, preserving all seven slots and the original rho. -/
def conjugatedKnownSourceCurve (power : ℕ) : ℝ → CellL2 7 :=
  (smoothStrongSevenRow parameters lower length positive bounded lengthPositive core).conjugatedPolynomial power

def conjugatedKnownRowCurve (slot : Fin 4) (power : ℕ) : ℝ → CellL2 1 :=
  (smoothStrongKnownRow parameters lower positive bounded core length lengthPositive slot).conjugatedPolynomial power

def conjugatedGSourceCurve (power : ℕ) : ℝ → CellL2 1 :=
  (smoothStrongGRow parameters lower positive bounded core length lengthPositive).conjugatedPolynomial power

def conjugatedG3SourceCurve (power : ℕ) : ℝ → CellL2 1 :=
  ((smoothStrongGRow parameters lower positive bounded core length lengthPositive).radius positive).conjugatedPolynomial power

theorem conjugatedKnownSourceCurve_smooth (power : ℕ) :
    ContDiffOn ℝ ∞ (conjugatedKnownSourceCurve parameters lower length positive bounded lengthPositive core power) (Icc lower 1) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_smooth _ positive power

theorem conjugatedKnownRowCurve_smooth (slot : Fin 4) (power : ℕ) :
    ContDiffOn ℝ ∞ (conjugatedKnownRowCurve parameters lower length positive bounded lengthPositive core slot power) (Icc lower 1) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_smooth _ positive power

theorem conjugatedGSourceCurve_smooth (power : ℕ) :
    ContDiffOn ℝ ∞ (conjugatedGSourceCurve parameters lower length positive bounded lengthPositive core power) (Icc lower 1) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_smooth _ positive power

theorem conjugatedG3SourceCurve_smooth (power : ℕ) :
    ContDiffOn ℝ ∞ (conjugatedG3SourceCurve parameters lower length positive bounded lengthPositive core power) (Icc lower 1) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_smooth _ positive power

theorem conjugatedKnownSourceCurve_actual (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedKnownSourceCurve parameters lower length positive bounded lengthPositive core power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded
                ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core))) radius mode) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_actual _ parameters positive power

theorem conjugatedKnownRowCurve_actual (slot : Fin 4) (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedKnownRowCurve parameters lower length positive bounded lengthPositive core slot power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (strongKnownBulk parameters lower positive bounded
                ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core) slot) radius mode) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_actual _ parameters positive power

theorem conjugatedGSourceCurve_actual (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedGSourceCurve parameters lower length positive bounded lengthPositive core power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              ((strongToLow parameters lower positive bounded 0 0
                ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core)).ofLp.1.ofLp.2) radius mode) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_actual _ parameters positive power

theorem conjugatedG3SourceCurve_actual (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedG3SourceCurve parameters lower length positive bounded lengthPositive core power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            (radius • lowRhoPhysicalCoefficient parameters lower positive
              ((strongToLow parameters lower positive bounded 0 0
                ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core)).ofLp.1.ofLp.2) radius mode)) :=
  FiniteSmoothStoredRow.radius_conjugatedPolynomial_actual
    (smoothStrongGRow parameters lower positive bounded core length lengthPositive) parameters positive power

theorem conjugatedKnownSourceCurve_physical (power : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    conjugatedKnownSourceCurve parameters lower length positive bounded lengthPositive core power radius mode =
      (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        smoothKnownSourceCurve parameters lower length positive bounded lengthPositive core power radius mode :=
  FiniteSmoothStoredRow.conjugatedPolynomial_physical _ parameters power radius mode

theorem conjugatedKnownSourceCurve_grade (power : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    conjugatedKnownSourceCurve parameters lower length positive bounded lengthPositive core power radius mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
        conjugatedKnownSourceCurve parameters lower length positive bounded lengthPositive core 0 radius mode :=
  FiniteSmoothStoredRow.conjugatedPolynomial_grade _ power radius mode

end Grad.AnnularSmoothSources
