import AKV31ActualCartesianKnownSevenCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.AnnularRestriction
open Grad.AnnularOriginalSmoothCore Grad.AnnularStrongOrbit Grad.GaugeCoefficients.Physical.Allocation

theorem originalThirdCurve_actual (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (row : DivisionRow 1 lower)
    (curves : OriginalRowRadialCurves parameters lower row) (stored : DivisionRow 1 lower)
    (storedSame : stored = divisionHighWeight lower positive bounded.le row) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      (radius • curves.curve grade radius) mode = (annularFrequency mode.1 mode.2 : ℂ)^grade •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • radius •
          lowRhoPhysicalCoefficient parameters lower positive stored radius mode) := by
  rw [storedSame]
  filter_upwards [curves.same grade,originalF1Coefficient_eq_originalRow parameters lower positive bounded row]
    with radius same decoded
  intro mode
  change radius • curves.curve grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade •
    ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • radius •
      originalF1Coefficient parameters lower positive bounded.le row radius mode)
  rw [same mode,decoded mode]
  rw [smul_comm radius ((annularFrequency mode.1 mode.2 : ℂ)^grade),smul_comm radius (Real.exp (radialPhase parameters radius mode.2) : ℂ)]

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)

def actualCartesianThirdCurve (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  radius • (actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat).curve grade radius

theorem actualCartesianThirdCurve_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (actualCartesianThirdCurve parameters length rho epsilon field small lower positive bounded source flat grade) (Icc lower 1) :=
  contDiffOn_id.smul ((actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat).smooth grade)

theorem actualCartesianThirdRow_stored :
    (strongToLow parameters lower positive bounded.le 0 0
      (actualCartesianWeightedDatum parameters length rho epsilon field small lower positive bounded lengthPositive source flat)).ofLp.1.ofLp.2 =
    divisionHighWeight lower positive bounded.le
      (originalAngularDecode lower (actualOriginalG3Row parameters length rho epsilon field small lower positive bounded.le 0 source)) := by
  unfold actualCartesianWeightedDatum
  rw [originalStrongWeight_g]
  rfl

theorem actualCartesianThirdCurve_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      actualCartesianThirdCurve parameters length rho epsilon field small lower positive bounded source flat grade radius mode =
        (annularFrequency mode.1 mode.2 : ℂ)^grade •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • radius •
            lowRhoPhysicalCoefficient parameters lower positive
              (strongToLow parameters lower positive bounded.le 0 0
                (actualCartesianWeightedDatum parameters length rho epsilon field small lower positive bounded lengthPositive source flat)).ofLp.1.ofLp.2 radius mode) := by
  exact originalThirdCurve_actual parameters lower positive bounded _
    (actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat) _
    (actualCartesianThirdRow_stored parameters length rho epsilon field small lower positive bounded lengthPositive source flat) grade

/-- The full actual original Cartesian datum satisfies the source-curve
contract without finite support or any assumed source regularity. The A-core
jets and genuine SCS kappa products supply all derivatives at the same width. -/
def actualCartesianSourceRadialCurves :
    ActualSourceRadialCurves parameters lower positive bounded
      (actualCartesianWeightedDatum parameters length rho epsilon field small lower positive bounded lengthPositive source flat) where
  seven := actualCartesianKnownSevenCurve parameters length lower positive bounded source
  force := actualCartesianPrimitiveCurve parameters length lower positive bounded source 3
  third := actualCartesianThirdCurve parameters length rho epsilon field small lower positive bounded source flat
  sevenSmooth := actualCartesianKnownSevenCurve_smooth parameters length lower positive bounded source
  forceSmooth := (actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source 3).smooth
  thirdSmooth := actualCartesianThirdCurve_smooth parameters length rho epsilon field small lower positive bounded source flat
  sevenSame := actualCartesianKnownSevenCurve_actual parameters length rho epsilon field small lower positive bounded lengthPositive source flat
  forceSame := actualCartesianPrimitiveCurve_actual parameters length rho epsilon field small lower positive bounded lengthPositive source flat 3
  thirdSame := actualCartesianThirdCurve_actual parameters length rho epsilon field small lower positive bounded lengthPositive source flat

end Grad.AnnularGeneralSourceRegularity
