import AKV32ActualFullCartesianSourceCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.AnnularStrongOrbit Grad.GaugeCoefficients.Physical.Allocation Grad.ExhaustionSourceAllocation
open Grad.AnnularForwardDatum
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.AnnularRestriction

def ActualSourceRadialCurves.of_same_bulk {parameters : PhaseParameters} {lower : ℝ}
    {positive : 0 < lower} {bounded : lower < 1}
    {first second : StrongDataCarrier parameters lower positive bounded.le 0 0}
    (curves : ActualSourceRadialCurves parameters lower positive bounded first)
    (known : strongKnownBulk parameters lower positive bounded.le second = strongKnownBulk parameters lower positive bounded.le first)
    (third : (strongToLow parameters lower positive bounded.le 0 0 second).ofLp.1.ofLp.2 =
      (strongToLow parameters lower positive bounded.le 0 0 first).ofLp.1.ofLp.2) :
    ActualSourceRadialCurves parameters lower positive bounded second where
  seven := curves.seven
  force := curves.force
  third := curves.third
  sevenSmooth := curves.sevenSmooth
  forceSmooth := curves.forceSmooth
  thirdSmooth := curves.thirdSmooth
  sevenSame grade := by rw [known]; exact curves.sevenSame grade
  forceSame grade := by rw [known]; exact curves.forceSame grade
  thirdSame grade := by rw [third]; exact curves.thirdSame grade

theorem originalKnownBulk_same_sources (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (first second : OriginalStrongCarrier parameters lower 0 0)
    (same : second.val.ofLp.1=first.val.ofLp.1) :
    strongKnownBulk parameters lower positive bounded.le
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 second) =
    strongKnownBulk parameters lower positive bounded.le
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 first) := by

  exact (originalStrongWeight_knownRows parameters lower length positive bounded.le lengthPositive second).trans
    ((congrArg (originalStoredKnownRows parameters lower positive bounded.le) same).trans
      (originalStrongWeight_knownRows parameters lower length positive bounded.le lengthPositive first).symm)

theorem originalThirdBulk_same_sources (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (first second : OriginalStrongCarrier parameters lower 0 0)
    (same : second.val.ofLp.1=first.val.ofLp.1) :
    (strongToLow parameters lower positive bounded.le 0 0
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 second)).ofLp.1.ofLp.2 =
    (strongToLow parameters lower positive bounded.le 0 0
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 first)).ofLp.1.ofLp.2 := by

  exact (originalStrongWeight_g parameters lower length positive bounded.le lengthPositive second).trans
    ((congrArg (fun sources : ForwardSourceBlocks parameters lower =>
      divisionHighWeight lower positive bounded.le (originalAngularDecode lower sources.ofLp.2.ofLp.2)) same).trans
      (originalStrongWeight_g parameters lower length positive bounded.le lengthPositive first).symm)

/-- Source regularity depends on the four prescribed source blocks and
therefore preserves the actual incoming and outer data of an observed solution. -/
def actualCartesianSourceCurves_of_sourceBlocks
    (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (same : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length rho epsilon field small lower positive bounded 0 source flat).val.ofLp.1) :
    ActualSourceRadialCurves parameters lower positive bounded
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) :=
  (actualCartesianSourceRadialCurves parameters length rho epsilon field small lower positive bounded lengthPositive source flat).of_same_bulk
    (originalKnownBulk_same_sources parameters lower length positive bounded lengthPositive _ data same)
    (originalThirdBulk_same_sources parameters lower length positive bounded lengthPositive _ data same)

end Grad.AnnularGeneralSourceRegularity
