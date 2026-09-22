import AKE4SolvedFiveBlockInverse
import AJW11ExactOriginalHighRestriction
import AJV8ExactLowEndpointConsumer
import AJZ7ExactFullSourceRestrictionConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.AnnularLowEnergy
open Grad.AnnularForwardDatum Grad.AnnularCrossMaps Grad.AnnularOriginalHigh Grad.AnnularOriginalLow
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule

private theorem restrictionPair_fixedBound {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (first : E →L[ℝ] E') (second : F →L[ℝ] F') (constant : ℝ) (nonnegative : 0 ≤ constant)
    (firstBound : ∀ value, ‖first value‖ ≤ constant * ‖value‖)
    (secondBound : ∀ value, ‖second value‖ ≤ ‖value‖) (field : WithLp 2 (E × F)) :
    ‖restrictionHilbertPairMap first second field‖ ≤ (constant + 1) * ‖field‖ := by
  have pair := hilbert_norm_le_add (restrictionHilbertPairMap first second field)
  have retained := (firstBound field.ofLp.1).trans
    (mul_le_mul_of_nonneg_left (hilbert_first_bound field) nonnegative)
  have source := (secondBound field.ofLp.2).trans (hilbert_second_bound field)
  change ‖restrictionHilbertPairMap first second field‖ ≤ ‖first field.ofLp.1‖ + ‖second field.ofLp.2‖ at pair
  nlinarith only [pair,retained,source]

variable (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)

/-- The SAME original high and low retained graphs, restricted through the
accepted endpoint-changing BF6 maps. Both original derivative coordinates survive. -/
def originalRetainedRestriction : OriginalCoupledSpace lower length lowerPositive →L[ℂ]
    OriginalCoupledSpace upper length upperPositive :=
  restrictionPairMap
    (originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included)
    (originalLowEndpointRestriction parameters lower upper length included lowerPositive upperPositive upperBounded lengthPositive)

theorem originalRetainedRestriction_coordinates (field : OriginalCoupledSpace lower length lowerPositive) :
    (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field).ofLp =
      (originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field.ofLp.1,
        originalLowEndpointRestriction parameters lower upper length included lowerPositive upperPositive upperBounded lengthPositive field.ofLp.2) := rfl

/-- All five original AK31 graph blocks, with exactly the original source,
residual and retained norms. This definition has no smooth-core or PDE premise. -/
def originalFiveBlockRestriction : ForwardFiveBlocks parameters lower length lowerPositive →L[ℝ]
    ForwardFiveBlocks parameters upper length upperPositive :=
  restrictionHilbertPairMap
    ((originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included).restrictScalars ℝ)
    (originalFullSourceRestriction parameters lower upper included)

theorem originalFiveBlockRestriction_coordinates (field : ForwardFiveBlocks parameters lower length lowerPositive) :
    let output := originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field
    output.ofLp.1 = originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field.ofLp.1 ∧
    output.ofLp.2.ofLp.1.ofLp.1 = sourceGraphRestriction parameters 1 lower upper included 1 0 0 field.ofLp.2.ofLp.1.ofLp.1 ∧
    output.ofLp.2.ofLp.1.ofLp.2 = sourceGraphRestriction parameters 1 lower upper included 0 0 0 field.ofLp.2.ofLp.1.ofLp.2 ∧
    output.ofLp.2.ofLp.2.ofLp.1 = originalBulkRestriction 1 lower upper included field.ofLp.2.ofLp.2.ofLp.1 ∧
    output.ofLp.2.ofLp.2.ofLp.2 = originalBulkRestriction 1 lower upper included field.ofLp.2.ofLp.2.ofLp.2 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

def originalFiveBlockRestrictionConstant : ℝ :=
  ‖originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included‖ + 1

theorem originalFiveBlockRestrictionConstant_nonnegative :
    0 ≤ originalFiveBlockRestrictionConstant parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included :=
  add_nonneg (ContinuousLinearMap.opNorm_nonneg _) zero_le_one

/-- A finite bound between these fixed endpoints. The source portion is an
actual contraction; the retained portion uses the original bounded BF6 map. -/
theorem originalFiveBlockRestriction_bound (field : ForwardFiveBlocks parameters lower length lowerPositive) :
    ‖originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field‖ ≤
      originalFiveBlockRestrictionConstant parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included * ‖field‖ :=
  restrictionPair_fixedBound _ _ _ (ContinuousLinearMap.opNorm_nonneg _)
    (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included).le_opNorm
    (originalFullSourceRestriction_bound parameters lower upper included) field

theorem originalFiveBlockRestriction_continuous :
    Continuous (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included) :=
  (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included).continuous

end Grad.AnnularRestriction
