import AKI17LiteralTuplePhysicalReconstruction
import AJX2OriginalFullGraphObservation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularSourceGraph

/-- Representation in the exact original five measured graph coordinates.
The residual coordinates are computed AH24 expressions of the four fields;
there is no PDE, inverse, free-residual tuple or equation-graph condition. -/
structure OriginalTupleObservation (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower)
    (point : OriginalFiveBlockAmbient parameters lower length positive) : Prop where
  pressure : ∀ radius : Icc lower (1 : ℝ), ∀ mode,
    originalPhysicalCoefficient (tuple.val 0) radius.val mode = angularInverseMultiplier mode •
      sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
        (originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive point.ofLp.1) 0 radius mode
  scalar : ∀ radius : Icc lower (1 : ℝ), ∀ mode,
    originalPhysicalCoefficient (tuple.val 1) radius.val mode =
      sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive
        (originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive point.ofLp.1) 0 radius mode
  sourceZero : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
    originalPhysicalCoefficient (tuple.val 2) radius mode = originalF1Coefficient parameters lower positive bounded.le
      (unweightedSourceF0Bulk parameters lower point.ofLp.2.ofLp.1.ofLp.1) radius mode
  sourceTwo : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
    originalPhysicalCoefficient (tuple.val 3) radius mode = originalF1Coefficient parameters lower positive bounded.le
      (unweightedSourceF2Bulk parameters lower point.ofLp.2.ofLp.1.ofLp.2) radius mode
  firstResidual : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
    originalTupleF1 parameters length compact lower positive state tuple ⟨radius, inside⟩ mode =
      originalF1Coefficient parameters lower positive bounded.le point.ofLp.2.ofLp.2.ofLp.1 radius mode
  thirdResidual : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
    originalTupleG3 parameters length compact lower positive state tuple ⟨radius, inside⟩ mode =
      originalG3Coefficient parameters lower positive bounded.le point.ofLp.2.ofLp.2.ofLp.2 radius mode

/-- Literal original core image on the original c <= min(1/2,L) domain.
Graph realization for arbitrary tuples is a separate totality assertion;
this definition faithfully records only represented tuples and their norms. -/
def CoreAnn (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (domain : lower ≤ min (1 / 2) length) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) :
    Set (OriginalFiveBlockAmbient parameters lower length positive) :=
  {point | ∃ tuple : OriginalSmoothTuple parameters lower,
    OriginalTupleObservation parameters length compact lower positive
      ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive state tuple point}

/-- AK31 completion in the SAME five norms. No equation graph is inserted
into this closure definition. -/
def CoreAnnClosure (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (domain : lower ≤ min (1 / 2) length) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) :
    Set (OriginalFiveBlockAmbient parameters lower length positive) :=
  closure (CoreAnn parameters length compact lower positive domain lengthPositive state)

theorem coreAnnClosure_closed (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (domain : lower ≤ min (1 / 2) length) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) :
    IsClosed (CoreAnnClosure parameters length compact lower positive domain lengthPositive state) := isClosed_closure

/-- The literal full G3 coordinate includes exactly the original first
angular norm, rather than replacing it by Rg. -/
theorem OriginalTupleObservation.strengthenedThird {parameters : PhaseParameters} {length compact lower : ℝ}
    {positive : 0 < lower} {bounded : lower < 1} {lengthPositive : 0 < length}
    {state : RetainedInverseState parameters length compact}
    {tuple : OriginalSmoothTuple parameters lower} {point : OriginalFiveBlockAmbient parameters lower length positive}
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple point) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
      ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • originalTupleG3 parameters length compact lower positive state tuple ⟨radius, inside⟩ mode =
        originalF1Coefficient parameters lower positive bounded.le point.ofLp.2.ofLp.2.ofLp.2 radius mode := by
  filter_upwards [represented.thirdResidual, originalG3Coefficient_strengthened parameters lower positive bounded.le
    point.ofLp.2.ofLp.2.ofLp.2] with radius original strengthened
  intro inside mode
  rw [original inside mode, strengthened mode]

end Grad.AnnularOriginalSmoothCore
