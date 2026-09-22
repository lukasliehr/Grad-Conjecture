import QS1CanonicalProjections
import QR3CoreCompatibility

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.RealFixedRanges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisCore
open Grad.SmoothingFamily Grad.Cor18 Grad.QuotientProjection Grad.CompletedReality

/-- Intersection of two literal fixed sets; no commutation premise is needed
for closedness or completeness. Commutation is used later for real-core density. -/
def jointFixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (projection symmetry : E →L[ℝ] E) : Submodule ℝ E :=
  (projection - ContinuousLinearMap.id ℝ E).ker ⊓ (symmetry - ContinuousLinearMap.id ℝ E).ker

theorem mem_jointFixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (projection symmetry : E →L[ℝ] E) (field : E) :
    field ∈ jointFixed projection symmetry ↔ projection field = field ∧ symmetry field = field := by
  change (projection field - field = 0 ∧ symmetry field - field = 0) ↔ _
  simp only [sub_eq_zero]

theorem jointFixed_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (projection symmetry : E →L[ℝ] E) : IsClosed (jointFixed projection symmetry : Set E) :=
  (projection - ContinuousLinearMap.id ℝ E).isClosed_ker.inter
    (symmetry - ContinuousLinearMap.id ℝ E).isClosed_ker

def stateRange (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    Submodule ℝ (XAmbient parameters grade) :=
  jointFixed ((stateProjection parameters parameter inside grade large).restrictScalars ℝ)
    (xConjugation parameters grade).toContinuousLinearEquiv.toContinuousLinearMap

def sourceRange (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    Submodule ℝ (ZAmbient parameters grade) :=
  jointFixed ((sourceProjection parameters grade large).restrictScalars ℝ)
    (zConjugation parameters grade).toContinuousLinearEquiv.toContinuousLinearMap

theorem stateRange_closed (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    IsClosed (stateRange parameters parameter inside grade large : Set (XAmbient parameters grade)) :=
  jointFixed_closed _ _

theorem sourceRange_closed (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    IsClosed (sourceRange parameters grade large : Set (ZAmbient parameters grade)) :=
  jointFixed_closed _ _

instance stateRange_complete (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    CompleteSpace (stateRange parameters parameter inside grade large) :=
  (stateRange_closed parameters parameter inside grade large).completeSpace_coe

instance sourceRange_complete (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    CompleteSpace (sourceRange parameters grade large) :=
  (sourceRange_closed parameters grade large).completeSpace_coe

theorem mem_stateRange (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : XAmbient parameters grade) :
    field ∈ stateRange parameters parameter inside grade large ↔
      stateProjection parameters parameter inside grade large field = field ∧
      xConjugation parameters grade field = field := mem_jointFixed _ _ _

theorem mem_sourceRange (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : ZAmbient parameters grade) :
    field ∈ sourceRange parameters grade large ↔ sourceProjection parameters grade large field = field ∧
      zConjugation parameters grade field = field := mem_jointFixed _ _ _

def stateInclusion (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    stateRange parameters parameter inside grade large →L[ℝ] XAmbient parameters grade :=
  (stateRange parameters parameter inside grade large).subtypeL

def sourceInclusion (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    sourceRange parameters grade large →L[ℝ] ZAmbient parameters grade :=
  (sourceRange parameters grade large).subtypeL

/-- The reference slice is the same construction at the chosen admissible seed. -/
abbrev referenceStateRange (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :=
  stateRange parameters reference inside grade large

theorem stateInclusion_norm (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateRange parameters parameter inside grade large) :
    ‖stateInclusion parameters parameter inside grade large field‖ = ‖field‖ := rfl

theorem sourceInclusion_norm (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : sourceRange parameters grade large) :
    ‖sourceInclusion parameters grade large field‖ = ‖field‖ := rfl

end Grad.RealFixedRanges
