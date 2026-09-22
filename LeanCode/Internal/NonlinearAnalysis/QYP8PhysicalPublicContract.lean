import QYP7PhysicalRealDerivatives

noncomputable section

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.RealFixedRanges Grad.ConstrainedGrades Grad.QuotientProjection Grad.Q24Realization

/-- Literal seed-coordinate ℓ¹ plus real curvature plus original constrained
state direction norm; only the state enters the high base factor. -/
def PhysicalMixedDerivativeEstimate (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) : Prop :=
  ∀ (grade : ℕ) (large : 4 ≤ grade) (order : ℕ)
    (seedPatch : Set Seed.Parameters), IsCompact seedPatch → seedPatch ⊆ Seed.parameterDomain →
    ∀ (curvatureBound stateBound : ℝ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
        (directions : Fin order → RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)),
        realMixedSeed parameters reference insideR (grade + 6) (realHighLarge grade) base ∈ seedPatch →
        ‖base.ofLp.2.ofLp.1‖ ≤ curvatureBound →
        base ∈ realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade) →
        ‖stateLowering parameters reference insideR realLowLarge (realLowLeHigh grade) base.ofLp.2.ofLp.2‖ ≤ stateBound →
        ‖iteratedFDeriv ℝ order
          (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (by omega)) base directions‖ ≤
          constant * realMixedCompletedOneHigh parameters reference insideR grade order base directions

/-- The exact public Q24 contract on the canonical real carriers. Its map
is the actual completed literal residual, not a chosen replacement. -/
structure PhysicalMixedBanachRealization (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) : Prop where
  smooth : ∀ (grade : ℕ) (large : 4 ≤ grade),
    ContDiffOn ℝ ∞ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (by omega))
      (realMixedDomain parameters reference insideR (grade + 6) (realHighLarge grade))
  literal : ∀ (grade : ℕ) (large : 4 ≤ grade)
    (base : RealMixedCore parameters reference insideR) (insideS : base.1 ∈ Seed.parameterDomain),
    ChartAxisCondition (smoothingChartCore parameters base.2.2.val) →
    sourceInclusion parameters grade (by omega)
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (by omega)
        (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) base)) =
      quotientEta parameters grade (physicalFixedSliceMap parameters cellLength reference insideR base.1 insideS
        (realJointCoreToJoint parameters reference insideR base.2))
  compatible : ∀ (lower upper : ℕ) (large : 4 ≤ lower) (ordered : lower ≤ upper)
    (base : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)),
    base ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper) →
    sourceLowering parameters (by omega) ordered
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR upper (by omega) base) =
      completedRealPhysicalMixedSlice parameters cellLength reference insideR lower (by omega)
        (realMixedLowering parameters reference insideR (realHighLarge lower)
          (Nat.add_le_add_right ordered 6) base)
  derivativesCompatible : ∀ (lower upper : ℕ) (large : 4 ≤ lower) (ordered : lower ≤ upper) (order : ℕ)
    (base : RealMixedAmbient parameters reference insideR (upper + 6) (realHighLarge upper)),
    base ∈ realMixedDomain parameters reference insideR (upper + 6) (realHighLarge upper) →
    ∀ directions,
    sourceLowering parameters (by omega) ordered (iteratedFDeriv ℝ order
      (completedRealPhysicalMixedSlice parameters cellLength reference insideR upper (by omega)) base directions) =
      iteratedFDeriv ℝ order (completedRealPhysicalMixedSlice parameters cellLength reference insideR lower (by omega))
        (realMixedLowering parameters reference insideR (realHighLarge lower)
          (Nat.add_le_add_right ordered 6) base)
        (fun position => realMixedLowering parameters reference insideR (realHighLarge lower)
          (Nat.add_le_add_right ordered 6) (directions position))
  tame : PhysicalMixedDerivativeEstimate parameters cellLength reference insideR


end Grad.PhysicalCoordinates

