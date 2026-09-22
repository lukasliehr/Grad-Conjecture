import ANP9ActualStateProjection

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
variable {L sigma gamma ell : ℝ}

theorem apSmoothRawVector_projection (admissible : Admissible L sigma gamma ell)
    (first second : ℤ) (field : APSmooth L sigma gamma ell 2) :
    apSmoothRawVector L sigma gamma ell first (apSmoothRawVector L sigma gamma ell second field) =
      if first = second then apSmoothRawVector L sigma gamma ell first field else 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have composed := (apSmoothRawVector_jet admissible first _ cell).trans
    ((congrArg (rawVectorJet first) (apSmoothRawVector_jet admissible second field cell)).trans
      (rawVectorJet_projection first second _))
  split_ifs with same
  · exact composed.trans ((if_pos same).trans (apSmoothRawVector_jet admissible first field cell).symm)
  · exact composed.trans ((if_neg same).trans (map_zero (apSmoothJet admissible 2 cell)).symm)

theorem rawStoredJet_projection (first second : ℤ) (field : ClosedJet 3) :
    rawStoredJet first (rawStoredJet second field) = if first = second then rawStoredJet first field else 0 := by
  apply storedJet_joint_injective
  · rw [rawStoredJet_planar, rawStoredJet_planar, rawVectorJet_projection]
    split_ifs <;> simp only [rawStoredJet_planar, valueMapJet_map_zero]
  · rw [rawStoredJet_scalar, rawStoredJet_scalar, angularClosedJet_projection]
    split_ifs <;> simp only [rawStoredJet_scalar, valueMapJet_map_zero]

theorem apSmoothRawStored_projection (admissible : Admissible L sigma gamma ell)
    (first second : ℤ) (field : APSmooth L sigma gamma ell 3) :
    apSmoothRawStored L sigma gamma ell first (apSmoothRawStored L sigma gamma ell second field) =
      if first = second then apSmoothRawStored L sigma gamma ell first field else 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have composed := (apSmoothRawStored_jet admissible first _ cell).trans
    ((congrArg (rawStoredJet first) (apSmoothRawStored_jet admissible second field cell)).trans
      (rawStoredJet_projection first second _))
  split_ifs with same
  · exact composed.trans ((if_pos same).trans (apSmoothRawStored_jet admissible first field cell).symm)
  · exact composed.trans ((if_neg same).trans (map_zero (apSmoothJet admissible 3 cell)).symm)

private theorem pair_conditional {E F : Type*} [Zero E] [Zero F] (condition : Prop) [Decidable condition]
    (first : E) (second : F) :
    (if condition then first else 0, if condition then second else 0) =
      if condition then (first, second) else 0 := by split_ifs <;> rfl

theorem rawSourceProjector_projection (admissible : Admissible L sigma gamma ell)
    (first second : ℤ) (source : SmoothCapSource L sigma gamma ell) :
    rawSourceProjector L sigma gamma ell first (rawSourceProjector L sigma gamma ell second source) =
      if first = second then rawSourceProjector L sigma gamma ell first source else 0 := by
  have scalar := (congrArg₂ Prod.mk (apSmoothAngularMode_projection admissible first second source.2.1)
    (apSmoothAngularMode_projection admissible first second source.2.2)).trans
      (pair_conditional (first = second) _ _)
  exact (congrArg₂ Prod.mk (apSmoothRawVector_projection admissible first second source.1) scalar).trans
    (pair_conditional (first = second) _ _)

theorem rawStateProjector_projection (admissible : Admissible L sigma gamma ell)
    (first second : ℤ) (state : CompensatedData L sigma gamma ell) :
    rawStateProjector L sigma gamma ell first (rawStateProjector L sigma gamma ell second state) =
      if first = second then rawStateProjector L sigma gamma ell first state else 0 := by
  exact (congrArg₂ Prod.mk (apSmoothAngularMode_projection admissible first second state.1)
    (apSmoothRawStored_projection admissible first second state.2)).trans
      (pair_conditional (first = second) _ _)

/-- The three exceptional raw sectors, including the mean. -/
def IsExceptionalRaw (mode : ℤ) : Prop := mode = 0 ∨ mode = 2 ∨ mode = -2

def exceptionalComplement {E : Type*} [AddCommGroup E] [Module ℂ E]
    (projector : ℤ → E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  LinearMap.id - (projector 0 + projector 2 + projector (-2))

theorem exceptionalComplement_excludes {E : Type*} [AddCommGroup E] [Module ℂ E]
    (projector : ℤ → E →ₗ[ℂ] E)
    (orthogonal : ∀ first second field, projector first (projector second field) =
      if first = second then projector first field else 0)
    (mode : ℤ) (exceptional : IsExceptionalRaw mode) (field : E) :
    projector mode (exceptionalComplement projector field) = 0 := by
  change projector mode (field - (projector 0 field + projector 2 field + projector (-2) field)) = 0
  rw [map_sub, map_add, map_add, orthogonal, orthogonal, orthogonal]
  rcases exceptional with rfl | rfl | rfl <;> norm_num

theorem exceptionalComplement_sum {E : Type*} [AddCommGroup E] [Module ℂ E]
    (projector : ℤ → E →ₗ[ℂ] E) (field : E) :
    projector 0 field + projector 2 field + projector (-2) field + exceptionalComplement projector field = field := by
  change projector 0 field + projector 2 field + projector (-2) field +
    (field - (projector 0 field + projector 2 field + projector (-2) field)) = field
  abel

def rawSourceComplement (L sigma gamma ell : ℝ) :
    SmoothCapSource L sigma gamma ell →ₗ[ℂ] SmoothCapSource L sigma gamma ell :=
  exceptionalComplement (rawSourceProjector L sigma gamma ell)

def rawStateComplement (L sigma gamma ell : ℝ) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] CompensatedData L sigma gamma ell :=
  exceptionalComplement (rawStateProjector L sigma gamma ell)

theorem rawSourceComplement_excludes (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (exceptional : IsExceptionalRaw mode) (source : SmoothCapSource L sigma gamma ell) :
    rawSourceProjector L sigma gamma ell mode (rawSourceComplement L sigma gamma ell source) = 0 :=
  exceptionalComplement_excludes _ (rawSourceProjector_projection admissible) mode exceptional source

theorem rawStateComplement_excludes (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (exceptional : IsExceptionalRaw mode) (state : CompensatedData L sigma gamma ell) :
    rawStateProjector L sigma gamma ell mode (rawStateComplement L sigma gamma ell state) = 0 :=
  exceptionalComplement_excludes _ (rawStateProjector_projection admissible) mode exceptional state

theorem rawSource_decomposition (source : SmoothCapSource L sigma gamma ell) :
    rawSourceProjector L sigma gamma ell 0 source + rawSourceProjector L sigma gamma ell 2 source +
      rawSourceProjector L sigma gamma ell (-2) source + rawSourceComplement L sigma gamma ell source = source :=
  exceptionalComplement_sum _ source

theorem rawState_decomposition (state : CompensatedData L sigma gamma ell) :
    rawStateProjector L sigma gamma ell 0 state + rawStateProjector L sigma gamma ell 2 state +
      rawStateProjector L sigma gamma ell (-2) state + rawStateComplement L sigma gamma ell state = state :=
  exceptionalComplement_sum _ state

theorem rawSourceComplement_preserves (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (member : source ∈ smoothCapSourceCore admissible) :
    rawSourceComplement L sigma gamma ell source ∈ smoothCapSourceCore admissible :=
  (smoothCapSourceCore admissible).sub_mem member ((smoothCapSourceCore admissible).add_mem
    ((smoothCapSourceCore admissible).add_mem (rawSourceProjector_preserves admissible 0 source member)
      (rawSourceProjector_preserves admissible 2 source member))
        (rawSourceProjector_preserves admissible (-2) source member))

theorem rawStateComplement_preserves (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (member : state ∈ circularCompensatedCore admissible) :
    rawStateComplement L sigma gamma ell state ∈ circularCompensatedCore admissible :=
  (circularCompensatedCore admissible).sub_mem member ((circularCompensatedCore admissible).add_mem
    ((circularCompensatedCore admissible).add_mem (rawStateProjector_preserves admissible 0 state member)
      (rawStateProjector_preserves admissible 2 state member))
        (rawStateProjector_preserves admissible (-2) state member))

end Grad.RawCircularSectors
