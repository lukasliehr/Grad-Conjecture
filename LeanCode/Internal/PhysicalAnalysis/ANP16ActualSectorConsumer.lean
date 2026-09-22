import ANP15AxisConsequences

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
variable {L sigma gamma ell : ℝ}

theorem exceptionalComplement_of_excluded {E : Type*} [AddCommGroup E] [Module ℂ E]
    (projector : ℤ → E →ₗ[ℂ] E) (field : E)
    (excluded : ∀ mode, IsExceptionalRaw mode → projector mode field = 0) :
    exceptionalComplement projector field = field := by
  change field - (projector 0 field + projector 2 field + projector (-2) field) = field
  rw [excluded 0 (Or.inl rfl), excluded 2 (Or.inr (Or.inl rfl)), excluded (-2) (Or.inr (Or.inr rfl))]
  simp only [add_zero, sub_zero]

theorem rawSourceComplement_idempotent (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) :
    rawSourceComplement L sigma gamma ell (rawSourceComplement L sigma gamma ell source) =
      rawSourceComplement L sigma gamma ell source :=
  exceptionalComplement_of_excluded _ _ (rawSourceComplement_avoids admissible source)

theorem rawStateComplement_idempotent (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) :
    rawStateComplement L sigma gamma ell (rawStateComplement L sigma gamma ell state) =
      rawStateComplement L sigma gamma ell state :=
  exceptionalComplement_of_excluded _ _ (rawStateComplement_avoids admissible state)

theorem rawSourceComplement_force_firstJet (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible) :
    APSmoothAxisFirstJetZero admissible (rawSourceComplement L sigma gamma ell source).1 := by
  apply apSmoothAxisFirstJetZero_of_closed
  intro cell
  have actual := Grad.ActualMeanInverse.actualSource_conditions admissible _
    (rawSourceComplement_preserves admissible source compatible)
  exact ⟨actual.1.2.1 cell, exceptionalSource_force_partial_zero admissible _
    (rawSourceComplement_avoids admissible source) cell⟩

/-- The exact source split on SmoothCapSource. Each selected mode preserves
AM9 and the original all-grade norm. Its literal complement removes precisely
the raw sectors 0, +2 and -2 and carries the derived force Taylor condition. -/
theorem actualRawSourceDecomposition (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible) :
    (∀ mode : ℤ, rawSourceProjector L sigma gamma ell mode source ∈ smoothCapSourceCore admissible ∧
      IsRawSourceSector admissible mode (rawSourceProjector L sigma gamma ell mode source) ∧
      ∀ grade : ℕ, ‖capSourceGrade grade (rawSourceProjector L sigma gamma ell mode source)‖ ≤
        rawSourceBoundConstant grade * ‖capSourceGrade grade source‖) ∧
    rawSourceComplement L sigma gamma ell source ∈ smoothCapSourceCore admissible ∧
    AvoidsExceptionalSource (rawSourceComplement L sigma gamma ell source) ∧
    APSmoothAxisFirstJetZero admissible (rawSourceComplement L sigma gamma ell source).1 ∧
    (∀ grade : ℕ, ‖capSourceGrade grade (rawSourceComplement L sigma gamma ell source)‖ ≤
      (1 + 3 * rawSourceBoundConstant grade) * ‖capSourceGrade grade source‖) ∧
    rawSourceProjector L sigma gamma ell 0 source + rawSourceProjector L sigma gamma ell 2 source +
      rawSourceProjector L sigma gamma ell (-2) source + rawSourceComplement L sigma gamma ell source = source :=
  ⟨fun mode => ⟨rawSourceProjector_preserves admissible mode source compatible,
      rawSourceProjector_sector admissible mode source, rawSourceProjector_bound mode source⟩,
    rawSourceComplement_preserves admissible source compatible, rawSourceComplement_avoids admissible source,
    rawSourceComplement_force_firstJet admissible source compatible,
    rawSourceComplement_bound source, rawSource_decomposition source⟩

/-- The matching exact split on the original compensated domain, preserving
both gauges, the genuine reconstructed axis jet and the five native AN8 slots. -/
theorem actualRawStateDecomposition (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (member : state ∈ circularCompensatedCore admissible) :
    (∀ mode : ℤ, rawStateProjector L sigma gamma ell mode state ∈ circularCompensatedCore admissible ∧
      IsRawStateSector admissible mode (rawStateProjector L sigma gamma ell mode state) ∧
      ∀ grade : ℕ, compensatedNorm admissible grade (rawStateProjector L sigma gamma ell mode state) ≤
        rawStateBoundConstant grade * compensatedNorm admissible grade state) ∧
    rawStateComplement L sigma gamma ell state ∈ circularCompensatedCore admissible ∧
    AvoidsExceptionalState (rawStateComplement L sigma gamma ell state) ∧
    (∀ grade : ℕ, compensatedNorm admissible grade (rawStateComplement L sigma gamma ell state) ≤
      (1 + 3 * rawStateBoundConstant grade) * compensatedNorm admissible grade state) ∧
    rawStateProjector L sigma gamma ell 0 state + rawStateProjector L sigma gamma ell 2 state +
      rawStateProjector L sigma gamma ell (-2) state + rawStateComplement L sigma gamma ell state = state :=
  ⟨fun mode => ⟨rawStateProjector_preserves admissible mode state member,
      rawStateProjector_sector admissible mode state, rawStateProjector_bound admissible mode state⟩,
    rawStateComplement_preserves admissible state member, rawStateComplement_avoids admissible state,
    rawStateComplement_bound admissible state, rawState_decomposition state⟩

end Grad.RawCircularSectors
