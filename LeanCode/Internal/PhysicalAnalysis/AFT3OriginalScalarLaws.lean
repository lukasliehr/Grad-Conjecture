import AFT2OriginalRobinNecessity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalNonexceptionalUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.BoundaryTrace Grad.CircularHighWeak Grad.ActualSmoothRobin Grad.CircularNormalLift
open Grad.InhomogeneousHighRobin Grad.OrdinaryDiskCalculus
open Grad.ActualScalarForcing Grad.ActualNonexceptionalInverse
open Grad.ActualReferenceAssembly Grad.ActualForcingSupport Grad.ActualScalarAxis Grad.RawCircularSectors Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

theorem normalBoundary_all_coefficients (grade : ℕ) (field : normalBoundaryGrade (grade + 2)) (pair : ℤ × ℤ) :
    apBoundaryCoefficient 1 0 0 1 (grade + 1) field.val pair =
      if pair.2 = 0 then normalBoundaryCoefficient (grade + 2) field pair.1 else 0 := by
  by_cases zero : pair.2 = 0
  · have same : pair = (pair.1, 0) := Prod.ext rfl zero
    rw [same, if_pos rfl]
    rfl
  · rw [if_neg zero]
    change (apBoundaryWeight 1 0 0 1 (grade + 1) pair : ℂ)⁻¹ • field.val pair = 0
    rw [normalBoundary_cell_zero (grade + 2) field pair.1 pair.2 zero, smul_zero]

/-- Equality of every literal physical Robin coefficient implies equality in
the actual completed trace carrier used by the accepted scalar inverse. -/
theorem scalarRobin_trace_of_coefficients (admissible : Admissible L sigma gamma ell)
    (boundary : BandSmoothBoundary L sigma gamma ell) (cell : ℤ) (field : ClosedJet 1) (grade : ℕ)
    (coefficients : ∀ mode : ℤ, fourierCoeff (fun angle : CellCircle =>
      (robinResidualJet field).value (boundaryDiskPoint angle)) mode =
        apBoundaryCoefficient L sigma gamma ell (grade + 1) (boundary.grade grade) (mode, cell)) :
    ordinaryRobinTrace grade (unitDiskCoreInto (grade + 2) field) = ((smoothBoundaryCell admissible boundary cell).grade grade).val := by
  apply originalBoundary_ext (grade + 1)
  intro pair
  have first := (congrArg (fun value => apBoundaryCoefficient 1 0 0 1 (grade + 1) value pair)
    (ordinaryRobinTrace_core grade field)).trans
      (ordinaryBoundaryTrace_core_coefficient (grade + 1) (by omega) (robinResidualJet field) pair)
  have second := normalBoundary_all_coefficients grade ((smoothBoundaryCell admissible boundary cell).grade grade) pair
  by_cases zero : pair.2 = 0
  · exact first.trans ((if_pos zero).trans ((coefficients pair.1).trans
      ((smoothBoundaryCell_coefficient admissible boundary cell grade pair.1).symm.trans
        ((if_pos zero).symm.trans second.symm))))
  · exact first.trans ((if_neg zero).trans ((if_neg zero).symm.trans second.symm))

/-- All exact scalar laws follow from an arbitrary original nonexceptional
state and its original rows/boundary. No scalar law is an input hypothesis. -/
theorem originalState_scalar_laws (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val)
    (source : SmoothCapSource L sigma gamma ell) (sourceExcluded : AvoidsExceptionalSource source)
    (rows : circularRows admissible state.val = source) (beta : BandSmoothBoundary L sigma gamma ell)
    (boundary : ∀ grade : ℕ, circularCoreTrace admissible grade state.val = beta.grade grade) :
    IsOriginalScalarSolution admissible (scalarForcing admissible source) (forcedBoundary admissible source beta) state.val.1 := by
  intro cell
  have conditions := originalCircularState_scalar_conditions admissible state excluded
  refine ⟨⟨conditions.1 cell 0 (Or.inl rfl), conditions.1 cell 2 (Or.inr (Or.inl rfl)),
    conditions.1 cell (-2) (Or.inr (Or.inr rfl))⟩,
    originalRows_scalar_equation admissible state excluded source sourceExcluded rows cell,
    conditions.2 cell, ?_⟩
  intro grade
  exact scalarRobin_trace_of_coefficients admissible (forcedBoundary admissible source beta) cell _ grade
    (fun mode => originalRows_robin_coefficient admissible state excluded source sourceExcluded rows beta boundary cell mode grade)

end Grad.OriginalNonexceptionalUniqueness
