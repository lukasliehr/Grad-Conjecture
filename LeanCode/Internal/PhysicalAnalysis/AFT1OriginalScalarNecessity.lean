import ANU5ActualScalarSolverAdapter
import AUS2OriginalScalarDomainConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalNonexceptionalUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope
open Grad.ActualScalarForcing Grad.ActualScalarResidual Grad.ActualNonexceptionalInverse
open Grad.ActualReconstructionUniqueness Grad.ActualScalarAxis Grad.RawCircularSectors Grad.BoundedScalarInverse
variable {L sigma gamma ell : ℝ}

theorem originalRows_reconstruction (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val)
    (source : SmoothCapSource L sigma gamma ell) (rows : circularRows admissible state.val = source) :
    state.val = reconstructedState admissible state.val.1 source :=
  originalReconstruction_unique admissible state.val.1 source state excluded rfl
    (congrArg Prod.fst rows) (congrArg (fun data : SmoothCapSource L sigma gamma ell => data.2.2) rows)

theorem originalRows_determinant_residual (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val)
    (source : SmoothCapSource L sigma gamma ell) (rows : circularRows admissible state.val = source) :
    determinantResidual admissible state.val.1 source = 0 := by
  let divergence := apSmoothDiv admissible (compensatedReconstruct admissible state.val)
  have remove := scalarExcluded_removeMean admissible divergence (state_divergence_excluded admissible state.val excluded)
  have determinant : -apSmoothRemoveMean L sigma gamma ell 1 divergence = source.2.1 :=
    congrArg (fun data : SmoothCapSource L sigma gamma ell => data.2.1) rows
  have literal : -divergence = source.2.1 := (congrArg Neg.neg remove).symm.trans determinant
  have residual : divergence + source.2.1 = 0 := (congrArg (fun value => divergence + value) literal.symm).trans (add_neg_cancel divergence)
  have reconstructed := originalRows_reconstruction admissible state excluded source rows
  exact (congrArg (fun data : CompensatedData L sigma gamma ell =>
    apSmoothDiv admissible (compensatedReconstruct admissible data) + source.2.1) reconstructed).symm.trans residual

private theorem scalar_from_residual {E : Type*} [AddCommGroup E] (lap potential forcing : E)
    (zero : lap - potential + forcing = 0) : -lap + potential = forcing := by
  calc -lap + potential = forcing - (lap - potential + forcing) := by abel
       _ = forcing := by rw [zero, sub_zero]

/-- The scalar PDE is necessary for an arbitrary actual original circular
state with the specified nonexceptional rows. No scalar equation is assumed. -/
theorem originalRows_scalar_equation (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val)
    (source : SmoothCapSource L sigma gamma ell) (sourceExcluded : AvoidsExceptionalSource source)
    (rows : circularRows admissible state.val = source) (cell : ℤ) :
    fullScalarJet ((cell : ℝ) * ell / L) (apSmoothJet admissible 1 cell state.val.1) =
      apSmoothJet admissible 1 cell (scalarForcing admissible source) := by
  have thetaExcluded := (originalCircularState_scalar_conditions admissible state excluded).1
  have residualZero := originalRows_determinant_residual admissible state excluded source rows
  let project := (apSmoothJet admissible 1 cell).comp (apFullB admissible)
  have multiplierZero : project (determinantResidual admissible state.val.1 source) = 0 :=
    (congrArg project residualZero).trans (map_zero project)
  have identity := actualScalarResidualIdentity admissible state.val.1 source thetaExcluded sourceExcluded cell
  have equation := scalar_from_residual _ _ _ (identity.symm.trans multiplierZero)
  have multiplier := apFullB_jet admissible state.val.1 cell
  exact (fullScalarJet_formula _ _).trans
    ((congrArg (fun jet : ClosedJet 1 => -laplacianJet (apSmoothJet admissible 1 cell state.val.1) +
      ((((cell : ℝ) * ell / L) ^ 2 : ℝ) : ℂ) • jet) multiplier).symm.trans equation)

end Grad.OriginalNonexceptionalUniqueness
