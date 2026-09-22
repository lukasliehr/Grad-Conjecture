import ANF7ActualReconstructionSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarForcing
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

def determinantResidual (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  apSmoothDiv admissible (compensatedReconstruct admissible (reconstructedState admissible theta source)) + source.2.1

private theorem B_residual_algebra {E : Type*} [AddCommGroup E] [Module ℂ E]
    (B : E →ₗ[ℂ] E) (total hom force axial extra G : E)
    (split : total = hom + force + axial + extra) :
    B (total + G) = B hom + B axial + B (G + force + extra) := by
  rw [split, map_add, map_add, map_add, map_add, map_add, map_add]
  abel

theorem determinantResidual_B_split (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) :
    apFullB admissible (determinantResidual admissible theta source) =
      apFullB admissible (apSmoothDiv admissible (homogeneousLift admissible theta source)) +
        apFullB admissible (apSmoothAxial L sigma gamma ell 1 (apSmoothAxial L sigma gamma ell 1 theta)) +
        scalarForcing admissible source :=
  B_residual_algebra (apFullB admissible) _ _ _ _ _ source.2.1 (actualReconstruction_div_split admissible theta source)

theorem axialSquared_B_jet (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apFullB admissible
      (apSmoothAxial L sigma gamma ell 1 (apSmoothAxial L sigma gamma ell 1 theta))) =
      (seedScaledFrequency L ell cell * seedScaledFrequency L ell cell) •
        apSmoothJet admissible 1 cell (apFullB admissible theta) := by
  let jet := apSmoothJet admissible 1 cell
  let B : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 :=
    LinearMap.id + (4 : ℂ) • (shiftInverseLinear 1 0).comp (shiftInverseLinear 1 0)
  have twice : jet (apSmoothAxial L sigma gamma ell 1 (apSmoothAxial L sigma gamma ell 1 theta)) =
      (seedScaledFrequency L ell cell * seedScaledFrequency L ell cell) • jet theta :=
    (apSmoothAxial_jet admissible (apSmoothAxial L sigma gamma ell 1 theta) cell).trans
      ((congrArg (fun value : ClosedJet 1 => seedScaledFrequency L ell cell • value)
        (apSmoothAxial_jet admissible theta cell)).trans (smul_smul _ _ _))
  exact (apFullB_jet admissible _ cell).trans
    ((congrArg B twice).trans ((B.map_smul _ (jet theta)).trans
      (congrArg (fun value : ClosedJet 1 => (seedScaledFrequency L ell cell * seedScaledFrequency L ell cell) • value)
        (apFullB_jet admissible theta cell).symm)))

theorem seedFrequency_square (L ell : ℝ) (cell : ℤ) :
    seedScaledFrequency L ell cell * seedScaledFrequency L ell cell =
      -(((cell : ℝ) * ell / L) ^ 2 : ℝ) := by
  unfold seedScaledFrequency
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- Exact AN15 residual identity on every actual original cell. -/
theorem actualScalarResidualIdentity (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (cell : ℤ) :
    apSmoothJet admissible 1 cell (apFullB admissible (determinantResidual admissible theta source)) =
      laplacianJet (apSmoothJet admissible 1 cell theta) -
        ((((cell : ℝ) * ell / L) ^ 2 : ℝ) : ℂ) • apSmoothJet admissible 1 cell (apFullB admissible theta) +
          apSmoothJet admissible 1 cell (scalarForcing admissible source) := by
  let jet := apSmoothJet admissible 1 cell
  have hom := (actualReconstructedElimination admissible theta source thetaExcluded sourceExcluded cell).1
  have axial : jet (apFullB admissible (apSmoothAxial L sigma gamma ell 1 (apSmoothAxial L sigma gamma ell 1 theta))) =
      -(((((cell : ℝ) * ell / L) ^ 2 : ℝ) : ℂ) • jet (apFullB admissible theta)) :=
    (axialSquared_B_jet admissible theta cell).trans
      ((congrArg (fun coefficient : ℂ => coefficient • jet (apFullB admissible theta))
        (seedFrequency_square L ell cell)).trans (neg_smul _ _))
  have expanded := (congrArg jet (determinantResidual_B_split admissible theta source)).trans
    ((jet.map_add _ _).trans (congrArg (fun value : ClosedJet 1 => value + jet (scalarForcing admissible source))
      (jet.map_add _ _)))
  exact expanded.trans ((congrArg (fun value : ClosedJet 1 => value + jet (scalarForcing admissible source))
    (congrArg₂ (fun a b : ClosedJet 1 => a + b) hom axial)).trans (by rw [sub_eq_add_neg]))

private theorem residual_zero_algebra {E : Type*} [AddCommGroup E] (lap potential force : E)
    (equation : -lap + potential = force) : lap - potential + force = 0 := by
  rw [← equation]
  abel

theorem scalarEquation_annihilates_actualResidual (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (equation : ∀ cell : ℤ,
      -laplacianJet (apSmoothJet admissible 1 cell theta) +
        ((((cell : ℝ) * ell / L) ^ 2 : ℝ) : ℂ) • apSmoothJet admissible 1 cell (apFullB admissible theta) =
          apSmoothJet admissible 1 cell (scalarForcing admissible source)) :
    apFullB admissible (determinantResidual admissible theta source) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (actualScalarResidualIdentity admissible theta source thetaExcluded sourceExcluded cell).trans
    ((residual_zero_algebra _ _ _ (equation cell)).trans (map_zero _).symm)

end Grad.ActualScalarForcing
