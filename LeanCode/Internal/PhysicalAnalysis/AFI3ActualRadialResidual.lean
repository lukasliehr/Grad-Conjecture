import AFI2ActualBoundaryMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.GaugeCoefficients.Envelope Grad.BoundaryTrace Grad.CircularHighWeak
open Grad.ActualScalarForcing Grad.ActualScalarResidual Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

private theorem radial_split_algebra {E V : Type*} [AddCommGroup E] [AddCommGroup V]
    [Module ℂ E] [Module ℂ V] (radial : V →ₗ[ℂ] E) (whole first second third : V)
    (split : whole = first + second + third) (zero : radial third = 0) :
    radial whole = radial first + radial second := by
  rw [split, map_add, map_add, zero, add_zero]

theorem actualReconstruction_radial_split (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) :
    apSmoothRadial admissible (compensatedReconstruct admissible (reconstructedState admissible theta source)) =
      apSmoothRadial admissible (homogeneousLift admissible theta source) + forceRadial admissible source.1 :=
  radial_split_algebra (apSmoothRadial admissible) _ _ _ _
    (actualReconstruction_split admissible theta source) (radial_toroidalLift admissible _)

/-- The original radial reconstruction satisfies the literal full-B Robin
identity on the whole closed disk, including the center modes. -/
theorem actualRadialResidualIdentity (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (cell : ℤ) :
    apSmoothJet admissible 1 cell (apFullB admissible
      (apSmoothRadial admissible (compensatedReconstruct admissible (reconstructedState admissible theta source)))) =
      (eulerJet (apSmoothJet admissible 1 cell theta) + (2 : ℂ) • apSmoothJet admissible 1 cell theta) +
        apSmoothJet admissible 1 cell (apFullB admissible (forceRadial admissible source.1)) := by
  let project := (apSmoothJet admissible 1 cell).comp (apFullB admissible)
  exact (congrArg project (actualReconstruction_radial_split admissible theta source)).trans
    ((project.map_add _ _).trans (congrArg (fun jet : ClosedJet 1 => jet +
      apSmoothJet admissible 1 cell (apFullB admissible (forceRadial admissible source.1)))
        (actualReconstructedElimination admissible theta source thetaExcluded sourceExcluded cell).2))

/-- High projection can be cancelled through the original boundary B. -/
theorem originalHighTrace_B (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (field : APSmooth L sigma gamma ell 1) :
    boundaryB L sigma gamma ell (grade + 1)
      (apHighTrace L sigma gamma ell (grade + 1) (by omega) (apSmoothGrade L sigma gamma ell 1 (grade + 1) field)) =
    apHighTrace L sigma gamma ell (grade + 1) (by omega)
      (apSmoothGrade L sigma gamma ell 1 (grade + 1) (apFullB admissible field)) :=
  (boundaryB_highProjection (grade + 1) _).trans (fullB_highTrace admissible (grade + 1) (by omega) field).symm

/-- Physical Fourier coefficient identity for the actual original circular
boundary row, at every positive trace grade. -/
theorem actualCircularTrace_B_coefficient (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (pair : ℤ × ℤ) (high : 3 ≤ |pair.1|) :
    apBoundaryCoefficient L sigma gamma ell (grade + 1)
      (boundaryB L sigma gamma ell (grade + 1) (circularCoreTrace admissible grade (reconstructedState admissible theta source))) pair =
      (angularClosedJet pair.1 (eulerJet (apSmoothJet admissible 1 pair.2 theta) + (2 : ℂ) • apSmoothJet admissible 1 pair.2 theta)).value (boundaryDiskPoint 0) +
        (highMultiplier pair.1 : ℂ) •
          (angularClosedJet pair.1 (apSmoothJet admissible 1 pair.2 (forceRadial admissible source.1))).value (boundaryDiskPoint 0) := by
  let radial := apSmoothRadial admissible (compensatedReconstruct admissible (reconstructedState admissible theta source))
  have boundary := congrArg (fun field : APBoundaryGrade L sigma gamma ell 1 (grade + 1) =>
    apBoundaryCoefficient L sigma gamma ell (grade + 1) field pair) (originalHighTrace_B admissible grade radial)
  have projected := apHighProjection_coefficient L sigma gamma ell (grade + 1)
    (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega) (apSmoothGrade L sigma gamma ell 1 (grade + 1) (apFullB admissible radial))) pair
  rw [if_pos high] at projected
  have physical := originalSmoothTrace_coefficient admissible (grade + 1) (by omega) (apFullB admissible radial) pair
  have residual := congrArg (fun jet : ClosedJet 1 => (angularClosedJet pair.1 jet).value (boundaryDiskPoint 0))
    (actualRadialResidualIdentity admissible theta source thetaExcluded sourceExcluded pair.2)
  have modeNonzero : pair.1 ≠ 0 := by intro zero; rw [zero] at high; norm_num at high
  have forcing := (congrArg (angularClosedJet pair.1) (apFullB_jet admissible (forceRadial admissible source.1) pair.2)).trans
    ((literalMultiplier_coefficient pair.1 _).trans (if_neg modeNonzero))
  have evaluated := congrArg (fun jet : ClosedJet 1 => jet.value (boundaryDiskPoint 0)) forcing
  have scalar := congrArg (fun coefficient : ℂ => coefficient •
    (angularClosedJet pair.1 (apSmoothJet admissible 1 pair.2 (forceRadial admissible source.1))).value (boundaryDiskPoint 0))
      (highMultiplier_complex pair.1 high).symm
  have final := evaluated.trans scalar
  have expansion (first second : ClosedJet 1) :
      (angularClosedJet pair.1 (first + second)).value (boundaryDiskPoint 0) =
        (angularClosedJet pair.1 first).value (boundaryDiskPoint 0) +
          (angularClosedJet pair.1 second).value (boundaryDiskPoint 0) := by
    rw [angularClosedJet_add]
    rfl
  exact boundary.trans (projected.trans (physical.trans (residual.trans ((expansion _ _).trans
    (congrArg (fun value =>
      (angularClosedJet pair.1 (eulerJet (apSmoothJet admissible 1 pair.2 theta) +
        (2 : ℂ) • apSmoothJet admissible 1 pair.2 theta)).value (boundaryDiskPoint 0) + value) final)))))

end Grad.ActualReferenceAssembly
