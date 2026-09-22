import AFY7ActualStrongConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 150000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

/-- Q kills the literal completed angular mean, at the original trace grade. -/
theorem apHighTrace_angularMean_zero (L sigma gamma ell : ℝ) (grade : ℕ) (positive : 1 ≤ grade)
    (field : apGrade L sigma gamma ell 1 grade) :
    apHighTrace L sigma gamma ell grade positive (apAngularMean L sigma gamma ell 1 grade field) = 0 := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := 1) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((apHighTrace L sigma gamma ell grade positive).continuous.comp
      (apAngularMean L sigma gamma ell 1 grade).continuous) continuous_const) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apAngularMean_core]
  apply lp.ext
  funext mode
  have coefficient : apBoundaryCoefficient L sigma gamma ell grade
      (apHighTrace L sigma gamma ell grade positive
        (apFiniteInto L sigma gamma ell (apFiniteJetMap (angularClosedJetLinear 1 0) core))) mode = 0 := by
    change apBoundaryCoefficient L sigma gamma ell grade
      (apHighProjection L sigma gamma ell grade
        (apBoundaryTrace L sigma gamma ell grade positive
          (apFiniteInto L sigma gamma ell (apFiniteJetMap (angularClosedJetLinear 1 0) core)))) mode = 0
    rw [apHighProjection_coefficient, apBoundaryTrace_coefficient]
    split_ifs with high
    · change fourierCoeff (fun angle : CellCircle =>
        (angularClosedJet 0 (core mode.2)).value (boundaryDiskPoint angle)) mode.1 = 0
      have nonzero : mode.1 ≠ 0 := by intro zero; simp [zero] at high
      rw [boundaryCoefficient_angular, angularClosedJet_projection, if_neg nonzero]
      rfl
    · rfl
  have weighted := apBoundary_weighted_coefficient L sigma gamma ell grade
    (apHighTrace L sigma gamma ell grade positive
      (apFiniteInto L sigma gamma ell (apFiniteJetMap (angularClosedJetLinear 1 0) core))) mode
  exact weighted.symm.trans ((congrArg (fun value : ComplexEuclidean 1 =>
    (apBoundaryWeight L sigma gamma ell grade mode : ℂ) • value) coefficient).trans (smul_zero _))

/-- The high trace of the actual P=I-Pi primitive is its high unprojected trace. -/
theorem apHighTrace_meanFree (L sigma gamma ell : ℝ) (grade : ℕ) (positive : 1 ≤ grade)
    (field : apGrade L sigma gamma ell 1 grade) :
    apHighTrace L sigma gamma ell grade positive (apMeanFree L sigma gamma ell 1 grade field) =
      apHighTrace L sigma gamma ell grade positive field := by
  have subtraction := (apHighTrace L sigma gamma ell grade positive).map_sub field
    (apAngularMean L sigma gamma ell 1 grade field)
  exact subtraction.trans ((congrArg (fun mean : APBoundaryGrade L sigma gamma ell 1 grade =>
    apHighTrace L sigma gamma ell grade positive field - mean)
    (apHighTrace_angularMean_zero L sigma gamma ell grade positive field)).trans (sub_zero _))

theorem completedNormalTrace_high {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    apHighProjection L sigma gamma ell (grade + 1) (completedNormalTrace admissible data grade core field) =
      completedNormalTrace admissible data grade core field :=
  apHighProjection_idempotent L sigma gamma ell (grade + 1)
    (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
      (apMultiplier admissible (normalRowFamily data (grade + 1)) (completedReconstruct admissible grade core field)))

end Grad.GaugeCoefficients.Physical.Compensated
