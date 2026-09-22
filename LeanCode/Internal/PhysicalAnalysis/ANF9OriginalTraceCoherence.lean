import ANF8ActualScalarResidual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarForcing
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.BoundaryTrace Grad.CircularHighWeak
variable {L sigma gamma ell : ℝ}

/-- Coefficients of the original completed AP trace commute with grade
lowering, including grade one. Proved by the existing dense finite core. -/
theorem originalTrace_lowering_coefficient (low high : ℕ) (lowPositive : 1 ≤ low) (highPositive : 1 ≤ high)
    (ordered : low ≤ high) (field : apGrade L sigma gamma ell 1 high) (pair : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell low
      (apBoundaryTrace L sigma gamma ell low lowPositive (apLowering L sigma gamma ell ordered field)) pair =
    apBoundaryCoefficient L sigma gamma ell high (apBoundaryTrace L sigma gamma ell high highPositive field) pair := by
  let first : apGrade L sigma gamma ell 1 high →L[ℂ] ComplexEuclidean 1 := ((apBoundaryCoefficientCLM L sigma gamma ell low pair).comp
    (apBoundaryTrace L sigma gamma ell low lowPositive)).comp (apLowering L sigma gamma ell ordered)
  let second : apGrade L sigma gamma ell 1 high →L[ℂ] ComplexEuclidean 1 := (apBoundaryCoefficientCLM L sigma gamma ell high pair).comp
    (apBoundaryTrace L sigma gamma ell high highPositive)
  have same : first = second := by
    apply apFiniteGenerator_ext L sigma gamma ell
    intro cell core
    change apBoundaryCoefficient L sigma gamma ell low
      (apBoundaryTrace L sigma gamma ell low lowPositive
        (apLowering L sigma gamma ell ordered (apFiniteInto L sigma gamma ell (Finsupp.single cell core)))) pair =
      apBoundaryCoefficient L sigma gamma ell high
        (apBoundaryTrace L sigma gamma ell high highPositive (apFiniteInto L sigma gamma ell (Finsupp.single cell core))) pair
    rw [apLowering_core, apBoundaryTrace_coefficient, apBoundaryTrace_coefficient]
  exact congrArg (fun mapping : apGrade L sigma gamma ell 1 high →L[ℂ] ComplexEuclidean 1 => mapping field) same

/-- Literal endpoint coefficient at every positive original trace grade,
including the H^(1/2) grade used by the common smooth boundary carrier. -/
theorem originalSmoothTrace_coefficient (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (positive : 1 ≤ grade) (field : APSmooth L sigma gamma ell 1) (pair : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade
      (apBoundaryTrace L sigma gamma ell grade positive (apSmoothGrade L sigma gamma ell 1 grade field)) pair =
      (angularClosedJet pair.1 (apSmoothJet admissible 1 pair.2 field)).value (boundaryDiskPoint 0) := by
  have lowering := originalTrace_lowering_coefficient (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
    grade (grade + 2) positive (by omega) (by omega) (apSmoothGrade L sigma gamma ell 1 (grade + 2) field) pair
  have coherent := field.property grade (grade + 2) (by omega)
  have low := congrArg (fun value : apGrade L sigma gamma ell 1 grade => apBoundaryCoefficient L sigma gamma ell grade
    (apBoundaryTrace L sigma gamma ell grade positive value) pair) coherent
  have literal := apBoundaryTrace_literal admissible (by omega : 2 ≤ grade + 2)
    (apSmoothGrade L sigma gamma ell 1 (grade + 2) field) pair
  have trace : apTrace admissible (by omega : 2 ≤ grade + 2) pair.2
      (apSmoothGrade L sigma gamma ell 1 (grade + 2) field) = (apSmoothJet admissible 1 pair.2 field).value :=
    (apSmoothJet_value_trace admissible (by omega : 2 ≤ grade + 2) field pair.2).symm
  rw [trace, boundaryCoefficient_angular] at literal
  exact low.symm.trans (lowering.trans literal)

theorem boundaryForcing_literal_coefficient (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (source : SmoothCapSource L sigma gamma ell) (beta : APBoundaryGrade L sigma gamma ell 1 (grade + 1))
    (pair : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell (grade + 1) (boundaryForcing admissible grade source beta) pair =
      (highMultiplier pair.1 : ℂ) •
        (apBoundaryCoefficient L sigma gamma ell (grade + 1) beta pair -
          (angularClosedJet pair.1 (apSmoothJet admissible 1 pair.2 (forceRadial admissible source.1))).value (boundaryDiskPoint 0)) := by
  let trace := apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
    (apSmoothGrade L sigma gamma ell 1 (grade + 1) (forceRadial admissible source.1))
  have subtraction := (apBoundaryCoefficientCLM L sigma gamma ell (grade + 1) pair).map_sub beta trace
  have literal := originalSmoothTrace_coefficient admissible (grade + 1) (by omega) (forceRadial admissible source.1) pair
  exact (boundaryB_coefficient (grade + 1) (beta - trace) pair).trans
    (congrArg (fun value : ComplexEuclidean 1 => (highMultiplier pair.1 : ℂ) • value)
      (subtraction.trans (congrArg (fun value : ComplexEuclidean 1 =>
        apBoundaryCoefficient L sigma gamma ell (grade + 1) beta pair - value) literal)))

theorem boundaryForcing_coherent (admissible : Admissible L sigma gamma ell) (low high : ℕ)
    (source : SmoothCapSource L sigma gamma ell)
    (first : APBoundaryGrade L sigma gamma ell 1 (low + 1))
    (second : APBoundaryGrade L sigma gamma ell 1 (high + 1))
    (coherent : ∀ pair : ℤ × ℤ, apBoundaryCoefficient L sigma gamma ell (low + 1) first pair =
      apBoundaryCoefficient L sigma gamma ell (high + 1) second pair) (pair : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell (low + 1) (boundaryForcing admissible low source first) pair =
      apBoundaryCoefficient L sigma gamma ell (high + 1) (boundaryForcing admissible high source second) pair := by
  rw [boundaryForcing_literal_coefficient, boundaryForcing_literal_coefficient, coherent pair]

end Grad.ActualScalarForcing
