import AFL1OriginalRowCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
namespace Grad.FullReferenceUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.ActualScalarForcing Grad.ActualReferenceAssembly Grad.BoundedScalarInverse
open Grad.BoundaryTrace Grad.CircularHighWeak
variable {L sigma gamma ell : ℝ}

theorem circularTrace_literal_coefficient (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (grade : ℕ) (pair : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell (grade + 1) (circularCoreTrace admissible grade state) pair =
      if 3 ≤ |pair.1| then
        (angularClosedJet pair.1 (apSmoothJet admissible 1 pair.2
          (apSmoothRadial admissible (compensatedReconstruct admissible state)))).value (boundaryDiskPoint 0) else 0 := by
  let radial := apSmoothRadial admissible (compensatedReconstruct admissible state)
  have projected := apHighProjection_coefficient L sigma gamma ell (grade + 1)
    (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
      (apSmoothGrade L sigma gamma ell 1 (grade + 1) radial)) pair
  exact projected.trans (congrArg (fun value : ComplexEuclidean 1 => if 3 ≤ |pair.1| then value else 0)
    (originalSmoothTrace_coefficient admissible (grade + 1) (by omega) radial pair))

theorem circularTrace_coherent (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (first second : ℕ) (pair : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell (first + 1) (circularCoreTrace admissible first state) pair =
      apBoundaryCoefficient L sigma gamma ell (second + 1) (circularCoreTrace admissible second state) pair :=
  (circularTrace_literal_coefficient admissible state first pair).trans
    (circularTrace_literal_coefficient admissible state second pair).symm

theorem circularTrace_zero_all (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell)
    (zero : circularCoreTrace admissible 1 state = 0) (grade : ℕ) :
    circularCoreTrace admissible grade state = 0 := by
  apply originalBoundary_ext (grade + 1)
  intro pair
  exact (circularTrace_coherent admissible state grade 1 pair).trans
    ((congrArg (apBoundaryCoefficient L sigma gamma ell 2 · pair) zero).trans
      ((apBoundaryCoefficientCLM L sigma gamma ell 2 pair).map_zero.trans
        (apBoundaryCoefficientCLM L sigma gamma ell (grade + 1) pair).map_zero.symm))

theorem circularTrace_eq_all (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (beta : BandSmoothBoundary L sigma gamma ell)
    (same : circularCoreTrace admissible 1 state = beta.grade 1) (grade : ℕ) :
    circularCoreTrace admissible grade state = beta.grade grade := by
  apply originalBoundary_ext (grade + 1)
  intro pair
  exact (circularTrace_coherent admissible state grade 1 pair).trans
    ((congrArg (apBoundaryCoefficient L sigma gamma ell 2 · pair) same).trans
      ((beta.coherent 1 pair).trans (beta.coherent grade pair).symm))

end Grad.FullReferenceUniqueness
