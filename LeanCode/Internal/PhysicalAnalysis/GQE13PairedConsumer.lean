import GQE12BulkRealization

noncomputable section
set_option maxHeartbeats 500000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

theorem apPairedContraction_bounds {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    ‖(apPairedContraction admissible grade field).1‖ ≤ fixedRowBoundConstant L sigma gamma grade radialRowJet * ‖field‖ ∧
    ‖(apPairedContraction admissible grade field).2‖ ≤
      ((1 + orthogonalGradeConstant grade) * fixedRowBoundConstant L sigma gamma grade tangentRowJet) * ‖field‖ := by
  refine ⟨apFixedRow_bound admissible grade radialRowJet field, ?_⟩
  exact (apMeanFree_bound L sigma gamma ell 1 grade (apTangentContraction admissible grade field)).trans
    ((mul_le_mul_of_nonneg_left (apFixedRow_bound admissible grade tangentRowJet field)
      (add_nonneg zero_le_one (orthogonalGradeConstant_nonnegative grade))).trans_eq (mul_assoc _ _ _).symm)

theorem apProjectedTangent_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : apGrade L sigma gamma ell 3 grade) (point : ClosedDisk) :
    apPhysicalValue admissible large angle
        (apMeanFree L sigma gamma ell 1 grade (apTangentContraction admissible grade field)) point 0 =
      storedTangentDot point (apPhysicalValue admissible large angle field point) -
        closedAngularMean (fun other => storedTangentDot other (apPhysicalValue admissible large angle field other)) point := by
  let tangent := apTangentContraction admissible grade field
  have mean := congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean 1) => mapping point 0)
    (apAngularMean_physical admissible large angle tangent)
  have scalarMean : cMapAngular 1 0 (apPhysicalValue admissible large angle tangent) point 0 =
      closedAngularMean (fun other => apPhysicalValue admissible large angle tangent other 0) point := by
    rw [cMapAngular_apply, closedCharacterProjection_zero]
    exact closedAngularMean_clm
      ((PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : ComplexEuclidean 1 →L[ℂ] ℂ).restrictScalars ℝ)
      (apPhysicalValue admissible large angle tangent) (apPhysicalValue admissible large angle tangent).continuous point
  have tangentValues : (fun other => apPhysicalValue admissible large angle tangent other 0) =
      fun other => storedTangentDot other (apPhysicalValue admissible large angle field other) :=
    funext (apTangentContraction_physical admissible large angle field)
  have meanValue := mean.trans (scalarMean.trans (congrArg (fun value : ClosedDisk → ℂ => closedAngularMean value point) tangentValues))
  have subtraction := congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean 1) => mapping point 0)
    (map_sub (apPhysicalValue (dimension := 1) admissible large angle) tangent
      (apAngularMean L sigma gamma ell 1 grade tangent))
  exact subtraction.trans (congrArg₂ (fun first second : ℂ => first - second)
    (apTangentContraction_physical admissible large angle field point) meanValue)

/-- CT_GC01_contractions in its actual AP2 carrier and original scaled
norm, including q=0,1. The physical formulas above give Y·v and P(JY·v). -/
theorem actualPairedComplementContraction {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    (∀ field : apComplementRange L sigma gamma ell grade,
      apPairedContraction admissible grade field.val = 0) ∧
    (∀ field : apGrade L sigma gamma ell 3 grade,
      ‖(apPairedContraction admissible grade field).1‖ ≤ fixedRowBoundConstant L sigma gamma grade radialRowJet * ‖field‖ ∧
      ‖(apPairedContraction admissible grade field).2‖ ≤
        ((1 + orthogonalGradeConstant grade) * fixedRowBoundConstant L sigma gamma grade tangentRowJet) * ‖field‖) :=
  ⟨fun field => apPairedContraction_range_zero admissible grade field.val field.property,
    apPairedContraction_bounds admissible grade⟩

end Grad.GaugeCoefficients.Physical.Compensated
