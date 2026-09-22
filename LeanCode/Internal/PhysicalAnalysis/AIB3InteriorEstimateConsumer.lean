import AIB2HigherOrdinaryRegularity

noncomputable section
namespace Grad.OrdinaryInteriorBootstrap
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.InteriorLocalization Grad.OrdinaryDiskCalculus Grad.COR12Extension
open Grad.GaugeCoefficients.Physical.RadialLedger

def ordinaryInteriorSourceConstant (grade : ℕ) : ℝ :=
  (sameGradeConstant (grade + 2) * sameGradeConstant grade) * unitCutoffSourceConstant grade

def ordinaryInteriorStateConstant (grade : ℕ) : ℝ :=
  (sameGradeConstant (grade + 2) * sameGradeConstant grade) *
    (unitCutoffStateConstant grade + unitCutoffSourceConstant grade * apLoweringConstant grade)

/-- Quantitative all-grade interior estimate on the actual disk field.
This is the global H^(q+1)-state version of the cutoff step; the paper's
sharper collar-only state norm remains a separate gluing/induction obligation. -/
theorem ordinaryInterior_estimate (parameters : PhaseParameters) (grade : ℕ)
    (state : unitDiskSobolev (grade + 1)) (laplacian : unitDiskSobolev grade)
    (equation : HasDiskWeakLaplacian (unitDiskBulk (grade + 1) state) (unitDiskBulk grade laplacian)) :
    ∃ regular : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) regular =
        diskScalar interiorCutoff.toFun interiorCutoff.smooth (unitDiskBulk (grade + 1) state) ∧
      ‖regular‖ ≤ ordinaryInteriorSourceConstant grade * ‖laplacian‖ +
        ordinaryInteriorStateConstant grade * ‖state‖ := by
  have existence : ∃ regular : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) regular =
        diskScalar interiorCutoff.toFun interiorCutoff.smooth (unitDiskBulk (grade + 1) state) ∧
      ‖regular‖ ≤ (sameGradeConstant (grade + 2) * sameGradeConstant grade) *
        (‖unitLocalizedLaplacian grade state laplacian‖ + ‖unitLocalizedField grade state‖) :=
    ordinaryInterior_gainTwo parameters grade state laplacian equation
  obtain ⟨regular, same, bound⟩ := existence
  refine ⟨regular, same, bound.trans ?_⟩
  have lower := add_le_add (unitLocalizedLaplacian_bound grade state laplacian)
    (unitLocalizedField_bound grade state)
  exact (mul_le_mul_of_nonneg_left lower
    (mul_nonneg (sameGradeConstant_nonnegative (grade + 2)) (sameGradeConstant_nonnegative grade))).trans_eq (by
      unfold ordinaryInteriorSourceConstant ordinaryInteriorStateConstant
      ring)

end Grad.OrdinaryInteriorBootstrap
