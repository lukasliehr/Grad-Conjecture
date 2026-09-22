import AKQ7ActualConstantMatrixCubicRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets

/-- Physical row ordering is (planar 1, toroidal, planar 2), whereas the
columns are (y1,y2,axial). The tilt is retained in both planar columns. -/
def tiltedAxisFrame (planar : Matrix (Fin 2) (Fin 2) ℂ) (tilt : ComplexEuclidean 2) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![planar 0 0, planar 0 1, 0; tilt 0, tilt 1, 1; planar 1 0, planar 1 1, 0]

def tiltedAxisInverse (inverse : Matrix (Fin 2) (Fin 2) ℂ) (tilt : ComplexEuclidean 2) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![inverse 0 0, 0, inverse 0 1; inverse 1 0, 0, inverse 1 1;
    -(tilt 0 * inverse 0 0 + tilt 1 * inverse 1 0), 1,
    -(tilt 0 * inverse 0 1 + tilt 1 * inverse 1 1)]

theorem tiltedAxisFrame_det (planar : Matrix (Fin 2) (Fin 2) ℂ) (tilt : ComplexEuclidean 2) :
    (tiltedAxisFrame planar tilt).det = -planar.det := by
  simp [tiltedAxisFrame,Matrix.det_fin_three,Matrix.det_fin_two]
  ring

theorem tiltedAxisFrame_right_inverse (planar inverse : Matrix (Fin 2) (Fin 2) ℂ)
    (tilt : ComplexEuclidean 2) (inverseLaw : planar * inverse = 1) :
    tiltedAxisFrame planar tilt * tiltedAxisInverse inverse tilt = 1 := by
  have entry (row column : Fin 2) := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℂ => matrix row column) inverseLaw
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply] at entry
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [tiltedAxisFrame,tiltedAxisInverse,Matrix.mul_apply,Fin.sum_univ_three,entry]

theorem tiltedAxisFrame_inv (planar inverse : Matrix (Fin 2) (Fin 2) ℂ)
    (tilt : ComplexEuclidean 2) (inverseLaw : planar * inverse = 1) :
    (tiltedAxisFrame planar tilt)⁻¹ = tiltedAxisInverse inverse tilt :=
  Matrix.inv_eq_right_inv (tiltedAxisFrame_right_inverse planar inverse tilt inverseLaw)

/-- AM26 inverse Gram, with all off-diagonal tilt entries. -/
def tiltedAxisGram (gram : Matrix (Fin 2) (Fin 2) ℂ) (tilt : ComplexEuclidean 2) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![gram 0 0, gram 0 1, -(gram 0 0 * tilt 0 + gram 0 1 * tilt 1);
    gram 1 0, gram 1 1, -(gram 1 0 * tilt 0 + gram 1 1 * tilt 1);
    -(tilt 0 * gram 0 0 + tilt 1 * gram 1 0),
      -(tilt 0 * gram 0 1 + tilt 1 * gram 1 1),
      1 + tilt 0 * (gram 0 0 * tilt 0 + gram 0 1 * tilt 1) +
        tilt 1 * (gram 1 0 * tilt 0 + gram 1 1 * tilt 1)]

theorem tiltedAxisInverse_gram (inverse : Matrix (Fin 2) (Fin 2) ℂ) (tilt : ComplexEuclidean 2) :
    tiltedAxisInverse inverse tilt * (tiltedAxisInverse inverse tilt).transpose =
      tiltedAxisGram (inverse * inverse.transpose) tilt := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [tiltedAxisInverse,tiltedAxisGram,Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two] <;> ring

/-- The signed cofactor has the original negative determinant sign. -/
theorem tiltedAxisFrame_signedCofactor (planar inverse : Matrix (Fin 2) (Fin 2) ℂ)
    (tilt : ComplexEuclidean 2) (inverseLaw : planar * inverse = 1) :
    (tiltedAxisFrame planar tilt).det •
      ((tiltedAxisFrame planar tilt)⁻¹ * ((tiltedAxisFrame planar tilt)⁻¹).transpose) =
        (-planar.det) • tiltedAxisGram (inverse * inverse.transpose) tilt := by
  rw [tiltedAxisFrame_det,tiltedAxisFrame_inv planar inverse tilt inverseLaw,tiltedAxisInverse_gram]

theorem inverseGram_eq (planar : Matrix (Fin 2) (Fin 2) ℂ) :
    planar⁻¹ * planar⁻¹.transpose = (planar.transpose * planar)⁻¹ := by
  rw [Matrix.mul_inv_rev,Matrix.transpose_nonsing_inv]

theorem tiltedAxisFrame_signedCofactor_inverseGram (planar : Matrix (Fin 2) (Fin 2) ℂ)
    (tilt : ComplexEuclidean 2) (invertible : IsUnit planar.det) :
    (tiltedAxisFrame planar tilt).det •
      ((tiltedAxisFrame planar tilt)⁻¹ * ((tiltedAxisFrame planar tilt)⁻¹).transpose) =
        (-planar.det) • tiltedAxisGram ((planar.transpose * planar)⁻¹) tilt := by
  rw [tiltedAxisFrame_signedCofactor planar planar⁻¹ tilt (Matrix.mul_nonsing_inv planar invertible),inverseGram_eq]

end Grad.FinitePhysicalJetLift
