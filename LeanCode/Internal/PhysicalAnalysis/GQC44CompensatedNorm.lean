import GQC43SmoothSplitting

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

def graphDimension : Fin 5 → ℕ := ![1, 2, 2, 1, 1]

def graphGrade (grade : ℕ) : Fin 5 → ℕ := ![grade + 2, grade + 1, grade + 1, grade + 1, grade + 1]

abbrev CompensatedGraphAmbient (L sigma gamma ell : ℝ) (grade : ℕ) :=
  PiLp 2 (fun index : Fin 5 => apGrade L sigma gamma ell (graphDimension index) (graphGrade grade index))

def compensatedGraphEntry {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (index : Fin 5) : CompensatedData L sigma gamma ell →ₗ[ℂ]
      apGrade L sigma gamma ell (graphDimension index) (graphGrade grade index) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun empty => Fin.elim0 empty))))) index
  · exact (apSmoothGrade L sigma gamma ell 1 (grade + 2)).comp (LinearMap.fst ℂ _ _)
  · exact (apSmoothGrade L sigma gamma ell 2 (grade + 1)).comp
      ((apSmoothValueMap L sigma gamma ell planarPartMap).comp (LinearMap.snd ℂ _ _))
  · exact (apSmoothGrade L sigma gamma ell 2 (grade + 1)).comp
      ((apSmoothRotation admissible 2).comp
        ((apSmoothValueMap L sigma gamma ell planarPartMap).comp (LinearMap.snd ℂ _ _)))
  · exact (apSmoothGrade L sigma gamma ell 1 (grade + 1)).comp
      ((apSmoothValueMap L sigma gamma ell toroidalPartMap).comp (LinearMap.snd ℂ _ _))
  · exact (apSmoothGrade L sigma gamma ell 1 (grade + 1)).comp
      ((apSmoothRotation admissible 1).comp
        ((apSmoothValueMap L sigma gamma ell toroidalPartMap).comp (LinearMap.snd ℂ _ _)))

def compensatedGraphLinear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    CompensatedData L sigma gamma ell →ₗ[ℂ] CompensatedGraphAmbient L sigma gamma ell grade where
  toFun data := WithLp.toLp 2 (fun index => compensatedGraphEntry admissible grade index data)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (compensatedGraphEntry admissible grade index).map_add first second
  map_smul' scalar data := by
    apply PiLp.ext
    intro index
    exact (compensatedGraphEntry admissible grade index).map_smul scalar data

/-- Exactly AN8: Θ at s+2; v_c,Rv_c,e,Re each at s+1, with the
literal original AP2 norm in all five slots. -/
def compensatedNorm {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) : ℝ :=
  ‖compensatedGraphLinear admissible grade data‖

theorem sum_fin_five (field : Fin 5 → ℝ) :
    ∑ index, field index = field 0 + field 1 + field 2 + field 3 + field 4 := by
  simp [Fin.sum_univ_succ, add_assoc]

theorem compensatedNorm_sq {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) :
    compensatedNorm admissible grade data ^ 2 =
      ‖apSmoothGrade L sigma gamma ell 1 (grade + 2) data.1‖ ^ 2 +
      ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) (apSmoothValueMap L sigma gamma ell planarPartMap data.2)‖ ^ 2 +
      ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) (apSmoothRotation admissible 2 (apSmoothValueMap L sigma gamma ell planarPartMap data.2))‖ ^ 2 +
      ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (apSmoothValueMap L sigma gamma ell toroidalPartMap data.2)‖ ^ 2 +
      ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (apSmoothRotation admissible 1 (apSmoothValueMap L sigma gamma ell toroidalPartMap data.2))‖ ^ 2 := by
  exact (PiLp.norm_sq_eq_of_L2
    (fun index : Fin 5 => apGrade L sigma gamma ell (graphDimension index) (graphGrade grade index))
    (compensatedGraphLinear admissible grade data)).trans
      (sum_fin_five (fun index => ‖compensatedGraphEntry admissible grade index data‖ ^ 2))

theorem compensatedNorm_nonnegative {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) : 0 ≤ compensatedNorm admissible grade data := norm_nonneg _

theorem compensatedNorm_triangle {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (first second : CompensatedData L sigma gamma ell) :
    compensatedNorm admissible grade (first + second) ≤
      compensatedNorm admissible grade first + compensatedNorm admissible grade second := by
  unfold compensatedNorm
  rw [map_add]
  exact norm_add_le _ _

theorem compensatedGraphEntry_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) (index : Fin 5) :
    ‖compensatedGraphEntry admissible grade index data‖ ≤ compensatedNorm admissible grade data :=
  PiLp.norm_apply_le (compensatedGraphLinear admissible grade data) index

end Grad.GaugeCoefficients.Physical.Compensated
