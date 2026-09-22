import AKDX5FixedCutoffCartesianEnergy
import SCD9RadialAngularJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift
open Grad.SourceCollarDivision

def polarWordCount {order : ℕ} (word : CartesianWord order) (coordinate : Fin 2) : ℕ :=
  ∑ position : Fin order,if word position=coordinate then 1 else 0

theorem polarWordCount_succ {order : ℕ} (word : CartesianWord (order+1)) (coordinate : Fin 2) :
    polarWordCount word coordinate=(if word 0=coordinate then 1 else 0)+polarWordCount (Fin.tail word) coordinate :=
  Fin.sum_univ_succ _

theorem polarWordCount_total {order : ℕ} (word : CartesianWord order) :
    polarWordCount word 0+polarWordCount word 1=order := by
  rw [polarWordCount,polarWordCount,←Finset.sum_add_distrib]
  calc
    _=∑ _position : Fin order,(1:ℕ) := by
      apply Finset.sum_congr rfl
      intro position _
      generalize word position=coordinate
      fin_cases coordinate <;> simp
    _=_ := by simp

def polarWordField {dimension order : ℕ} (field : ℝ×ℝ→ComplexEuclidean dimension)
    (word : CartesianWord order) (point : ℝ×ℝ) : ComplexEuclidean dimension :=
  iteratedFDeriv ℝ order field point (fun position => productBasis (word position))

theorem polarWordField_smooth {dimension order : ℕ} (field : ℝ×ℝ→ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (word : CartesianWord order) : ContDiff ℝ ∞ (polarWordField field word) := by
  let evaluation := ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => ℝ×ℝ)
    (ComplexEuclidean dimension) (fun position => productBasis (word position))
  exact evaluation.contDiff.comp (smooth.iteratedFDeriv_right (m:=∞) (i:=order) (by norm_cast))

theorem polarWordField_periodic {dimension order : ℕ} (field : ℝ×ℝ→ComplexEuclidean dimension)
    (periodic : Function.Periodic field (0,2*Real.pi)) (word : CartesianWord order) :
    Function.Periodic (polarWordField field word) (0,2*Real.pi) := by
  intro point
  exact congrArg (fun tensor => tensor (fun position => productBasis (word position)))
    (periodic_iteratedFDeriv order field periodic point)

theorem polarWordField_step {dimension order : ℕ} (field : ℝ×ℝ→ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (word : CartesianWord (order+1)) (point : ℝ×ℝ) :
    polarWordField field word point=
      fderiv ℝ (polarWordField field (Fin.tail word)) point (productBasis (word 0)) := by
  exact ((smooth.contDiffAt.iteratedFDeriv_right (m:=∞) (i:=order) (by norm_cast)).differentiableAt
    (by simp)).iteratedFDeriv_succ_apply_left' (m:=fun position => productBasis (word position))

/-- Every original polar tensor word has the literal Fourier multiplier
and radial derivative; no angular summability or finite support is assumed. -/
theorem polarWordField_coefficient {dimension : ℕ} (field : ℝ×ℝ→ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (periodic : Function.Periodic field (0,2*Real.pi))
    (order : ℕ) (word : CartesianWord order) (radius : ℝ) (mode : ℤ) :
    angularCoefficient (fun angle => polarWordField field word (radius,angle)) mode=
      (Complex.I*(mode:ℂ))^(polarWordCount word 1) •
        radialCoefficientJet field mode (polarWordCount word 0) radius := by
  induction order generalizing radius with
  | zero => simp [polarWordField,polarWordCount,radialCoefficientJet,radialIter,iteratedFDeriv_zero_apply]
  | succ order previous =>
    let tail := polarWordField field (Fin.tail word)
    have tailSmooth : ContDiff ℝ ∞ tail := polarWordField_smooth field smooth (Fin.tail word)
    have tailPeriodic : Function.Periodic tail (0,2*Real.pi) := polarWordField_periodic field periodic (Fin.tail word)
    by_cases first : word 0=0
    · have same : polarWordField field word=radialField tail := by
        funext point
        rw [polarWordField_step field smooth word point,first]
        rfl
      have derivative := angularCoefficient_hasDerivAt tail tailSmooth mode radius
      have coefficients : (fun current => angularCoefficient (fun angle => tail (current,angle)) mode)=
          fun current => (Complex.I*(mode:ℂ))^(polarWordCount (Fin.tail word) 1) •
            radialCoefficientJet field mode (polarWordCount (Fin.tail word) 0) current := by
        funext current
        exact previous (Fin.tail word) current
      rw [coefficients] at derivative
      have identified := derivative.unique ((radialCoefficientJet_hasDerivAt field smooth mode
        (polarWordCount (Fin.tail word) 0) radius).const_smul ((Complex.I*(mode:ℂ))^(polarWordCount (Fin.tail word) 1)))
      rw [same]
      simpa only [polarWordCount_succ,first,ite_true,ite_false,zero_ne_one,zero_add,Nat.add_comm] using identified
    · have firstOne : word 0=1 := by omega
      have same : polarWordField field word=angularJet 1 tail := by
        funext point
        rw [polarWordField_step field smooth word point,firstOne]
        simp only [angularJet,iteratedFDeriv_one_apply]
        rfl
      rw [same,angularCoefficient_angularJet 1 tail tailSmooth tailPeriodic radius mode]
      change (Complex.I*(mode:ℂ))^1 • angularCoefficient (fun angle => polarWordField field (Fin.tail word) (radius,angle)) mode=_
      rw [previous (Fin.tail word) radius,smul_smul]
      simp only [polarWordCount_succ,firstOne,ite_true,ite_false,one_ne_zero,zero_add,pow_one]
      rw [pow_add,pow_one]

end Grad.OriginalCollarNorm
