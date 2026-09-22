import AKCO6SignedOperatorAlgebra
import AKCG11PositiveAxialRemainderGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupSignedAction
variable {input output : ℕ} {L ell : ℝ}

def fixed (coarse : StartupL2 input →L[ℂ] StartupL2 output)
    (fine : StartupFirst input →L[ℂ] StartupFirst output)
    (compatible : StartupCompatible coarse fine) (diagonal : StartupCellwise coarse) :
    StartupSignedAction input output L ell where
  coarse := coarse
  fine := fine
  compatible := compatible
  action family := family.map coarse diagonal
  sameField _ := rfl
  lowerRemainder family power _ := ⟨0,by simp only [map_zero,StartupSignedFamily.map,sub_self]⟩

/-- The actual full coefficient matrix's lower signed remainder is the
accepted positive displacement graph, with strictly lower input powers. -/
def matrix {sigma gamma : ℝ} (admissible : Admissible L sigma gamma ell)
    (coefficients : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent coefficients) :
    StartupSignedAction input output L ell where
  coarse := originalMatrixKernel admissible coefficients coherent
  fine := startupMatrixFirstGraphCLM admissible coefficients coherent
  compatible := startupMatrixFirstGraph_compatible admissible coefficients coherent
  action family := family.matrix admissible coefficients coherent
  sameField _ := rfl
  lowerRemainder family power lower := by
    let lowerGraphs : Fin power → StartupFirst input := fun j =>
      (lower (power-(j.val+1)) (startupPositiveAxialRemainder_lower power j)).choose
    have same : ∀ j : Fin power,
        base input 1 openUnitDisk (fun _ => 0) (lowerGraphs j) = family.moment (power-(j.val+1)) :=
      fun j => (lower (power-(j.val+1)) (startupPositiveAxialRemainder_lower power j)).choose_spec
    refine ⟨startupPositiveAxialRemainderGraph admissible coefficients coherent power
      (show 1-1 ≤ 0 by decide) lowerGraphs,?_⟩
    rw [startupPositiveAxialRemainderGraph_base admissible coefficients coherent power _ lowerGraphs family.moment same]
    change startupPositiveAxialRemainder admissible coefficients coherent power family.moment =
      startupKernelAxialMoment admissible coefficients coherent zeroDerivativeIndex power family.moment - _
    rw [startupKernelAxialMoment_leadingSplit]
    abel

def add (first second : StartupSignedAction input output L ell) : StartupSignedAction input output L ell where
  coarse := first.coarse + second.coarse
  fine := first.fine + second.fine
  compatible := startupCompatible_add first.compatible second.compatible
  action family := (first.action family).add (second.action family)
  sameField family := by
    change (first.action family).field + (second.action family).field = _
    rw [first.sameField,second.sameField]
    rfl
  lowerRemainder family power lower := by
    obtain ⟨one,oneSame⟩ := first.lowerRemainder family power lower
    obtain ⟨two,twoSame⟩ := second.lowerRemainder family power lower
    refine ⟨one+two,?_⟩
    rw [map_add,oneSame,twoSame]
    change _ = (first.action family).moment power + (second.action family).moment power -
      (first.coarse (family.moment power)+second.coarse (family.moment power))
    abel

def sub (first second : StartupSignedAction input output L ell) : StartupSignedAction input output L ell where
  coarse := first.coarse - second.coarse
  fine := first.fine - second.fine
  compatible := startupCompatible_sub first.compatible second.compatible
  action family := (first.action family).sub (second.action family)
  sameField family := by
    change (first.action family).field - (second.action family).field = _
    rw [first.sameField,second.sameField]
    rfl
  lowerRemainder family power lower := by
    obtain ⟨one,oneSame⟩ := first.lowerRemainder family power lower
    obtain ⟨two,twoSame⟩ := second.lowerRemainder family power lower
    refine ⟨one-two,?_⟩
    rw [map_sub,oneSame,twoSame]
    change _ = (first.action family).moment power - (second.action family).moment power -
      (first.coarse (family.moment power)-second.coarse (family.moment power))
    abel

def smul (operator : StartupSignedAction input output L ell) (scalar : ℂ) :
    StartupSignedAction input output L ell where
  coarse := scalar • operator.coarse
  fine := scalar • operator.fine
  compatible := startupCompatible_smul scalar operator.compatible
  action family := (operator.action family).smul scalar
  sameField family := by
    change scalar • (operator.action family).field = _
    rw [operator.sameField]
    rfl
  lowerRemainder family power lower := by
    obtain ⟨remainder,same⟩ := operator.lowerRemainder family power lower
    refine ⟨scalar • remainder,?_⟩
    rw [map_smul,same,smul_sub]
    rfl

end StartupSignedAction
end Grad.CartesianStartup
