import AKCO5ExactSignedCellFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets

namespace StartupSignedFamily
variable {dimension : ℕ} {L ell : ℝ}

def add (first second : StartupSignedFamily dimension L ell) : StartupSignedFamily dimension L ell where
  field := first.field + second.field
  moment power := first.moment power + second.moment power
  same power := by
    filter_upwards [Lp.coeFn_add (first.moment power) (second.moment power),
      Lp.coeFn_add first.field second.field,first.same power,second.same power] with point one two left right
    intro cell
    rw [one,two,Pi.add_apply,Pi.add_apply,lp.coeFn_add,lp.coeFn_add,Pi.add_apply,Pi.add_apply,left cell,right cell,smul_add]

def sub (first second : StartupSignedFamily dimension L ell) : StartupSignedFamily dimension L ell where
  field := first.field - second.field
  moment power := first.moment power - second.moment power
  same power := by
    filter_upwards [Lp.coeFn_sub (first.moment power) (second.moment power),
      Lp.coeFn_sub first.field second.field,first.same power,second.same power] with point one two left right
    intro cell
    rw [one,two,Pi.sub_apply,Pi.sub_apply,lp.coeFn_sub,lp.coeFn_sub,Pi.sub_apply,Pi.sub_apply,left cell,right cell,smul_sub]

def smul (family : StartupSignedFamily dimension L ell) (scalar : ℂ) : StartupSignedFamily dimension L ell where
  field := scalar • family.field
  moment power := scalar • family.moment power
  same power := by
    filter_upwards [Lp.coeFn_smul scalar (family.moment power),Lp.coeFn_smul scalar family.field,
      family.same power] with point one two same
    intro cell
    rw [one,two,Pi.smul_apply,Pi.smul_apply,lp.coeFn_smul,lp.coeFn_smul,Pi.smul_apply,Pi.smul_apply,same cell]
    exact smul_comm _ _ _

end StartupSignedFamily

/-- One exact signed moment action and its genuinely lower-power first
remainder. Composition will retain the actual full coefficient operator. -/
structure StartupSignedAction (input output : ℕ) (L ell : ℝ) where
  coarse : StartupL2 input →L[ℂ] StartupL2 output
  fine : StartupFirst input →L[ℂ] StartupFirst output
  compatible : StartupCompatible coarse fine
  action : StartupSignedFamily input L ell → StartupSignedFamily output L ell
  sameField : ∀ family, (action family).field = coarse family.field
  lowerRemainder : ∀ (family : StartupSignedFamily input L ell) (power : ℕ),
    (∀ q < power, ∃ graph : StartupFirst input,
      base input 1 openUnitDisk (fun _ => 0) graph = family.moment q) →
    ∃ remainder : StartupFirst output,
      base output 1 openUnitDisk (fun _ => 0) remainder =
        (action family).moment power - coarse (family.moment power)

namespace StartupSignedAction
variable {input middle output : ℕ} {L ell : ℝ}

theorem preservesFirst (operator : StartupSignedAction input output L ell)
    (family : StartupSignedFamily input L ell) (power : ℕ)
    (regular : ∀ q ≤ power, ∃ graph : StartupFirst input,
      base input 1 openUnitDisk (fun _ => 0) graph = family.moment q) :
    ∃ graph : StartupFirst output, base output 1 openUnitDisk (fun _ => 0) graph =
      (operator.action family).moment power := by
  obtain ⟨top,topSame⟩ := regular power le_rfl
  obtain ⟨remainder,remainderSame⟩ := operator.lowerRemainder family power
    (fun q bound => regular q bound.le)
  refine ⟨operator.fine top+remainder,?_⟩
  rw [map_add,operator.compatible,topSame,remainderSame]
  abel

/-- Actual nested compositions only use lower powers of the original
input. Regularity of the intermediate top power is never assumed. -/
def comp (outer : StartupSignedAction middle output L ell)
    (inner : StartupSignedAction input middle L ell) : StartupSignedAction input output L ell where
  coarse := outer.coarse.comp inner.coarse
  fine := outer.fine.comp inner.fine
  compatible := startupCompatible_comp outer.compatible inner.compatible
  action family := outer.action (inner.action family)
  sameField family := by rw [outer.sameField,inner.sameField]; rfl
  lowerRemainder family power lower := by
    have intermediate : ∀ q < power, ∃ graph : StartupFirst middle,
        base middle 1 openUnitDisk (fun _ => 0) graph = (inner.action family).moment q := by
      intro q less
      exact inner.preservesFirst family q (fun r bound => lower r (bound.trans_lt less))
    obtain ⟨outerRem,outerSame⟩ := outer.lowerRemainder (inner.action family) power intermediate
    obtain ⟨innerRem,innerSame⟩ := inner.lowerRemainder family power lower
    refine ⟨outerRem+outer.fine innerRem,?_⟩
    rw [map_add,outer.compatible,outerSame,innerSame,map_sub,ContinuousLinearMap.comp_apply]
    abel

end StartupSignedAction
end Grad.CartesianStartup
