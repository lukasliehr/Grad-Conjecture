import AKCX8SameRankDerivativeRepresentatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered
namespace StartupSpatialAction
variable {rank input middle output : ℕ} {L ell : ℝ}

theorem outputGraph (operator : StartupSpatialAction rank input output L ell)
    (family : StartupSignedFamily input L ell) (regular : family.HasSpatialGrade rank) :
    ∃ image : GraphGrade output rank 0 openUnitDisk,
      base output rank openUnitDisk (fun _ => 0) image = operator.signed.coarse family.field := by
  obtain ⟨image,same⟩ := operator.preserves rank family regular 0 0
  exact ⟨image,by rw [(operator.signed.action family).zero,operator.signed.sameField] at same; exact same⟩

/-- Composition retains the genuine rank operators, and propagates only
first-graph remainders through their compatible fine actions. -/
def comp (outer : StartupSpatialAction rank middle output L ell)
    (inner : StartupSpatialAction rank input middle L ell) : StartupSpatialAction rank input output L ell where
  signed := outer.signed.comp inner.signed
  ranked := outer.ranked.comp inner.ranked
  preserves order family regular := outer.preserves order (inner.signed.action family)
    (inner.preserves order family regular)
  leading family regular field fieldSame image imageSame := by
    obtain ⟨intermediate,intermediateSame⟩ := inner.outputGraph family regular
    have outerInputSame : base middle rank openUnitDisk (fun _ => 0) intermediate = (inner.signed.action family).field := by
      rw [inner.signed.sameField]
      exact intermediateSame
    have outerImageSame : base output rank openUnitDisk (fun _ => 0) image =
        outer.signed.coarse (inner.signed.action family).field := by
      rw [inner.signed.sameField]
      exact imageSame
    obtain ⟨outerRem,outerEq⟩ := outer.leading (inner.signed.action family)
      (inner.preserves rank family regular) intermediate outerInputSame image outerImageSame
    obtain ⟨innerRem,innerEq⟩ := inner.leading family regular field fieldSame intermediate intermediateSame
    refine ⟨outerRem+outer.ranked.fine innerRem,?_⟩
    rw [outerEq,innerEq,map_add,map_add]
    have fineSame : base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0)
        (outer.ranked.fine innerRem) = outer.ranked.coarse
          (base (startupTensorDimension middle rank) 1 openUnitDisk (fun _ => 0) innerRem) :=
      outer.ranked.compatible innerRem
    rw [fineSame]
    change _ = outer.ranked.coarse (inner.ranked.coarse _) + _
    abel

def add (first second : StartupSpatialAction rank input output L ell) :
    StartupSpatialAction rank input output L ell where
  signed := first.signed.add second.signed
  ranked := first.ranked.add second.ranked
  preserves order family regular := (first.preserves order family regular).add (second.preserves order family regular)
  leading family regular field fieldSame image imageSame := by
    obtain ⟨one,oneSame⟩ := first.outputGraph family regular
    obtain ⟨two,twoSame⟩ := second.outputGraph family regular
    obtain ⟨oneRem,oneEq⟩ := first.leading family regular field fieldSame one oneSame
    obtain ⟨twoRem,twoEq⟩ := second.leading family regular field fieldSame two twoSame
    have same : base output rank openUnitDisk (fun _ => 0) image =
        base output rank openUnitDisk (fun _ => 0) (one+two) := by
      rw [imageSame,map_add,oneSame,twoSame]
      rfl
    have derivativeSame := startupOrderedDerivative_sameBase image le_rfl (one+two) le_rfl same
    refine ⟨oneRem+twoRem,?_⟩
    rw [derivativeSame,map_add,map_add,oneEq,twoEq,map_add]
    change _ = first.ranked.coarse _ + second.ranked.coarse _ + _
    abel

def sub (first second : StartupSpatialAction rank input output L ell) :
    StartupSpatialAction rank input output L ell where
  signed := first.signed.sub second.signed
  ranked := first.ranked.sub second.ranked
  preserves order family regular := (first.preserves order family regular).sub (second.preserves order family regular)
  leading family regular field fieldSame image imageSame := by
    obtain ⟨one,oneSame⟩ := first.outputGraph family regular
    obtain ⟨two,twoSame⟩ := second.outputGraph family regular
    obtain ⟨oneRem,oneEq⟩ := first.leading family regular field fieldSame one oneSame
    obtain ⟨twoRem,twoEq⟩ := second.leading family regular field fieldSame two twoSame
    have same : base output rank openUnitDisk (fun _ => 0) image =
        base output rank openUnitDisk (fun _ => 0) (one-two) := by
      rw [imageSame,map_sub,oneSame,twoSame]
      rfl
    have derivativeSame := startupOrderedDerivative_sameBase image le_rfl (one-two) le_rfl same
    refine ⟨oneRem-twoRem,?_⟩
    rw [derivativeSame,map_sub,map_sub,oneEq,twoEq,map_sub]
    change _ = (first.ranked.coarse _ - second.ranked.coarse _) + _
    abel

def smul (operator : StartupSpatialAction rank input output L ell) (scalar : ℂ) :
    StartupSpatialAction rank input output L ell where
  signed := operator.signed.smul scalar
  ranked := operator.ranked.smul scalar
  preserves order family regular := (operator.preserves order family regular).smul scalar
  leading family regular field fieldSame image imageSame := by
    obtain ⟨one,oneSame⟩ := operator.outputGraph family regular
    obtain ⟨oneRem,oneEq⟩ := operator.leading family regular field fieldSame one oneSame
    have same : base output rank openUnitDisk (fun _ => 0) image =
        base output rank openUnitDisk (fun _ => 0) (scalar • one) := by
      rw [imageSame,map_smul,oneSame]
      rfl
    have derivativeSame := startupOrderedDerivative_sameBase image le_rfl (scalar • one) le_rfl same
    refine ⟨scalar • oneRem,?_⟩
    rw [derivativeSame,map_smul,map_smul,oneEq,smul_add,map_smul]
    rfl

end StartupSpatialAction
end Grad.CartesianStartup
