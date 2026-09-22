import AKCX21SameRankDerivativeAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered
namespace StartupSpatialAction
variable {rank input middle output : ℕ} {L ell : ℝ}

theorem HasMixedLeading.comp {outer : StartupSpatialAction rank middle output L ell}
    {inner : StartupSpatialAction rank input middle L ell}
    (outerMixed : outer.HasMixedLeading) (innerMixed : inner.HasMixedLeading) : (outer.comp inner).HasMixedLeading := by
  intro family regular power lower
  have intermediateLower : ∀ q < power, ∃ first : StartupFirst (startupTensorDimension middle rank),
      base (startupTensorDimension middle rank) 1 openUnitDisk (fun _ => 0) first =
        (inner.signed.action family).rankDerivative (inner.preserves rank family regular) q := by
    intro q less
    obtain ⟨inputFirst,inputSame⟩ := lower q less
    obtain ⟨remainder,equation⟩ := innerMixed family regular q (fun r before => lower r (before.trans less))
    refine ⟨inner.ranked.fine inputFirst+remainder,?_⟩
    have fineSame : base (startupTensorDimension middle rank) 1 openUnitDisk (fun _ => 0)
        (inner.ranked.fine inputFirst) = inner.ranked.coarse
          (base (startupTensorDimension input rank) 1 openUnitDisk (fun _ => 0) inputFirst) :=
      inner.ranked.compatible inputFirst
    rw [map_add,fineSame,inputSame]
    exact equation.symm
  obtain ⟨outerRem,outerEq⟩ := outerMixed (inner.signed.action family)
    (inner.preserves rank family regular) power intermediateLower
  obtain ⟨innerRem,innerEq⟩ := innerMixed family regular power lower
  refine ⟨outerRem+outer.ranked.fine innerRem,?_⟩
  change (outer.signed.action (inner.signed.action family)).rankDerivative
    (outer.preserves rank (inner.signed.action family) (inner.preserves rank family regular)) power =
    outer.ranked.coarse (inner.ranked.coarse (family.rankDerivative regular power)) +
      base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0) (outerRem+outer.ranked.fine innerRem)
  rw [outerEq,innerEq,map_add,map_add]
  have fineSame : base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0)
      (outer.ranked.fine innerRem) = outer.ranked.coarse
        (base (startupTensorDimension middle rank) 1 openUnitDisk (fun _ => 0) innerRem) := outer.ranked.compatible innerRem
  rw [fineSame]
  change _ = outer.ranked.coarse (inner.ranked.coarse _) + _
  abel

theorem HasMixedLeading.add {first second : StartupSpatialAction rank input output L ell}
    (one : first.HasMixedLeading) (two : second.HasMixedLeading) : (first.add second).HasMixedLeading := by
  intro family regular power lower
  obtain ⟨oneRem,oneEq⟩ := one family regular power lower
  obtain ⟨twoRem,twoEq⟩ := two family regular power lower
  refine ⟨oneRem+twoRem,?_⟩
  have outputSame := StartupSignedFamily.rankDerivative_add (first.signed.action family) (second.signed.action family)
    (first.preserves rank family regular) (second.preserves rank family regular) power
  change ((first.signed.action family).add (second.signed.action family)).rankDerivative
    ((first.preserves rank family regular).add (second.preserves rank family regular)) power =
    (first.ranked.coarse (family.rankDerivative regular power)+second.ranked.coarse (family.rankDerivative regular power)) +
      base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0) (oneRem+twoRem)
  rw [outputSame,oneEq,twoEq,map_add]
  change _ = (first.ranked.coarse _+second.ranked.coarse _)+_
  abel

theorem HasMixedLeading.sub {first second : StartupSpatialAction rank input output L ell}
    (one : first.HasMixedLeading) (two : second.HasMixedLeading) : (first.sub second).HasMixedLeading := by
  intro family regular power lower
  obtain ⟨oneRem,oneEq⟩ := one family regular power lower
  obtain ⟨twoRem,twoEq⟩ := two family regular power lower
  refine ⟨oneRem-twoRem,?_⟩
  have outputSame := StartupSignedFamily.rankDerivative_sub (first.signed.action family) (second.signed.action family)
    (first.preserves rank family regular) (second.preserves rank family regular) power
  change ((first.signed.action family).sub (second.signed.action family)).rankDerivative
    ((first.preserves rank family regular).sub (second.preserves rank family regular)) power =
    (first.ranked.coarse (family.rankDerivative regular power)-second.ranked.coarse (family.rankDerivative regular power)) +
      base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0) (oneRem-twoRem)
  rw [outputSame,oneEq,twoEq,map_sub]
  change _ = (first.ranked.coarse _-second.ranked.coarse _)+_
  abel

theorem HasMixedLeading.smul {operator : StartupSpatialAction rank input output L ell}
    (mixed : operator.HasMixedLeading) (scalar : ℂ) : (operator.smul scalar).HasMixedLeading := by
  intro family regular power lower
  obtain ⟨remainder,equation⟩ := mixed family regular power lower
  refine ⟨scalar • remainder,?_⟩
  have outputSame := StartupSignedFamily.rankDerivative_smul (operator.signed.action family)
    (operator.preserves rank family regular) scalar power
  change ((operator.signed.action family).smul scalar).rankDerivative
    ((operator.preserves rank family regular).smul scalar) power =
    scalar • operator.ranked.coarse (family.rankDerivative regular power) +
      base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0) (scalar • remainder)
  rw [outputSame,equation,smul_add,map_smul]

/-- Cell-diagonal fixed actions have no positive axial allocations; their
mixed identity is the already proved true-covector spatial identity. -/
theorem mixed_of_sameMoment (operator : StartupSpatialAction rank input output L ell)
    (sameMoment : ∀ (family : StartupSignedFamily input L ell) (power : ℕ),
      (operator.signed.action family).moment power = operator.signed.coarse (family.moment power)) :
    operator.HasMixedLeading := by
  intro family regular power _
  let field := (regular power 0).choose
  let outputRegular := operator.preserves rank family regular
  let image := (outputRegular power 0).choose
  have fieldSame : base input rank openUnitDisk (fun _ => 0) field = (family.shift power).field :=
    (regular power 0).choose_spec
  have imageSame : base output rank openUnitDisk (fun _ => 0) image = operator.signed.coarse (family.shift power).field := by
    rw [(outputRegular power 0).choose_spec,sameMoment]
    rfl
  exact operator.leading (family.shift power) (regular.shift power) field fieldSame image imageSame

end StartupSpatialAction
end Grad.CartesianStartup
