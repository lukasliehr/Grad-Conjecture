import AKDP19SameOriginalRankLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.CartesianStartup
open Grad.NonlinearProduct Grad.Constraints.Gauges
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.OriginalCoreRealization Grad.NonlinearQuotientBounds

/-- Numerical constants for one actual rank, separated from the coefficient
state. The remainder is adjustable without changing the low neighborhood. -/
structure StartupCoreRankProfile where
  base : ℝ
  high : ℝ
  remainder : ℝ → ℝ
  baseNonnegative : 0≤base
  highNonnegative : 0≤high
  remainderNonnegative : ∀ epsilon,0<epsilon → 0≤remainder epsilon

/-- Same-original-core control for a literal full-cell operator and its
literal rank action. The sole coefficient payment is the displayed budget. -/
structure StartupCoreRankControl {input output rank : ℕ} (parameters : PhaseParameters)
    (budget : ℝ) (profile : StartupCoreRankProfile)
    (kernel : StartupL2 input →L[ℂ] StartupL2 output)
    (ranked : StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)) where
  action : ACore parameters input → ACore parameters output
  same : ∀ core, originalSourceFieldLinear parameters (action core) = kernel (originalSourceFieldLinear parameters core)
  baseBound : ∀ core, originalGradeNorm 0 (action core) ≤ profile.base*originalGradeNorm 0 core
  highBound : ∀ core, originalGradeNorm rank (action core) ≤
    profile.high*(originalGradeNorm rank core+budget*originalGradeNorm 0 core)
  remainderBound : ∀ epsilon,0<epsilon → ∀ core,
    ‖startupOriginalRankLinear parameters rank (action core)-ranked (startupOriginalRankLinear parameters rank core)‖ ≤
      epsilon*originalGradeNorm rank core+profile.remainder epsilon*(budget*originalGradeNorm 0 core)

namespace StartupCoreRankProfile

def fixed (base high : ℝ) (baseNonnegative : 0≤base) (highNonnegative : 0≤high) : StartupCoreRankProfile :=
  ⟨base,high,fun _ => 0,baseNonnegative,highNonnegative,fun _ _ => le_rfl⟩

def sum (first second : StartupCoreRankProfile) : StartupCoreRankProfile where
  base := first.base+second.base
  high := first.high+second.high
  remainder epsilon := first.remainder (epsilon/2)+second.remainder (epsilon/2)
  baseNonnegative := add_nonneg first.baseNonnegative second.baseNonnegative
  highNonnegative := add_nonneg first.highNonnegative second.highNonnegative
  remainderNonnegative epsilon positive := add_nonneg (first.remainderNonnegative _ (by positivity))
    (second.remainderNonnegative _ (by positivity))

end StartupCoreRankProfile
namespace StartupCoreRankControl
variable {input output rank : ℕ} {parameters : PhaseParameters} {budget : ℝ}

/-- Exact fixed action: no rank remainder is introduced. -/
def fixed (kernel : StartupL2 input →L[ℂ] StartupL2 output)
    (ranked : StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank))
    (action : ACore parameters input → ACore parameters output)
    (same : ∀ core,originalSourceFieldLinear parameters (action core)=kernel (originalSourceFieldLinear parameters core))
    (base high : ℝ) (baseNonnegative : 0≤base) (highNonnegative : 0≤high) (budgetNonnegative : 0≤budget)
    (baseBound : ∀ core,originalGradeNorm 0 (action core)≤base*originalGradeNorm 0 core)
    (highBound : ∀ core,originalGradeNorm rank (action core)≤high*originalGradeNorm rank core)
    (exactRank : ∀ core,startupOriginalRankLinear parameters rank (action core)=
      ranked (startupOriginalRankLinear parameters rank core)) :
    StartupCoreRankControl parameters budget (StartupCoreRankProfile.fixed base high baseNonnegative highNonnegative) kernel ranked where
  action := action
  same := same
  baseBound := baseBound
  highBound core := (highBound core).trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (mul_nonneg budgetNonnegative (originalGradeNorm_nonnegative 0 core))) highNonnegative)
  remainderBound epsilon positive core := by
    rw [exactRank core,sub_self,norm_zero]
    exact add_nonneg (mul_nonneg positive.le (originalGradeNorm_nonnegative rank core)) (by simp [StartupCoreRankProfile.fixed])

/-- Actual sums and differences use the same original field and rank
linearity; constants are selected before the coefficient state. -/
def add {firstProfile secondProfile : StartupCoreRankProfile}
    {firstKernel secondKernel : StartupL2 input →L[ℂ] StartupL2 output}
    {firstRank secondRank : StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (first : StartupCoreRankControl parameters budget firstProfile firstKernel firstRank)
    (second : StartupCoreRankControl parameters budget secondProfile secondKernel secondRank) :
    StartupCoreRankControl parameters budget (firstProfile.sum secondProfile) (firstKernel+secondKernel) (firstRank+secondRank) where
  action core := first.action core+second.action core
  same core := by rw [map_add,first.same,second.same]; rfl
  baseBound core := (originalGradeNorm_add_le 0 _ _).trans
    ((add_le_add (first.baseBound core) (second.baseBound core)).trans_eq (add_mul _ _ _).symm)
  highBound core := (originalGradeNorm_add_le rank _ _).trans
    ((add_le_add (first.highBound core) (second.highBound core)).trans_eq (add_mul _ _ _).symm)
  remainderBound epsilon positive core := by
    rw [map_add]
    change ‖_+_-(firstRank _+secondRank _)‖ ≤ _
    have identity {E : Type} [AddCommGroup E] (a b c d : E) : a+b-(c+d)=(a-c)+(b-d) := by abel
    rw [identity]
    exact (norm_add_le _ _).trans ((add_le_add
      (first.remainderBound (epsilon/2) (by positivity) core)
      (second.remainderBound (epsilon/2) (by positivity) core)).trans_eq (by
        change _ = epsilon*_+(firstProfile.remainder (epsilon/2)+secondProfile.remainder (epsilon/2))*_
        ring))

def sub {firstProfile secondProfile : StartupCoreRankProfile}
    {firstKernel secondKernel : StartupL2 input →L[ℂ] StartupL2 output}
    {firstRank secondRank : StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)}
    (first : StartupCoreRankControl parameters budget firstProfile firstKernel firstRank)
    (second : StartupCoreRankControl parameters budget secondProfile secondKernel secondRank) :
    StartupCoreRankControl parameters budget (firstProfile.sum secondProfile) (firstKernel-secondKernel) (firstRank-secondRank) where
  action core := first.action core-second.action core
  same core := by rw [map_sub,first.same,second.same]; rfl
  baseBound core := (originalGradeNorm_sub_le 0 _ _).trans
    ((add_le_add (first.baseBound core) (second.baseBound core)).trans_eq (add_mul _ _ _).symm)
  highBound core := (originalGradeNorm_sub_le rank _ _).trans
    ((add_le_add (first.highBound core) (second.highBound core)).trans_eq (add_mul _ _ _).symm)
  remainderBound epsilon positive core := by
    rw [map_sub]
    change ‖_-_-(firstRank _-secondRank _)‖ ≤ _
    have identity {E : Type} [AddCommGroup E] (a b c d : E) : a-b-(c-d)=(a-c)-(b-d) := by abel
    rw [identity]
    exact (norm_sub_le _ _).trans ((add_le_add
      (first.remainderBound (epsilon/2) (by positivity) core)
      (second.remainderBound (epsilon/2) (by positivity) core)).trans_eq (by
        change _ = epsilon*_+(firstProfile.remainder (epsilon/2)+secondProfile.remainder (epsilon/2))*_
        ring))

end StartupCoreRankControl
end Grad.CartesianStartup
