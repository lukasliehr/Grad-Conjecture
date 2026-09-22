import AKCO3ActualKnownSignedFirst
import AKBY1AllNaturalCellMoments
import AKBH1GenericMomentMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CellWeights

private theorem signedScalarNormalization (L ell n w : ℝ) (nonzero : w ≠ 0) (power : ℕ) :
    ((((ell/L : ℝ) : ℂ)*Complex.I)^power) * (((n/w)^power : ℝ) : ℂ) * ((w^power : ℝ) : ℂ) =
      (((n*ell/L : ℝ) : ℂ)*Complex.I)^power := by
  push_cast
  rw [← mul_pow,← mul_pow]
  congr 1
  have complexNonzero : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  rw [mul_assoc,div_mul_cancel₀ _ complexNonzero]
  ring

/-- Every signed startup power retains the next two natural cell moments
needed by the original phase conjugation and lower-order ER terms. -/
def StartupAllMoments.shift {dimension : ℕ} (family : StartupAllMoments dimension)
    (power : ℕ) : StartupMoments dimension where
  field := family.moment power
  moment grade := family.moment (power+grade.val)
  zero := by simp only [Fin.val_zero,Nat.add_zero]
  same := by
    filter_upwards [family.same] with point same
    intro grade cell
    rw [same (power+grade.val),same power,pow_add,mul_smul]
    exact smul_comm _ _ _

private theorem signedRatio_bound (power : ℕ) (cell : ℤ) :
    |((cell : ℝ)/cellWeight cell)^power| ≤ 1 := by
  have frequency : |(cell : ℝ)| ≤ cellWeight cell := by
    unfold cellWeight
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have ratio : |(cell : ℝ)/cellWeight cell| ≤ 1 := by
    rw [abs_div,abs_of_pos (cellWeight_pos cell)]
    exact (div_le_one (cellWeight_pos cell)).mpr frequency
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) ratio

def StartupAllMoments.signedMoments {dimension : ℕ} (family : StartupAllMoments dimension)
    (L ell : ℝ) (power : ℕ) : StartupMoments dimension :=
  ((family.shift power).diagonal (fun cell _ => ((cell : ℝ)/cellWeight cell)^power)
    1 zero_le_one (fun cell _ => signedRatio_bound power cell)
    (fun _ => aestronglyMeasurable_const)).smul ((((ell/L : ℝ) : ℂ)*Complex.I)^power)

/-- The bounded normalization reconstructs the actual signed derivative,
including ell/L, from the SAME native all-moment carrier. -/
theorem StartupAllMoments.signedMoments_same {dimension : ℕ} (family : StartupAllMoments dimension)
    (L ell : ℝ) (power : ℕ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (family.signedMoments L ell power).field point cell =
        startupAxialFrequency L ell cell ^ power • family.field point cell := by
  let diagonalField : StartupL2 dimension := startupMomentDiagonalField
    (fun cell _ => ((cell : ℝ)/cellWeight cell)^power) 1 zero_le_one
    (fun cell _ => signedRatio_bound power cell) (fun _ => aestronglyMeasurable_const) (family.moment power)
  let scalar : ℂ := (((ell/L : ℝ) : ℂ)*Complex.I)^power
  have literal : (family.signedMoments L ell power).field = scalar • diagonalField := rfl
  rw [literal]
  filter_upwards [Lp.coeFn_smul scalar diagonalField,
    startupMomentDiagonalField_ae (fun cell _ => ((cell : ℝ)/cellWeight cell)^power)
      1 zero_le_one (fun cell _ => signedRatio_bound power cell)
      (fun _ => aestronglyMeasurable_const) (family.moment power),family.same]
      with point scaled diagonal same
  intro cell
  rw [scaled,Pi.smul_apply,lp.coeFn_smul,Pi.smul_apply]
  change scalar • diagonalField point cell = _
  rw [show diagonalField point cell = _ from diagonal cell,same power cell]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul,smul_smul]
  congr 1
  exact signedScalarNormalization L ell (cell : ℝ) (cellWeight cell) (cellWeight_pos cell).ne' power

end Grad.CartesianStartup
