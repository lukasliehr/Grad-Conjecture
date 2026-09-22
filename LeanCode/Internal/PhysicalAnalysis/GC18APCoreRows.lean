import GC18APCoreKernel

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apAllocation_single_sum {dimension grade : ℕ}
    (family : APAllocation grade → DiskL2 dimension) (index : DerivativeIndex grade) :
    (∑ allocation : APAllocation grade,
      PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 dimension) (apOutputIndex allocation) (family allocation)) index =
      ∑ firstSplit : DerivativeSplit index,
        ∑ secondSplit : DerivativeSplit (upperDerivativeIndex index firstSplit), family ⟨index, firstSplit, secondSplit⟩ := by
  classical
  change (PiLp.projₗ 2 (𝕜 := ℂ) (fun _ : DerivativeIndex grade => DiskL2 dimension) index) _ = _
  rw [map_sum]
  change ∑ allocation : APAllocation grade,
    (PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 dimension) (apOutputIndex allocation) (family allocation)) index = _
  simp only [APAllocation, Fintype.sum_sigma, apOutputIndex, PiLp.single_apply]
  rw [Finset.sum_eq_single index]
  · simp only [ite_true]
  · intro other _ different
    simp only [Ne.symm different, ite_false, Finset.sum_const_zero]
  · simp

theorem apSingleRow_smul {dimension grade : ℕ} (index : DerivativeIndex grade) (scalar : ℂ) (value : DiskL2 dimension) :
    scalar • PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 dimension) index value =
      PiLp.single 2 index (scalar • value) := by
  apply PiLp.ext
  intro other
  simp only [PiLp.smul_apply, PiLp.single_apply]
  split_ifs <;> simp only [smul_zero]

end Grad.GaugeCoefficients.Physical.RadialLedger
