import AKO14ActualCompatibleIncomingFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Grad.AnnularIncomingIntegrability
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularRestriction

/-- Full EX incoming consumer. A compatible family of actual retained fields,
with uniform grade-zero and SAME inserted-grade-one norms, has a canonical
measurable incoming norm and one geometric sequence along which the original
full high/low incoming boundary pair tends to zero. No trace regularity,
measurability, density fidelity or logarithmic integrability is assumed. -/
theorem actualCompatibleFamily_common_vanishing_radii
    (upper length : ℝ) (upperPositive : 0 < upper) (upperBounded : upper < 1) (lengthPositive : 0 < length)
    (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index) (bounded : ∀ index, collars index < 1)
    (decreasing : Antitone collars) (cofinal : Tendsto collars atTop (𝓝 0))
    (fields weighted : ∀ index, CoupledSpace (collars index) length (positive index) lengthPositive)
    (compatible : ActualRetainedFamilyCompatible length lengthPositive collars positive bounded decreasing fields)
    (inserted : ∀ index, CoupledInsertedGrade (collars index) length (positive index) lengthPositive 1 (fields index) (weighted index))
    (retainedBound insertedBound : ℝ)
    (retained : ∀ index, ‖fields index‖ ≤ retainedBound)
    (insertedNorm : ∀ index, ‖weighted index‖ ≤ insertedBound)
    (exceptional : Set ℝ) (null : volume exceptional = 0) :
    ∃ (radii : ℕ → ℝ) (inside : ∀ index, radii index ∈ Ioc 0 upper),
      (∀ index, radii index ∉ exceptional) ∧
      (∀ index, radii (index + 1) < radii index / 2) ∧
      StrictAnti radii ∧
      (∀ index, actualFamilyIncomingNorm upper length lengthPositive collars positive bounded fields (radii index) < 1 / ((index : ℝ) + 1)) ∧
      Tendsto radii atTop (𝓝 0) ∧
      Tendsto (actualFamilyIncomingNorm upper length lengthPositive collars positive bounded fields ∘ radii) atTop (𝓝 0) ∧
      (∀ (stage index : ℕ) (included : collars index ≤ radii stage),
        ‖coupledIncomingTrace (radii stage) length ((positive index).trans_le included)
          ((inside stage).2.trans_lt upperBounded)
          lengthPositive
          (coupledEndpointRestriction (collars index) (radii stage) length (positive index) ((positive index).trans_le included)
            ((inside stage).2.trans_lt upperBounded) lengthPositive included (fields index))‖ < 1 / ((stage : ℝ) + 1)) := by
  have selected := actualRetainedFamily_common_vanishing_radii upper length upperPositive upperBounded.le lengthPositive
    collars positive bounded decreasing cofinal fields weighted inserted
    (actualFamilyIncomingNorm upper length lengthPositive collars positive bounded fields)
    (actualFamilyIncomingNorm_measurable upper length lengthPositive collars positive bounded fields)
    (fun radius _ => actualFamilyIncomingNorm_nonnegative upper length lengthPositive collars positive bounded fields radius)
    (by
      intro index
      filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
      exact actualFamilyIncomingNorm_square upper length upperBounded lengthPositive collars positive bounded decreasing fields
        cofinal compatible index radius inside)
    retainedBound insertedBound retained insertedNorm exceptional null
  obtain ⟨radii,inside,avoids,geometric,strict,incomingBound,toAxis,toZero⟩ := selected
  refine ⟨radii,inside,avoids,geometric,strict,incomingBound,toAxis,toZero,?_⟩
  intro stage index included
  have actual := actualFamilyIncomingNorm_eq_trace upper length upperBounded lengthPositive collars positive bounded decreasing fields
    compatible index (radii stage) ⟨included,(inside stage).2⟩
  exact actual.symm.trans_lt (incomingBound stage)

end Grad.AnnularIncomingIntegrability
