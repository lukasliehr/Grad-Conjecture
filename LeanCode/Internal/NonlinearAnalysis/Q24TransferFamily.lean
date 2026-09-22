import Q24ActualTransfer
import Q23SeedChartFamilies

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisCore Grad.SmoothingFamily Grad.RealFixedRanges Grad.ImplementationReadiness

/-- The parameter-smooth completed seed operator and Q24's dense
extension are exactly the same actual N18 operator. -/
theorem completedSeedTransferFamily_agrees (parameters : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (field : AGrade parameters 3 grade) :
    completedSeedTransferFamily parameters grade reference seed field =
      completedSeedTransfer parameters reference insideR seed insideS grade field := by
  refine isClosed_property (fieldEmbed_denseRange parameters 3 grade)
    (isClosed_eq (completedSeedTransferFamily parameters grade reference seed).continuous
      (completedSeedTransfer parameters reference insideR seed insideS grade).continuous) ?_ field
  intro core
  exact (completedSeedTransferFamily_core parameters grade reference insideR seed insideS core).trans
    (completedSeedTransfer_core parameters reference insideR seed insideS grade core).symm

/-- The actual transfer with a moving seed, on the full original state
completion. The product here is a calculus chart, not a replacement norm
for the final one-high estimate. -/
def completedReferenceTransferFamily (parameters : PhaseParameters)
    (reference : Seed.Parameters) (grade : ℕ)
    (pair : Seed.Parameters × XAmbient parameters grade) : XAmbient parameters grade :=
  statePack pair.2.ofLp.1
    (completedSeedTransferFamily parameters grade reference pair.1 pair.2.ofLp.2.ofLp.1)
    pair.2.ofLp.2.ofLp.2

def movingSeedDomain (parameters : PhaseParameters) (grade : ℕ) :
    Set (Seed.Parameters × XAmbient parameters grade) :=
  {pair | pair.1 ∈ Seed.parameterDomain}

theorem movingSeedDomain_isOpen (parameters : PhaseParameters) (grade : ℕ) :
    IsOpen (movingSeedDomain parameters grade) :=
  Seed.parameterDomain_isOpen.preimage continuous_fst

theorem completedReferenceTransferFamily_contDiffOn (parameters : PhaseParameters)
    (reference : Seed.Parameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedReferenceTransferFamily parameters reference grade)
      (movingSeedDomain parameters grade) := by
  have seedOperators : ContDiffOn ℝ ∞
      (fun pair : Seed.Parameters × XAmbient parameters grade =>
        completedSeedTransferFamily parameters grade reference pair.1)
      (movingSeedDomain parameters grade) :=
    (completedSeedTransferFamily_contDiffOn parameters grade reference).comp
      contDiff_fst.contDiffOn (fun _ inside => inside)
  have axes : ContDiff ℝ ∞ (fun pair : Seed.Parameters × XAmbient parameters grade => pair.2.ofLp.1) :=
    (stateAxis_contDiff parameters grade).comp contDiff_snd
  have fields : ContDiff ℝ ∞ (fun pair : Seed.Parameters × XAmbient parameters grade => pair.2.ofLp.2.ofLp) :=
    (stateFields_contDiff parameters grade).comp contDiff_snd
  have transferred := q23ContDiffOn_complexCLM_apply seedOperators fields.fst.contDiffOn
  exact (WithLp.prodContinuousLinearEquiv 1 ℝ (AxisGrade parameters 2 (grade + 1))
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).symm.contDiff.comp_contDiffOn
      (axes.contDiffOn.prodMk
        ((WithLp.prodContinuousLinearEquiv 1 ℝ (AGrade parameters 3 grade)
          (AGrade parameters 1 grade)).symm.contDiff.comp_contDiffOn
            (transferred.prodMk fields.snd.contDiffOn)))

theorem completedReferenceTransferFamily_agrees (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (state : XAmbient parameters grade) :
    completedReferenceTransferFamily parameters reference grade (seed, state) =
      completedReferenceTransfer parameters reference insideR seed insideS grade state := by
  unfold completedReferenceTransferFamily completedReferenceTransfer
  rw [completedSeedTransferFamily_agrees parameters grade reference insideR seed insideS]

end Grad.Q24Realization
