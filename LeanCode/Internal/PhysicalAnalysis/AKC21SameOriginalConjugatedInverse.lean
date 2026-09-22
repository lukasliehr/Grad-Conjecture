import AKC20ActualJetAndFixedFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 350000
open Set
open scoped Topology ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity

/-- The original inverse inherits every finite radial order at the unchanged
analytic width. Its accepted low-moment ball is used exactly once. -/
theorem SmoothConjugatedFamily.negativeInverse {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} (bounded : lower < 1)
    {kernel : (radius : RadialPoint) → RadialKernel parameters radius dimension dimension}
    (smooth : SmoothConjugatedFamily parameters lower positive bounded.le kernel)
    (regular : RegularKernelFamily kernel)
    (low : ℝ) (lowNonnegative : 0 ≤ low) (lowSmall : low < 1)
    (small : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernel radius) ≤ low) :
    SmoothConjugatedFamily parameters lower positive bounded.le (fun radius =>
      fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (kernel radius) low (small radius) lowSmall) := by
  let forward := fun grade radius => bulkKernelAction parameters grade (collarRadius lower positive bounded.le radius)
    (fullKernelNegativeIdentityPerturbation (radialKernelParameters parameters (collarRadius lower positive bounded.le radius))
      (kernel (collarRadius lower positive bounded.le radius)))
  let inverseKernel := fun radius =>
    fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (kernel radius) low (small radius) lowSmall
  let inverse := fun grade radius => bulkKernelAction parameters grade (collarRadius lower positive bounded.le radius)
    (inverseKernel (collarRadius lower positive bounded.le radius))
  have inverseRegular : RegularKernelFamily inverseKernel :=
    regular.negativeInverse (identityRadialKernel_regular parameters dimension) low lowNonnegative lowSmall small
  apply FiniteGradeSmooth.inverse parameters dimension (Icc lower 1) (uniqueDiffOn_Icc bounded) forward inverse
  · intro grade radius _
    exact (bulkKernelAction_inverse parameters grade _ _ low (small _) lowSmall).1
  · intro grade radius _
    exact (bulkKernelAction_inverse parameters grade _ _ low (small _) lowSmall).2
  · exact smoothConjugatedFamily_coherent parameters lower positive bounded.le inverseKernel
  · intro grade
    exact ⟨4, (radialConjugatedAction_reserved_continuous parameters lower positive bounded.le inverseKernel inverseRegular grade).continuousOn⟩
  · dsimp only [forward, fullKernelNegativeIdentityPerturbation]
    exact SmoothConjugatedFamily.sub (parameters := parameters) (lower := lower)
      (positive := positive) (bounded := bounded.le) (first := kernel)
      (second := fun radius => fullIdentityKernel (radialKernelParameters parameters radius) dimension)
      smooth (smoothConjugatedFamily_identity parameters lower positive bounded.le dimension)

end Grad.AnnularWeightedSmoothness
