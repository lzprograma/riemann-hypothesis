module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity

@[expose] public section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

theorem UpperTheory.One.M.isQg_of_over (D : D7) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    UpperTheory.One.M.IsQg (w.adicCompletion D.host.E) := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have key : Function.Surjective (Formalism.BasicNotions.Examples₂.LocF.emb w (D.host.g k) hw) := by
    refine GlobalTheory.TypeRec.Model.emb_surjective _ _ _ (fun h => ?_)
      (by
        simpa [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
          (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw))
    have h0 : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (D.host.g_prime k).ne_zero
    have hs := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2
      (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard (D.host.g_prime k) (D.nd.g_split k)).2
    have := hs w.asIdeal (by rw [← sq, Ideal.dvd_span_singleton]; exact h)
    exact w.isPrime.ne_top (Ideal.isUnit_iff.1 this)
  exact ⟨_, this, RingEquiv.ofBijective _ ⟨RingHom.injective _, key⟩, Formalism.BasicNotions.Examples₂.LocF.emb_cont _ _ hw⟩

end

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
namespace GlobalTheory.DepthZeroLoc

end GlobalTheory.DepthZeroLoc
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
namespace GlobalTheory.DepthZeroTame

end GlobalTheory.DepthZeroTame
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open scoped Pointwise
namespace GlobalTheory.DepthZeroType

end GlobalTheory.DepthZeroType
end
