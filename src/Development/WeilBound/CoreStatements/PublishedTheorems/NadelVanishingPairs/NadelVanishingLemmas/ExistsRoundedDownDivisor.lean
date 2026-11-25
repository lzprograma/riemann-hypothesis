module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicities
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

theorem exists_cartierDiv_mult_ediv : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (Γ : CartierDiv Y) (m : ℕ), ∃ F : CartierDiv Y, (∀ z, F.mult z = Γ.mult z / (m : ℤ)) ∧ F.supp ≤ Γ.supp := by
  intro k _ _ Y _ _ q n _ hproj Γ m
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hufd : ∀ x : Y, UniqueFactorizationMonoid (Y.presheaf.stalk x) :=
    fun x => AbelianProjective.ufd_stalk (K := k) q x
  have : GlobalTheory.IsNormalScheme Y := GlobalTheory.isNormalScheme_of_smooth q
  haveI : NoetherianSpace Y := ModelSum.noetherianSpace_of_isProjOver hproj
  haveI : CompactSpace Y := ⟨NoetherianSpace.isCompact _⟩
  have hsupp : Function.support (fun z => Γ.mult z / (m : ℤ)) ⊆ Function.support Γ.mult := by
    intro z hz h0
    apply hz
    simp only [h0, Int.zero_ediv]
  obtain ⟨F, hF⟩ := CartierDiv.exists_mult_eq_of_locallyFactorial Y hufd
    (fun z => Γ.mult z / (m : ℤ)) ((CartierDiv.finite_support_mult Γ).subset hsupp)
    (fun z hz => CartierDiv.coheight_eq_one_of_mult_ne_zero (hsupp hz))
  refine ⟨F, hF, ?_⟩
  intro x hx
  obtain ⟨_, hsuppF, _, _⟩ := MultEff.eff_supp_eq_of_mult Y F
  obtain ⟨z, hz, hzF⟩ := (hsuppF x).mp hx
  rw [hF z] at hzF
  exact hz.mem_closed Γ.supp.isClosed (CartierDiv.mem_supp_of_mult_ne_zero (hsupp hzF))

end GlobalTheory
