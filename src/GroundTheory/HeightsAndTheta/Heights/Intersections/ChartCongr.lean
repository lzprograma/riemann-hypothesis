module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherSide
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StFnDegAdjoin
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartScalingIndep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StAdjoinIndepRelfinrank
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StFinrankAdjoinRange
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRankAdjoin
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VerticalDegreeAfterAdjoining.chart_congr {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by
  subst h
  rfl

theorem VerticalDegreeAfterAdjoining.proof (hA : RankAdjoinFrac.Statement) (hB : FnDegAdjoin.Statement)
    (hT : ChartScalingIndep.Statement) (hC : AdjoinIndepRelfinrank.Statement)
    (hD : FinrankAdjoinRange.Statement) : VerticalDegreeAfterAdjoining.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n i' hv hp hW _ hc G'

  have hpΩ : ((p : ℕ) : G'.Φ') = 0 := by
    have h : ((p : ℕ) : MRing ι') ∈ RingHom.ker (aeval G'.x' : MRing ι' →ₐ[ℤ] G'.Φ') := G'.genericFibre_ker_target.symm ▸ hp
    rwa [RingHom.mem_ker, map_natCast] at h
  have : CharP G'.Φ' p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpΩ
  have : CharP G'.Φ p := ((algebraMap G'.Φ G'.Φ').charP_iff_charP p).2 inferInstance
  let : Algebra (ZMod p) G'.Φ' := ZMod.algebra _ p
  let : Algebra (ZMod p) G'.Φ := ZMod.algebra _ p
  have : IsScalarTower (ZMod p) G'.Φ G'.Φ' := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)

  have hker : RingHom.ker (aeval G'.x' : MRingOver (ZMod p) ι' →ₐ[ZMod p] G'.Φ') =
      W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))) := by
    ext g
    obtain ⟨f, rfl⟩ := PointVertical.red_surjective (ι := ι') p g
    have e : aeval G'.x' (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = aeval G'.x' f := by
      rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
    rw [PointVertical.mem_map_red_iff p hp, RingHom.mem_ker, e, ← RingHom.mem_ker, G'.genericFibre_ker_target]
  rw [← hker] at hW hc ⊢
  have hx : ∀ k', G'.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h => hc k' (by rw [RingHom.mem_ker, aeval_X, h])
  have hmh := hW.1.2.1
  let y' : (Σ k', ι' k') → G'.Φ' := fun q => G'.x' q / G'.x' ⟨q.1, i' q.1⟩
  refine Eq.trans (hB (ZMod p) G'.Φ' K ι K' ι' v G'.x' i' hx hmh)
    (Eq.trans (hA (ZMod p) G'.Φ' _ _ (Set.range_comp_subset_range v y'))
      (SemilocRankAdjoin.chain hT G' i' (ZMod p) hv hx hmh))

end GroundTheory.Heights₂.Heights.Inter
