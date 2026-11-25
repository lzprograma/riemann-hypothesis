module
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import Mathlib.RingTheory.RegularLocalRing.Defs
@[expose] public section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open ReciprocityTheory.ChartRestriction.G.Geo (coneMap)
theorem exists_ne_zero_of_isSubvar {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {d : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  exact ⟨i, fun h0 => hi (show MvPolynomial.X i ∈ RingHom.ker (coneMap F x) from by
    simp [RingHom.mem_ker, coneMap, h0])⟩

theorem VeryAmpleNefPlusAmple.equiv (hBun : BundleOfDeg.Statement) (hNef : ModelNefEq.Statement)
    (hVA : ModelVeryAmpleEq.Statement) (hDim : ModelDimEq.Statement) :
    Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement := by
  constructor
  · intro hA d F _ K _ _ ι _ Ω _ _ y k₀ hmod hdim μ hnef t ht
    obtain ⟨i₀, -⟩ := hmod.1 k₀
    let e := (Fintype.equivFin (ι k₀)).trans (finCongr (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.mpr ⟨i₀⟩)).symm)
    obtain ⟨Q, hQ⟩ := hBun F K ι Ω y k₀ _ e hmod μ
    obtain ⟨p, m, hp, hm, hva⟩ := hA F d Ω _ _ Q ((hDim F K ι Ω y k₀ _ e hmod d).mpr hdim)
      ((hNef F K ι Ω y k₀ _ e hmod μ Q hQ).mpr hnef) t ht
    exact ⟨p, m, hp, hm, (hVA F K ι Ω y k₀ _ e hmod μ Q hQ p m hp).mp hva⟩
  · intro hB k _ d Ω _ _ N x M hs hnef t ht
    obtain ⟨n, hn⟩ := Generated.full.{0, 0} k Ω N x M
    obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators (M.tensorProd (twistBundle k x n)) (hn n le_rfl)
    have hmod := GraphModel.full k N Ω x M n (r + 1) g (exists_ne_zero_of_isSubvar hs) hg
    have hsec := twist_secs_eq_secOver M n g hg
    obtain ⟨a, m, ha, hm, hva⟩ := hB d k _ _ Ω (graphVec x g) baseBlock hmod
      ((hDim k _ _ Ω (graphVec x g) baseBlock N (Equiv.refl _) hmod d).mp hs) (graphDeg n)
      ((hNef k _ _ Ω (graphVec x g) baseBlock N (Equiv.refl _) hmod (graphDeg n) M hsec).mp hnef) t ht
    exact ⟨a, m, ha, hm, (hVA k _ _ Ω (graphVec x g) baseBlock N (Equiv.refl _) hmod (graphDeg n) M hsec a m ha).mpr hva⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
