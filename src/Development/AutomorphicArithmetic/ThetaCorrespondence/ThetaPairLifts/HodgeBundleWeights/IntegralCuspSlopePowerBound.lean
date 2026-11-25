module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TamagawaPeterssonLambdaSqNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeBergmanBoundGoodCover
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

@[expose] public section

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open scoped GlobalTheory.CompHt
namespace GlobalTheory.BergRank
theorem _root_.UpperTheory.Lit.Tam.tamagawa_number_formula : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z, BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  refine ⟨4000, by norm_num, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hsz hfr ho la hla hS Z
  exact GlobalTheory.BergRank.berg_sup_rank_of_const D T hT j hj Y e o hY Lb hLb hsz la hS Z
    (MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d Y.d.l₂.M)
    (fun w hw1 hlogw => UpperTheory.Lit.Tam.supConst2Bounds D Y.d.l₂.M Lb w
      (by have := Y.d.l₂.three_le; omega) hLb hM hsz hfr hw1 hlogw)
    fun hL w hw hsp σ hσ y hy => UpperTheory.Lit.Tam.tamagawaPeterssonLambdaSq_nonneg trivial D j _ _ _ _ _
      Y.U Y.dict hL σ hσ (wtOf _ la 0) (AllWt.even_wtOf la 0) w hw (hsp σ hσ) Z y hy
end GlobalTheory.BergRank
end
end
