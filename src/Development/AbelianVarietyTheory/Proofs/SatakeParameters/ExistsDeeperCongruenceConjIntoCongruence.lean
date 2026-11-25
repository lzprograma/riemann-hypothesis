module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.IndefiniteReal.CongNatCastEqOneTmul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

namespace GlobalTheory.ConjCong

theorem exists_cong_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (g : GAf L n), 0 < N → ∃ M : ℕ, 0 < M ∧ ∀ κ, NG.Cong L n (N * M) κ → NG.Cong L n N (g⁻¹ * κ * g) := by
  intro L _ _ _ n N g hN
  obtain ⟨M, hM, h⟩ := Formalism.IndefR.principalLevelFrame.congConj_holds L n g N hN
  exact ⟨M, hM, fun κ hκ => h κ (NG.Cong.of_mul_right L n hκ)⟩

end GlobalTheory.ConjCong
