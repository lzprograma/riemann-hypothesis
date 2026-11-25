module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem ptField_main : ∀ D : D7, IsTotallyComplex D.what₂.LL ∧ (∃ v0 : InfinitePlace D.what₂.LL, Formalism.DivisionValues.IsConjAt v0) ∧ ∀ (u : D.what₂.Word) (c : (D.fm u).clsP), Nat.card ((D.fm u).stabilizer₂ c) ∣ (D.mem u).C.DGam := by
  intro D
  refine ⟨D.tcLL, _root_.GlobalTheory.exists_isConjAt_of_embedding D.what₂.LL ⟨D.what₂.embLL, D.starLL_cx⟩, ?_⟩
  intro u c
  exact (Subgroup.card_dvd_of_injective _ ((D.fm u).stabMap_inj c)).trans
    ((D.mem u).C.dvd_DGam _ le_rfl _)

end GlobalTheory
