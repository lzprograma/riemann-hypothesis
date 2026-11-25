module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.ConjTwist.Test

open GlobalTheory.ExportSeries

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

open Classical in
theorem splitSet_Pg {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) : SplitSet (R.Pg ∪ R.Q t) := by
  obtain ⟨-, e, he, -⟩ := hC.thP.vP i t
  exact ⟨e, by convert he⟩

theorem levS_chars {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B) (hL : R.toLevCh.Is A.μ0) (hB : B.Good) {ψ : Twist D Circle}
    (hψ : ψ.Good) (hQ : B.admitted ψ.Q) {t : T0} (ht : IsTupOf R B ψ t) :
    (B.levS ψ).Pg = (R.datVt i t).Pg ∧ (B.levS ψ).Q = (R.datVt i t).Q ∧
      (∀ c, ∀ PP ∈ R.Pg, (B.levS ψ).cg c PP = (R.datVt i t).cg c PP) ∧
      ∀ PP ∈ R.Q t, (B.levS ψ).xq PP = (R.datVt i t).xq PP :=
  ⟨h.Pg, by rw [show (R.datVt i t).Q = R.Q t from rfl, ht.2]; rfl, fun _ _ hPP => h.muC_eq hL hB hPP,
    fun _ hPP => (ht.xiR_eq hL hB hψ hQ hPP).symm⟩

end GlobalTheory.ConjTwist.Test
