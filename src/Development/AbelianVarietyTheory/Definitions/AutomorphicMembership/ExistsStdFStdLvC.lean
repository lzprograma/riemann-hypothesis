module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix


namespace GlobalTheory.Mem.Col2.StdModel

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

section Ker

variable {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}

theorem stdKer_iff (t : KerEntTied ex) : I.StdKer l Z t ↔ I.StdKerTie l Z t :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩⟩

end Ker




end GlobalTheory.Mem.Col2.StdModel

end
