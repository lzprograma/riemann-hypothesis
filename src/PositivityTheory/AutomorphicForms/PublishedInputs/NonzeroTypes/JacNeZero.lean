module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

@[expose] public section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp
variable {n : ℕ} (G : Grp k n)

theorem jac_ne_zero (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k))
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π)
    (x : V) (hx0 : x ≠ 0) (hx : x ∈ G.Eig π) :
    (Submodule.Quotient.mk x : Jacquet π (unipRad k G.e)) ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := hun
  intro h0
  obtain ⟨m, hm⟩ := hjK hcb hccB hΔU hΔM hJmul hJinv hlM hiw hTE hlU ϖ hϖ V π hs x hx h0
  rw [hTp hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw hTE ϖ hϖ V π x hx m] at hm
  apply hx0
  clear hx0 h0
  induction m generalizing x with
  | zero => simpa using hm
  | succ m ih =>
    rw [Function.iterate_succ_apply] at hm
    exact hTI hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hlU hiw hPJ hkill hni hTE hKC ϖ hϖ V π hs x hx
      (ih _ ((hTE hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw ϖ hϖ 1).2 V π x hx) hm)

end Grp
end UpperTheory.TNZ
