module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRegAboveWeight
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBdPtsNull
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDivisorPreimageNull
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartFun
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartMollifiedBounds
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh

@[expose] public section
set_option maxSynthPendingDepth 1
noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular

theorem RegAboveWeight.proof (hBd : BdPtsNull.Statement) (hDiv : DivisorPreimageNull.Statement) :
    RegAboveWeight.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨C, t₀, ht₀, hb⟩ := ChartMollifiedBounds.proof
    TruncPsh.proof X.M.Xc D.n X.M.atlas X.S.R X.S.ρ
  obtain ⟨t₂, ht₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 <|
    (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀)).and
      (X.S_tied.K_tendsto.eventually_ge_atTop 0)
  refine ⟨t₂, ht₂, D.Bd ∪ {z | X.M.proj z ∉ X.S.R.Yo}, ?_, fun t ht htt z hz hzN => ?_⟩
  · intro Ψ' hΨ'
    refine measure_mono_null (fun y hy => ?_)
      (measure_union_null (hBd II Ψ K ι Ω E D Ψ' hΨ') (hDiv K ι _ _ X.M X.S.R Ψ' hΨ'))
    obtain ⟨z, hz, h, hzy⟩ := hy
    exact Or.elim h (fun h => Or.inl ⟨z, hz, h, hzy⟩) (fun h => Or.inr ⟨z, hz, h, hzy⟩)
  obtain ⟨htt₀, hK⟩ : t < t₀ ∧ 0 ≤ X.S.K t := hsub ⟨ht, htt⟩
  have hY : X.M.proj z ∈ X.S.R.Yo := Classical.byContradiction fun h => hzN (Or.inr h)
  obtain ⟨k, hk⟩ := X.S.R.cover (X.M.proj z)
  have hkm := X.S.R.inner_subset_mid k hk
  let F := fun j x => X.S.R.phReg X.S.ρ (X.S.K t) t j x + 4 * X.S.e1 t * X.S.η j x
  have hglue := LogLogRegularisation.le_glue X.S.R.toPotentialCharts F (ht.le.trans (X.S.e1_ge t ht)) hkm
  simp only [F, X.S.cutoff.eq_zero k (X.M.proj z) hk, mul_zero, add_zero] at hglue
  rw [show X.S.regWeight t (X.M.proj z) = X.S.R.glue F (X.S.e1 t) (X.M.proj z) from rfl,
    show phMu X.H z = Real.log ((muLine X.H).h z) from rfl]
  linarith [((hb t ht htt₀).2 (X.S.K t) hK k (X.M.proj z) hkm).2.2 hY,
    X.S.ph_eq z ⟨Set.mem_sdiff_of_mem hz (fun h => hzN (Or.inl h)), hz⟩ hY]

end GroundTheory.Heights₂.Heights.LowerBoundFree
