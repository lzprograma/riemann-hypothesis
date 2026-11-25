module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

private theorem mem_R_of_split_coords_integral_congr (hs : M.split = some g) (x : E) (h1 : (g.e x).1 ∈ 𝒪[F])
    (h2 : (g.e x).2 ∈ 𝒪[F]) (hd : ∃ c : 𝒪[F], (g.e x).1 - (g.e x).2 = (g.q : F) * c) : x ∈ M.R := by
  obtain ⟨c, hc⟩ := hd
  unfold Model.R
  rw [hs]
  refine Subring.mem_comap.2 (Subring.mem_map.2 ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, ?_⟩)
  · rw [RingHom.mem_eqLocus]
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨c, Subtype.ext ?_⟩
    simp [hc, mul_comm]
  · rfl

theorem zsig_mem (hs : M.split = some g) (T T' : F) (c : 𝒪[F]) (hc : T - T' = (g.q : F) ^ 2 * c)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R)
    (hZ : Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T') (a b : Fin (r + 1)) :
    HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b ∈ M.R := by
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext (by simpa using h))
  have hmem : HermSp.ZZplusOf M Zh T T' b a ∈ M.R := by
    have := congrFun (congrFun hZ b) a
    simp only [Matrix.map_apply, Subring.coe_subtype] at this
    rw [← this]
    exact (Z b a).2
  obtain ⟨u1, u2, d, hd⟩ := comp_of_mem_R hs hmem
  rw [zz_comp hs] at u1 u2 hd
  dsimp only at u1 u2 hd
  have hT : T = T' + (g.q : F) ^ 2 * c := by linear_combination hc
  by_cases hab : a = Fin.last r ∧ b = Fin.last r
  · simp only [ite_eq_left hab.symm] at u1 u2 hd
    refine mem_R_of_split_coords_integral_congr hs _ ?_ ?_ ⟨d, ?_⟩
    all_goals rw [zz_comp hs]
    all_goals simp only [Matrix.map_apply, g.e_cj, Prod.fst_swap, Prod.snd_swap, ite_eq_left hab]
    · rw [show (g.e (Zh a b)).2 / (g.q : F) - -T / g.q =
          -(-((g.e (Zh a b)).2 / g.q) - T' / g.q) + g.q * c by rw [hT]; field_simp; ring]
      exact add_mem (neg_mem u2) (mul_mem g.q.2 c.2)
    · rw [show -((g.e (Zh b a)).1 / (g.q : F)) - T' / g.q =
          -((g.e (Zh b a)).1 / g.q - -T / g.q) + g.q * c by rw [hT]; field_simp; ring]
      exact add_mem (neg_mem u1) (mul_mem g.q.2 c.2)
    · rw [← hd]
      ring
  · have hba : ¬(b = Fin.last r ∧ a = Fin.last r) := fun h => hab (And.symm h)
    simp only [ite_eq_right hba] at u1 u2 hd
    refine mem_R_of_split_coords_integral_congr hs _ ?_ ?_ ⟨d, ?_⟩
    all_goals rw [zz_comp hs]
    all_goals simp only [Matrix.map_apply, g.e_cj, Prod.fst_swap, Prod.snd_swap, ite_eq_right hab]
    · rw [show (g.e (Zh a b)).2 / (g.q : F) - 0 = -(-((g.e (Zh a b)).2 / g.q) - 0) by ring]
      exact neg_mem u2
    · rw [show -((g.e (Zh b a)).1 / (g.q : F)) - 0 = -((g.e (Zh b a)).1 / g.q - 0) by ring]
      exact neg_mem u1
    · rw [← hd]
      ring

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
