module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoSmulCocompact

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

abbrev HS (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)

abbrev HT (I : Type) [Fintype I] (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : I => HS Wp Wq)

structure VecHyp {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) : Prop where
  hc : ∀ i, 0 ≤ c i
  hFi : ∀ i, KB.CptCoef p.T.base (Fi i)
  gram : ∀ Q Q' : C.LPt, TBB.NP p nn F (P.r + 1) w Q Q' =
    ∑ i, (c i : ℂ) * ⟪(omT p w.length Q' : ℂ) • L i (p.V (Fi i) Q'), (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)⟫_ℂ
  int : ∀ a : C.LPt, D.IsLocPt a P.r →
    Integrable (fun c : ℂ => TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a ++ [(1, c)]))
  fibre : ∀ a a' : C.LPt, D.IsLocPt a P.r → D.IsLocPt a' P.r →
    TBB.NP p nn F P.r w a a' = ∫ c : ℂ, TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])
  cont : ∀ i (m : ℕ) (h : C.LPt), (∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) → 1 ≤ m → D.ptSize h + m = P.r + 1 →
    ContinuousOn (fun c : ℂ => (omT p w.length (h ++ [(m, c)]) : ℂ) • p.V (Fi i) (h ++ [(m, c)])) {0}ᶜ

end

end Formalism.FourierDecayAlt.P.CutBP.GT
