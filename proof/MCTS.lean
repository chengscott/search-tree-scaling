import Mathlib

open Filter MeasureTheory
open scoped Asymptotics Topology BigOperators ENNReal

namespace MCTSCharacterization

universe u v

notation f " =O[∞] " g => f =O[atTop] g
notation f " =Ω[∞] " g => g =O[atTop] f
notation f " =Θ[∞] " g => f =Θ[atTop] g
notation f " =o[∞] " g => f =o[atTop] g

/--
If two eventually nonnegative functions satisfy `c * g n ≤ f n ≤ C * g n` eventually,
then `f = Θ(g)`.
-/
private theorem theta_of_eventual_sandwich
    {f g : ℕ → ℝ}
    (hf_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ f n)
    (hg_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ g n)
    (hupper : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, f n ≤ C * g n)
    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * g n ≤ f n) :
    f =Θ[∞] g := by
  rcases hupper with ⟨C, hC, hupper_ev⟩
  rcases hlower with ⟨c, hc, hlower_ev⟩
  constructor
  · exact Asymptotics.IsBigO.of_bound C <| by
      filter_upwards [hf_nonneg, hg_nonneg, hupper_ev] with n hfn hgn hup
      simpa [Real.norm_eq_abs, abs_of_nonneg hfn, abs_of_nonneg hgn] using hup
  · exact Asymptotics.IsBigO.of_bound (1 / c) <| by
      filter_upwards [hf_nonneg, hg_nonneg, hlower_ev] with n hfn hgn hlo
      have hle : g n ≤ f n / c := (le_div_iff₀ hc).2 (by linarith)
      simpa [Real.norm_eq_abs, abs_of_nonneg hgn, abs_of_nonneg hfn,
        div_eq_mul_inv, mul_comm] using hle

/-! ## MCTS model -/

structure MCTSModel where
  State : Type u
  Action : State → Type v
  prior : ∀ s : State, Action s → ℝ
  prior_nonneg : ∀ s a, 0 ≤ prior s a
  prior_sum : ∀ s, ∑' a, prior s a = 1
  value : ∀ s : State, Action s → ℝ
  searchValue : ∀ s : State, Action s → ℕ → ℝ
  parentVisit : State → ℕ → ℕ
  childVisit : ∀ s : State, Action s → ℕ → ℕ
  isTerminal : State → Prop
  selectedAt : ∀ s : State, Action s → ℕ → Prop
  isBest : ∀ s : State, Action s

  selection_disjoint :
    ∀ s : State, ∀ a b : Action s, ∀ t : ℕ,
      b ≠ a → selectedAt s b t → ¬ selectedAt s a t

namespace MCTSModel

variable (M : MCTSModel)

def Gap (s : M.State) (a : M.Action s) : ℝ :=
  M.value s (M.isBest s) - M.value s a

def Suboptimal (s : M.State) (a : M.Action s) : Prop :=
  a ≠ M.isBest s

noncomputable def puctScore
    (c : ℝ) (s : M.State) (a : M.Action s) (t : ℕ) : ℝ :=
  M.searchValue s a t +
    c * M.prior s a * Real.sqrt (M.parentVisit s t : ℝ) /
      (1 + (M.childVisit s a t : ℝ))

def arrivalCount (s : M.State) (t : ℕ) : ℕ := M.parentVisit s t + 1

def SelectedInfinitelyOften (s : M.State) (a : M.Action s) : Prop :=
  ∀ t0 : ℕ, ∃ t ≥ t0, M.selectedAt s a t

def NonSelectedInfinitelyOften (s : M.State) (a : M.Action s) : Prop :=
  ∀ t0 : ℕ, ∃ t ≥ t0, (∃ b, M.selectedAt s b t) ∧ ¬ M.selectedAt s a t

def ValueConsistent (s : M.State) (a : M.Action s) : Prop :=
  Tendsto (fun t : ℕ => M.searchValue s a t) atTop (𝓝 (M.value s a))

/-- Pointwise value convergence at infinitely visited states. -/
def ValueConsistency : Prop :=
  ∀ s : M.State, Tendsto (M.parentVisit s) atTop atTop →
    ∀ a : M.Action s, M.ValueConsistent s a

def UniformValueConsistency : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℕ, ∀ s a t,
    m₀ ≤ M.parentVisit s t → |M.searchValue s a t - M.value s a| ≤ ε

/-- Count identities along the reached optimal path. -/
def OptimalPathEdges (V : ℕ → ℕ) (H : ℕ)
    (state : ℕ → M.State) (time : ℕ → ℕ) : Prop :=
  ∀ x < H, ¬ M.isTerminal (state x) ∧
    V x = M.arrivalCount (state x) (time x) ∧
    V (x + 1) = M.childVisit (state x) (M.isBest (state x)) (time x)

/-- A nonterminal frontier with an unvisited optimal child. -/
def OptimalFrontier (V : ℕ → ℕ) (H : ℕ)
    (state : ℕ → M.State) (time : ℕ → ℕ) : Prop :=
  V H = M.arrivalCount (state H) (time H) ∧
    ¬ M.isTerminal (state H) ∧
    M.childVisit (state H) (M.isBest (state H)) (time H) = 0

/-- Use root arrival count `n + 1` for `n` completed simulations. -/
def OptimalPathCounts (V : ℕ → ℕ) (H root : ℕ)
    (state : ℕ → M.State) (time : ℕ → ℕ) : Prop :=
  V 0 = root ∧
    V H = M.arrivalCount (state H) (time H) ∧
    ¬ M.isTerminal (state H) ∧
    M.childVisit (state H) (M.isBest (state H)) (time H) = 0 ∧
    M.OptimalPathEdges V H state time

def CappedOptimalPathCounts (V : ℕ → ℕ) (H root L : ℕ)
    (state : ℕ → M.State) (time : ℕ → ℕ) : Prop :=
  V 0 = root ∧ H ≤ L ∧
    (H < L → M.OptimalFrontier V H state time) ∧
    M.OptimalPathEdges V H state time

end MCTSModel

structure MCTSModel.CountUpdates (M : MCTSModel) : Prop where
  parent_initial : ∀ s, M.parentVisit s 0 = 0
  child_initial : ∀ s a, M.childVisit s a 0 = 0
  child_le_parent : ∀ s a t, M.childVisit s a t ≤ M.parentVisit s t
  parent_selected : ∀ s a t, M.selectedAt s a t →
    M.parentVisit s (t + 1) = M.parentVisit s t + 1
  child_selected : ∀ s a t, M.selectedAt s a t →
    M.childVisit s a (t + 1) = M.childVisit s a t + 1
  child_idle : ∀ s a t, ¬ M.selectedAt s a t →
    M.childVisit s a (t + 1) = M.childVisit s a t
  parent_idle : ∀ s t, (∀ a, ¬ M.selectedAt s a t) →
    M.parentVisit s (t + 1) = M.parentVisit s t

/-- pUCT with a fixed exploration coefficient. -/
structure MCTSModel.Sequential (M : MCTSModel) (c : ℝ) : Prop extends M.CountUpdates where
  argmax : ∀ s a t, M.selectedAt s a t →
    ∀ b, M.puctScore c s b t ≤ M.puctScore c s a t

/-- pUCT with exploration evaluated at the parent count. -/
structure MCTSModel.Scheduled (M : MCTSModel) (c : ℝ → ℝ) : Prop extends M.CountUpdates where
  argmax : ∀ s a t, M.selectedAt s a t → ∀ b,
    M.puctScore (c (M.parentVisit s t)) s b t ≤ M.puctScore (c (M.parentVisit s t)) s a t

namespace MCTSModel.CountUpdates

variable {M : MCTSModel} (h : M.CountUpdates)
include h

private theorem child_monotone (s : M.State) (a : M.Action s) : Monotone (M.childVisit s a) := by
  apply monotone_nat_of_le_succ
  intro t
  by_cases ha : M.selectedAt s a t
  · rw [h.child_selected s a t ha]; omega
  · rw [h.child_idle s a t ha]

private theorem parent_monotone (s : M.State) : Monotone (M.parentVisit s) := by
  classical
  apply monotone_nat_of_le_succ
  intro t
  by_cases hsel : ∃ a, M.selectedAt s a t
  · obtain ⟨a, ha⟩ := hsel
    exact (h.parent_selected s a t ha).symm ▸ Nat.le_succ _
  · rw [h.parent_idle s t (not_exists.mp hsel)]

/-- Parent counts equal the sum of child counts. -/
private theorem count_identity (s : M.State) [Fintype (M.Action s)] (t : ℕ) :
    M.parentVisit s t = ∑ a, M.childVisit s a t := by
  classical
  induction t with
  | zero => simp [h.parent_initial, h.child_initial]
  | succ t ih =>
    by_cases hsel : ∃ a, M.selectedAt s a t
    · obtain ⟨a, ha⟩ := hsel
      have hupdate : ∀ b, M.childVisit s b (t + 1) =
          M.childVisit s b t + if b = a then 1 else 0 := by
        intro b
        by_cases hb : b = a
        · subst b
          simp [h.child_selected s a t ha]
        · simp [hb, h.child_idle s b t (M.selection_disjoint s b a t (Ne.symm hb) ha)]
      simp [h.parent_selected s a t ha, hupdate, Finset.sum_add_distrib, ih]
    · simpa [h.parent_idle s t (not_exists.mp hsel),
        h.child_idle s _ t (not_exists.mp hsel _)] using ih

private theorem child_tendsto (s : M.State) (a : M.Action s)
    (ha : M.SelectedInfinitelyOften s a) : Tendsto (M.childVisit s a) atTop atTop := by
  apply (h.child_monotone s a).tendsto_atTop_atTop
  intro k
  induction k with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨u, htu, hsel⟩ := ha t
    refine ⟨u + 1, ?_⟩
    rw [h.child_selected s a u hsel]
    have := h.child_monotone s a htu
    omega

private theorem child_eventually_constant (s : M.State) (a : M.Action s)
    (ha : ¬ M.SelectedInfinitelyOften s a) :
    ∃ k : ℕ, ∀ᶠ t in atTop, M.childVisit s a t = k := by
  classical
  simp only [MCTSModel.SelectedInfinitelyOften, not_forall, not_exists, not_and] at ha
  obtain ⟨t₀, hnone⟩ := ha
  refine ⟨M.childVisit s a t₀, ?_⟩
  filter_upwards [eventually_ge_atTop t₀] with t ht
  exact Nat.le_induction rfl (fun u hu ih => (h.child_idle s a u (hnone u hu)).trans ih) t ht

private theorem last_selection_exists (s : M.State) (a : M.Action s) :
    ∀ t, 0 < M.childVisit s a t → ∃ u < t, M.selectedAt s a u ∧
      M.childVisit s a t = M.childVisit s a u + 1 := by
  intro t
  induction t with
  | zero => simp [h.child_initial]
  | succ t ih =>
    intro hpos
    by_cases ha : M.selectedAt s a t
    · exact ⟨t, Nat.lt_succ_self t, ha, h.child_selected s a t ha⟩
    · have heq := h.child_idle s a t ha
      obtain ⟨u, hut, hu, hcount⟩ := ih (by simpa [heq] using hpos)
      exact ⟨u, Nat.lt_succ_of_lt hut, hu, heq.trans hcount⟩

/-- Last selection time, or zero if no selection has occurred. -/
private noncomputable def lastSelection (s : M.State) (a : M.Action s) (t : ℕ) : ℕ :=
  if hp : 0 < M.childVisit s a t then (h.last_selection_exists s a t hp).choose else 0

private theorem lastSelection_spec (s : M.State) (a : M.Action s) (t : ℕ)
    (hp : 0 < M.childVisit s a t) :
    h.lastSelection s a t < t ∧ M.selectedAt s a (h.lastSelection s a t) ∧
      M.childVisit s a t = M.childVisit s a (h.lastSelection s a t) + 1 := by
  simpa [lastSelection, hp] using
    (h.last_selection_exists s a t hp).choose_spec

end MCTSModel.CountUpdates

/-! ## Regularity -/

namespace Assumption

structure Regularity (M : MCTSModel) : Prop where
  finite_branching :
    ∃ b : ℕ, 0 < b ∧ ∀ s : M.State,
      Finite (M.Action s) ∧ Nat.card (M.Action s) ≤ b
  gap_lower :
    ∃ Δmin : ℝ, 0 < Δmin ∧
      ∀ s : M.State, ∀ a : M.Action s,
        M.Suboptimal s a → Δmin ≤ M.Gap s a
  gap_upper :
    ∃ Δmax : ℝ, 0 < Δmax ∧
      ∀ s : M.State, ∀ a : M.Action s,
        M.Suboptimal s a → M.Gap s a ≤ Δmax
  suboptimal_prior :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ s, ¬ M.isTerminal s →
      ∃ a, M.Suboptimal s a ∧ p₀ ≤ M.prior s a

end Assumption

/-! ## Preparatory lemmas -/

/-- Lemma 1: positive-prior actions are selected infinitely often at infinitely visited states. -/
theorem lemma1 {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c)
    (hreg : Assumption.Regularity M)
    (hconsistency : M.ValueConsistency) : (∀ s, Tendsto (M.parentVisit s) atTop atTop →
      ∀ a, 0 < M.prior s a → M.SelectedInfinitelyOften s a) := by
  have hlocal_selection_after {M : MCTSModel} (h : M.CountUpdates)
      (s : M.State) (hs : Tendsto (M.parentVisit s) atTop atTop)
      (t₀ : ℕ) : ∃ t ≥ t₀, ∃ a, M.selectedAt s a t := by
    classical
    by_contra hn
    push Not at hn
    have hev := hs.eventually (eventually_gt_atTop (M.parentVisit s t₀))
    obtain ⟨t, ht, hbig⟩ := ((eventually_ge_atTop t₀).and hev).exists
    have hconst : M.parentVisit s t = M.parentVisit s t₀ :=
      Nat.le_induction rfl (fun u hu ih => (h.parent_idle s u (hn u hu)).trans ih) t ht
    omega
  classical
  intro s hs a hprior
  letI : Finite (M.Action s) := hreg.finite_branching.choose_spec.2 s |>.1
  have hscore_limit (b : M.Action s) (B : ℝ)
      (hbonus : Tendsto (fun t => c * M.prior s b /
        (1 + (M.childVisit s b t : ℝ))) atTop (𝓝 B)) :
      Tendsto (fun t => M.puctScore c s b t / Real.sqrt (M.parentVisit s t : ℝ))
        atTop (𝓝 B) := by
    have hroot : Tendsto (fun t => Real.sqrt (M.parentVisit s t : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hs)
    have hvalue : Tendsto (fun t => M.searchValue s b t /
        Real.sqrt (M.parentVisit s t : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (hconsistency s hs b).mul (tendsto_inv_atTop_zero.comp hroot)
    have hsum := hvalue.add hbonus
    rw [zero_add] at hsum
    apply hsum.congr'
    filter_upwards [hs.eventually (eventually_gt_atTop 0)] with t ht
    have hsqrt : Real.sqrt (M.parentVisit s t : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast ht))
    dsimp [MCTSModel.puctScore]
    field_simp
  by_contra ha
  obtain ⟨k, hk⟩ := hseq.toCountUpdates.child_eventually_constant s a ha
  let A : ℝ := c * M.prior s a / (1 + (k : ℝ))
  have hA : 0 < A := by dsimp [A]; positivity
  have hsa : Tendsto (fun t => M.puctScore c s a t / Real.sqrt (M.parentVisit s t : ℝ))
      atTop (𝓝 A) := by
    apply hscore_limit
    apply tendsto_const_nhds.congr'
    filter_upwards [hk] with t ht
    simp [A, ht]
  have hcomparison : ∀ b : M.Action s, ∀ᶠ t in atTop,
      M.selectedAt s b t →
        M.puctScore c s b t / Real.sqrt (M.parentVisit s t : ℝ) <
          M.puctScore c s a t / Real.sqrt (M.parentVisit s t : ℝ) := by
    intro b
    by_cases hb : M.SelectedInfinitelyOften s b
    · have hcount : Tendsto (fun t => 1 + (M.childVisit s b t : ℝ)) atTop atTop :=
        tendsto_const_nhds.add_atTop
          (tendsto_natCast_atTop_atTop.comp (hseq.toCountUpdates.child_tendsto s b hb))
      have hsb : Tendsto (fun t => M.puctScore c s b t / Real.sqrt (M.parentVisit s t : ℝ))
          atTop (𝓝 0) := by
        apply hscore_limit
        simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hcount).const_mul
          (c * M.prior s b)
      exact (hsb.eventually_lt hsa hA).mono (fun _ ht _ => ht)
    · simp only [MCTSModel.SelectedInfinitelyOften, not_forall, not_exists, not_and] at hb
      obtain ⟨t₀, hnone⟩ := hb
      filter_upwards [eventually_ge_atTop t₀] with t ht
      exact fun hsel => (hnone t ht hsel).elim
  have hall : ∀ᶠ t in atTop, ∀ b : M.Action s,
      M.selectedAt s b t →
        M.puctScore c s b t / Real.sqrt (M.parentVisit s t : ℝ) <
          M.puctScore c s a t / Real.sqrt (M.parentVisit s t : ℝ) :=
    Filter.eventually_all.2 hcomparison
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 hall
  obtain ⟨t, ht, b, hb⟩ := hlocal_selection_after hseq.toCountUpdates s hs t₀
  have hless := ht₀ t ht
  have hmax := hseq.argmax s b t hb a
  have hnorm := div_le_div_of_nonneg_right hmax (Real.sqrt_nonneg (M.parentVisit s t : ℝ))
  exact (not_lt_of_ge hnorm) (hless b hb)

/-- Lemma 2: at infinitely visited states, actions with prior < 1 are skipped infinitely often. -/
theorem lemma2 {M : MCTSModel} {c : ℝ} (hc : 0 < c)
    (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
    (hconsistency : M.ValueConsistency) :
    ∀ s, Tendsto (M.parentVisit s) atTop atTop →
      ∀ a, M.prior s a < 1 → M.NonSelectedInfinitelyOften s a := by
  classical
  intro s hs a ha
  have hcompeting : ∃ b : M.Action s, b ≠ a ∧ 0 < M.prior s b := by
    by_contra hnone
    have hzero : ∀ b : M.Action s, b ≠ a → M.prior s b = 0 := by
      intro b hba
      exact le_antisymm (le_of_not_gt (fun hb => hnone ⟨b, hba, hb⟩)) (M.prior_nonneg s b)
    have hsum := M.prior_sum s
    rw [tsum_eq_single a hzero] at hsum
    exact (ne_of_lt ha) hsum
  obtain ⟨b, hba, hb⟩ := hcompeting
  have hb_inf := lemma1 hc hseq hreg hconsistency s hs b hb
  intro t0
  obtain ⟨t, ht, hbt⟩ := hb_inf t0
  exact ⟨t, ht, ⟨b, hbt⟩, M.selection_disjoint s a b t hba hbt⟩

private theorem lemma3_bonus_bound_from_count_gap
    {C c P m nstar : ℝ}
    (hm : 0 < m)
    (hc : 0 ≤ c) (hP : 0 ≤ P)
    (hnstar : m - C * Real.sqrt m ≤ nstar)
    (hlarge : 2 * C * Real.sqrt m ≤ m) :
    c * P * Real.sqrt m / (1 + nstar) ≤ (2 * c * P) / Real.sqrt m := by
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hdenominator_pos : 0 < 1 + nstar := by nlinarith
  have hbase : Real.sqrt m / (1 + nstar) ≤ 2 / Real.sqrt m := by
    apply (div_le_div_iff₀ hdenominator_pos hsqrt_pos).2
    nlinarith [Real.sq_sqrt hm.le]
  convert mul_le_mul_of_nonneg_left hbase (mul_nonneg hc hP) using 1 <;> ring

/-- Lemma 3: an O(√m) optimal-count deficit gives an o(1) optimal exploration bonus. -/
theorem lemma3 (c P : ℝ) (hc : 0 < c) (hP : 0 ≤ P)
    (m : ℕ → ℕ) (nstar : ℕ → ℝ) (hm : Tendsto m atTop atTop)
    (hgap : (fun t => (m t : ℝ) - nstar t) =O[∞]
      (fun t => Real.sqrt (m t : ℝ))) :
    (fun t => c * P * Real.sqrt (m t : ℝ) / (1 + nstar t)) =o[∞]
      (fun _ : ℕ => (1 : ℝ)) := by
  obtain ⟨C, _, hbound⟩ := hgap.exists_pos
  have hsqrt : Tendsto (fun t => Real.sqrt (m t : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hm)
  have hbounds : ∀ᶠ t : ℕ in atTop,
      0 ≤ c * P * Real.sqrt (m t : ℝ) / (1 + nstar t) ∧
      c * P * Real.sqrt (m t : ℝ) / (1 + nstar t) ≤
        (2 * c * P) / Real.sqrt (m t : ℝ) := by
    filter_upwards [hbound.bound, hm.eventually (eventually_gt_atTop 0),
      hsqrt.eventually (eventually_ge_atTop (2 * C))] with t ht hpos hlarge
    have hpos' : 0 < (m t : ℝ) := by exact_mod_cast hpos
    have hcount : (m t : ℝ) - nstar t ≤ C * Real.sqrt (m t : ℝ) :=
      (le_abs_self _).trans (by
        simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (m t : ℝ))] using ht)
    have hlarge' : 2 * C * Real.sqrt (m t : ℝ) ≤ (m t : ℝ) := by
      nlinarith [Real.sq_sqrt hpos'.le,
        mul_nonneg (Real.sqrt_nonneg (m t : ℝ)) (sub_nonneg.mpr hlarge)]
    have hdenominator_pos : 0 < 1 + nstar t := by nlinarith
    exact ⟨div_nonneg (by positivity) hdenominator_pos.le,
      lemma3_bonus_bound_from_count_gap hpos' hc.le hP (by linarith) hlarge'⟩
  have hlim : Tendsto (fun t => (2 * c * P) / Real.sqrt (m t : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hsqrt).const_mul (2 * c * P)
  simpa [Asymptotics.isLittleO_one_iff] using
    squeeze_zero' (hbounds.mono (fun _ ht => ht.1)) (hbounds.mono (fun _ ht => ht.2)) hlim

/-! ## Visit-count bounds -/

private theorem theorem1_part1_upper_case
    {Qstar Qi Qhatstar Qhati c P eps m n : ℝ}
    (hden : 0 < 1 + n)
    (hgap : 0 < (Qstar - Qi) - 2 * eps)
    (hsel : Qhatstar ≤ Qhati + c * P * Real.sqrt m / (1 + n))
    (hi_err : |Qhati - Qi| ≤ eps)
    (hstar_err : |Qhatstar - Qstar| ≤ eps) :
    n ≤ c * P * Real.sqrt m / ((Qstar - Qi) - 2 * eps) - 1 := by
  have hbonus : Qstar - Qi - 2 * eps ≤ c * P * Real.sqrt m / (1 + n) := by
    linarith [(abs_le.mp hi_err).2, (abs_le.mp hstar_err).1]
  have hmul := (le_div_iff₀ hden).1 hbonus
  apply (le_sub_iff_add_le).2
  apply (le_div_iff₀ hgap).2
  nlinarith

private theorem suboptimal_visit_upper_bound {M : MCTSModel} {c ε : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c)
    (s : M.State) (a : M.Action s) (mε : ℕ)
    (hgap : 0 < M.Gap s a - 2 * ε)
    (hvalues : ∀ t, mε ≤ M.parentVisit s t →
      |M.searchValue s a t - M.value s a| ≤ ε ∧
      |M.searchValue s (M.isBest s) t - M.value s (M.isBest s)| ≤ ε) :
    ∀ t, (M.childVisit s a t : ℝ) ≤ max ((mε : ℝ) + 1)
      ((c * M.prior s a / (M.Gap s a - 2 * ε)) *
        Real.sqrt (M.parentVisit s t : ℝ)) := by
  have hP : 0 ≤ M.prior s a := M.prior_nonneg s a
  have hA : 0 ≤ c * M.prior s a / (M.Gap s a - 2 * ε) := by positivity
  intro t
  by_cases hz : M.childVisit s a t = 0
  · rw [hz, Nat.cast_zero]
    exact (by positivity : (0 : ℝ) ≤ (mε : ℝ) + 1).trans (le_max_left _ _)
  let u := hseq.toCountUpdates.lastSelection s a t
  obtain ⟨hut, hsel, hcount⟩ :=
    hseq.toCountUpdates.lastSelection_spec s a t (Nat.pos_of_ne_zero hz)
  by_cases hlarge : mε ≤ M.parentVisit s u
  · obtain ⟨hi, hstar⟩ := hvalues u hlarge
    have hscore := hseq.argmax s a u hsel (M.isBest s)
    have hbonus : 0 ≤ c * M.prior s (M.isBest s) * Real.sqrt (M.parentVisit s u : ℝ) /
        (1 + (M.childVisit s (M.isBest s) u : ℝ)) := by
      have := M.prior_nonneg s (M.isBest s)
      positivity
    have hcompare : M.searchValue s (M.isBest s) u ≤ M.searchValue s a u +
        c * M.prior s a * Real.sqrt (M.parentVisit s u : ℝ) /
          (1 + (M.childVisit s a u : ℝ)) := by
      dsimp [MCTSModel.puctScore] at hscore
      linarith
    have hupper := theorem1_part1_upper_case (c := c) (P := M.prior s a)
      (by positivity : 0 < 1 + (M.childVisit s a u : ℝ)) hgap hcompare hi hstar
    have hroot : Real.sqrt (M.parentVisit s u : ℝ) ≤ Real.sqrt (M.parentVisit s t : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hseq.toCountUpdates.parent_monotone s hut.le)
    have hmono := mul_le_mul_of_nonneg_left hroot hA
    have hcount' : (M.childVisit s a t : ℝ) = (M.childVisit s a u : ℝ) + 1 := by
      exact_mod_cast hcount
    apply le_trans _ (le_max_right _ _)
    rw [← div_mul_eq_mul_div] at hupper
    dsimp [MCTSModel.Gap] at *
    linarith
  · have hle := hseq.child_le_parent s a u
    have hnat : M.childVisit s a t ≤ mε := by
      change M.childVisit s a t = M.childVisit s a u + 1 at hcount
      omega
    have hreal : (M.childVisit s a t : ℝ) ≤ (mε : ℝ) + 1 := by
      exact_mod_cast hnat.trans (Nat.le_succ _)
    exact hreal.trans (le_max_left _ _)

private theorem suboptimal_visit_upper_of_value_estimates {M : MCTSModel} {c Δ : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
    (hΔ : 0 < Δ) (s : M.State) (a : M.Action s) (hgap_lower : Δ ≤ M.Gap s a)
    (mε : ℕ) (hvalues : ∀ a t, mε ≤ M.parentVisit s t →
      |M.searchValue s a t - M.value s a| ≤ Δ / 4) (t : ℕ) :
    (M.childVisit s a t : ℝ) ≤ (mε : ℝ) + 1 +
      (2 * c / Δ) * Real.sqrt (M.parentVisit s t : ℝ) := by
  let ε := Δ / 4
  have hgap : 0 < M.Gap s a - 2 * ε := by
    have := hgap_lower
    dsimp [ε]
    linarith
  have hupper := suboptimal_visit_upper_bound hc hseq s a mε hgap
    (fun t ht => ⟨hvalues a t ht, hvalues (M.isBest s) t ht⟩) t
  have hPnonneg : 0 ≤ M.prior s a := M.prior_nonneg s a
  have hP : M.prior s a ≤ 1 := by
    classical
    letI : Finite (M.Action s) := hreg.finite_branching.choose_spec.2 s |>.1
    exact (Summable.of_finite.le_tsum a (fun b _ => M.prior_nonneg s b)).trans_eq
      (M.prior_sum s)
  have hcoef : c * M.prior s a / (M.Gap s a - 2 * ε) ≤ 2 * c / Δ := by
    apply (div_le_div_iff₀ hgap hΔ).2
    have hg := hgap_lower
    dsimp [ε]
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hP)]
  have hm := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (M.parentVisit s t : ℝ))
  apply hupper.trans
  apply max_le
  · have hn : 0 ≤ 2 * c / Δ * Real.sqrt (M.parentVisit s t : ℝ) := by positivity
    linarith
  · linarith [show (0 : ℝ) ≤ (mε : ℝ) by positivity]

private theorem count_gap_sum_le {M : MCTSModel} (h : M.CountUpdates)
    (s : M.State) [Finite (M.Action s)] (t b : ℕ) {K : ℝ}
    (hb : Nat.card (M.Action s) ≤ b) (hK : 0 ≤ K)
    (hbound : ∀ a, M.Suboptimal s a → (M.childVisit s a t : ℝ) ≤ K) :
    (M.parentVisit s t : ℝ) - M.childVisit s (M.isBest s) t ≤ (b : ℝ) * K := by
  classical
  letI := Fintype.ofFinite (M.Action s)
  have hsum : (M.parentVisit s t : ℝ) = ∑ a, (M.childVisit s a t : ℝ) := by
    exact_mod_cast h.count_identity s t
  have he := Finset.sum_erase_add (Finset.univ : Finset (M.Action s))
    (fun a => (M.childVisit s a t : ℝ)) (Finset.mem_univ (M.isBest s))
  have hsub : ∑ a ∈ (Finset.univ : Finset (M.Action s)).erase (M.isBest s),
      (M.childVisit s a t : ℝ) ≤
      ((Finset.univ.erase (M.isBest s)).card : ℝ) * K := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul
      (Finset.univ.erase (M.isBest s)) _ K
      (fun a ha => hbound a (Finset.ne_of_mem_erase ha))
  have hcard : ((Finset.univ.erase (M.isBest s)).card : ℝ) ≤ b := by
    exact_mod_cast (Finset.card_erase_le (s := Finset.univ) (a := M.isBest s)).trans
      (by simpa [Nat.card_eq_fintype_card] using hb)
  have hmul := mul_le_mul_of_nonneg_right hcard hK
  linarith

private theorem theorem1_part1_lower_case
    {Qstar Qi Qhatstar Qhati bonus_star c P eps m n : ℝ}
    (hden : 0 < 1 + n)
    (hgap : 0 < (Qstar - Qi) + 3 * eps)
    (hsel : Qhati + c * P * Real.sqrt m / (1 + n) ≤ Qhatstar + bonus_star)
    (hi_err : |Qhati - Qi| ≤ eps)
    (hstar_err : |Qhatstar - Qstar| ≤ eps)
    (hbonus_star : bonus_star ≤ eps) :
    c * P * Real.sqrt m / ((Qstar - Qi) + 3 * eps) - 1 ≤ n := by
  have hi := abs_le.mp hi_err
  have hstar := abs_le.mp hstar_err
  have hbonus : c * P * Real.sqrt m / (1 + n) ≤ (Qstar - Qi) + 3 * eps := by
    linarith [hi.1, hstar.2]
  have hmul := (div_le_iff₀ hden).1 hbonus
  have hdiv : c * P * Real.sqrt m / ((Qstar - Qi) + 3 * eps) ≤ 1 + n := by
    apply (div_le_iff₀ hgap).2
    simpa [mul_comm] using hmul
  linarith

private theorem last_optimal_parent_ge_half {M : MCTSModel} {c C : ℝ}
    (hseq : M.Sequential c) (hC : 0 < C)
    (s : M.State) (t : ℕ) (hm : 1 ≤ M.parentVisit s t)
    (hgap : (M.parentVisit s t : ℝ) - (M.childVisit s (M.isBest s) t : ℝ) ≤
      C * Real.sqrt (M.parentVisit s t : ℝ))
    (hlarge : 2 * (C + 1) ≤ Real.sqrt (M.parentVisit s t : ℝ)) :
    let u := hseq.toCountUpdates.lastSelection s (M.isBest s) t
    u < t ∧ M.selectedAt s (M.isBest s) u ∧
      (M.parentVisit s t : ℝ) / 2 ≤ (M.parentVisit s u : ℝ) := by
  have hmreal : (1 : ℝ) ≤ (M.parentVisit s t : ℝ) := by exact_mod_cast hm
  have hs := Real.sqrt_nonneg (M.parentVisit s t : ℝ)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (M.parentVisit s t : ℝ) by positivity)
  have hsmall : C * Real.sqrt (M.parentVisit s t : ℝ) + 1 ≤ (M.parentVisit s t : ℝ) / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlarge) hs]
  have hp : 0 < M.childVisit s (M.isBest s) t := by
    have : (0 : ℝ) < (M.childVisit s (M.isBest s) t : ℝ) := by linarith
    exact_mod_cast this
  have hspec := hseq.toCountUpdates.lastSelection_spec s (M.isBest s) t hp
  refine ⟨hspec.1, hspec.2.1, ?_⟩
  have hu := hseq.child_le_parent s (M.isBest s)
    (hseq.toCountUpdates.lastSelection s (M.isBest s) t)
  have hcounts : (M.childVisit s (M.isBest s) t : ℝ) ≤
      (M.parentVisit s (hseq.toCountUpdates.lastSelection s (M.isBest s) t) : ℝ) + 1 := by
    exact_mod_cast (by omega : M.childVisit s (M.isBest s) t ≤
      M.parentVisit s (hseq.toCountUpdates.lastSelection s (M.isBest s) t) + 1)
  linarith

/-- Theorem 1(1): positive-prior suboptimal actions receive Θ(√N(s)) visits. -/
theorem theorem1_part1 {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
    (hconsistency : M.ValueConsistency)
    (s : M.State) (hs : Tendsto (M.parentVisit s) atTop atTop)
    (a : M.Action s) (ha : M.Suboptimal s a) (hprior : 0 < M.prior s a) :
    (fun t => (M.childVisit s a t : ℝ)) =Θ[∞]
      (fun t => Real.sqrt (M.parentVisit s t : ℝ)) := by
  have hlocal_last_tendsto {M : MCTSModel} (h : M.CountUpdates) (s : M.State) (a : M.Action s)
      (ha : M.SelectedInfinitelyOften s a) : Tendsto (h.lastSelection s a) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    have hgrow := h.child_tendsto s a ha
    filter_upwards [hgrow.eventually (eventually_gt_atTop (M.childVisit s a K + 1))] with t ht
    have hp : 0 < M.childVisit s a t := by omega
    have hspec := h.lastSelection_spec s a t hp
    by_contra hK
    have huK : h.lastSelection s a t ≤ K := by omega
    have hcounts := h.child_monotone s a huK
    omega
  let u := hseq.toCountUpdates.lastSelection s (M.isBest s)
  let bonus := fun t => c * M.prior s (M.isBest s) * Real.sqrt (M.parentVisit s t : ℝ) /
    (1 + (M.childVisit s (M.isBest s) t : ℝ))
  obtain ⟨b, _, hf⟩ := hreg.finite_branching
  letI : Finite (M.Action s) := (hf s).1
  obtain ⟨Δ, hΔmin, hgaps⟩ := hreg.gap_lower
  have hvalues_eventually : ∀ a : M.Action s, ∀ᶠ t in atTop,
      |M.searchValue s a t - M.value s a| ≤ Δ / 4 := by
    intro a
    have hlim : Tendsto (fun t => |M.searchValue s a t - M.value s a|) atTop (𝓝 0) := by
      simpa using ((hconsistency s hs a).sub_const (M.value s a)).abs
    exact (hlim.eventually (gt_mem_nhds (by positivity : 0 < Δ / 4))).mono (fun _ ht => ht.le)
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 hvalues_eventually)
  let mε := M.parentVisit s t₀ + 1
  have hvalues : ∀ a t, mε ≤ M.parentVisit s t →
      |M.searchValue s a t - M.value s a| ≤ Δ / 4 := by
    intro a t ht
    have htime : t₀ ≤ t := by
      by_contra h
      have := hseq.toCountUpdates.parent_monotone s (Nat.le_of_lt (Nat.lt_of_not_ge h))
      dsimp [mε] at ht
      omega
    exact ht₀ t htime a
  let K : ℝ := (mε : ℝ) + 1
  let A : ℝ := 2 * c / Δ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hupper : ∀ a, M.Suboptimal s a → ∀ t,
      (M.childVisit s a t : ℝ) ≤ K + A * Real.sqrt (M.parentVisit s t : ℝ) :=
    fun a ha t => suboptimal_visit_upper_of_value_estimates hc hseq hreg hΔmin s a
      (hgaps s a ha) mε hvalues t
  have hsqrt : Tendsto (fun t => Real.sqrt (M.parentVisit s t : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hs)
  let C : ℝ := (b : ℝ) * (K + A) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hgap : ∀ᶠ t in atTop, (M.parentVisit s t : ℝ) - M.childVisit s (M.isBest s) t ≤
      C * Real.sqrt (M.parentVisit s t : ℝ) := by
    filter_upwards [hsqrt.eventually (eventually_ge_atTop 1)] with t ht
    have hsum := count_gap_sum_le hseq.toCountUpdates s t b (hf s).2
      (show 0 ≤ K + A * Real.sqrt (M.parentVisit s t : ℝ) by positivity)
      (fun a ha => hupper a ha t)
    have hscale := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hK ht)
      (Nat.cast_nonneg b (α := ℝ))
    dsimp [C]
    nlinarith [Real.sqrt_nonneg (M.parentVisit s t : ℝ)]
  have hselected : M.SelectedInfinitelyOften s (M.isBest s) := by
    by_cases hP : 0 < M.prior s (M.isBest s)
    · exact lemma1 hc hseq hreg hconsistency s hs (M.isBest s) hP
    · by_contra h
      obtain ⟨k, hk⟩ := hseq.toCountUpdates.child_eventually_constant s (M.isBest s) h
      obtain ⟨t, ht, hbound, hlarge⟩ :=
        (hk.and (hgap.and (hsqrt.eventually (eventually_ge_atTop (C + (k : ℝ) + 2))))).exists
      rw [ht] at hbound
      have hr := Real.sqrt_nonneg (M.parentVisit s t : ℝ)
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (M.parentVisit s t) (α := ℝ)),
        Nat.cast_nonneg k (α := ℝ), mul_nonneg (sub_nonneg.mpr hlarge) hr]
  have hu : Tendsto u atTop atTop :=
    hlocal_last_tendsto hseq.toCountUpdates s (M.isBest s) hselected
  have hvalue (b : M.Action s) :
      Tendsto (fun t => |M.searchValue s b (u t) - M.value s b|) atTop (𝓝 0) := by
    simpa using (((hconsistency s hs b).comp hu).sub_const (M.value s b)).abs
  have hbonus : Tendsto bonus atTop (𝓝 0) := by
    have hgapO : (fun t => (M.parentVisit s t : ℝ) - M.childVisit s (M.isBest s) t) =O[∞]
        (fun t => Real.sqrt (M.parentVisit s t : ℝ)) := by
      apply Asymptotics.IsBigO.of_bound C
      filter_upwards [hgap] with t ht
      have hnonneg : 0 ≤ (M.parentVisit s t : ℝ) - M.childVisit s (M.isBest s) t := by
        exact sub_nonneg.mpr (by exact_mod_cast hseq.child_le_parent s (M.isBest s) t)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg,
        abs_of_nonneg (Real.sqrt_nonneg (M.parentVisit s t : ℝ))] using ht
    simpa [Asymptotics.isLittleO_one_iff] using
      lemma3 c (M.prior s (M.isBest s)) hc (M.prior_nonneg s (M.isBest s))
        (M.parentVisit s) (fun t => (M.childVisit s (M.isBest s) t : ℝ)) hs hgapO
  have hΔ : 0 < M.Gap s a := hΔmin.trans_le (hgaps s a ha)
  let β := c * M.prior s a / (M.Gap s a + 3)
  have hβ : 0 < β := by dsimp [β]; positivity
  apply theta_of_eventual_sandwich
    (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
  · refine ⟨K + A, by positivity, ?_⟩
    filter_upwards [hsqrt.eventually (eventually_ge_atTop 1)] with t ht
    have hb := hupper a ha t
    nlinarith [le_mul_of_one_le_right hK ht]
  · refine ⟨β / 4, by positivity, ?_⟩
    filter_upwards [hgap, hs.eventually (eventually_ge_atTop 1),
      hsqrt.eventually (eventually_ge_atTop (max (2 * (C + 1)) (4 / β))),
      (hvalue a).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      (hvalue (M.isBest s)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      (hbonus.comp hu).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t hg hm hr hi hstar hb
    obtain ⟨hut, hsel, hhalf⟩ := last_optimal_parent_ge_half hseq hC s t hm hg
      ((le_max_left _ _).trans hr)
    have hlow := theorem1_part1_lower_case (c := c) (P := M.prior s a) (eps := 1)
      (by positivity : 0 < 1 + (M.childVisit s a (u t) : ℝ))
      (by linarith : 0 < M.Gap s a + 3 * 1)
      (hseq.argmax s (M.isBest s) (u t) hsel a) hi.le hstar.le hb.le
    have hlow' : β * Real.sqrt (M.parentVisit s (u t) : ℝ) - 1 ≤
        (M.childVisit s a (u t) : ℝ) := by
      dsimp [β, MCTSModel.Gap]
      convert hlow using 1
      ring
    have hroot : Real.sqrt (M.parentVisit s t : ℝ) / 2 ≤
        Real.sqrt (M.parentVisit s (u t) : ℝ) := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (M.parentVisit s t) (α := ℝ)),
        Real.sq_sqrt (Nat.cast_nonneg (M.parentVisit s (u t)) (α := ℝ)),
        Real.sqrt_nonneg (M.parentVisit s t : ℝ),
        Real.sqrt_nonneg (M.parentVisit s (u t) : ℝ)]
    have hmono : (M.childVisit s a (u t) : ℝ) ≤ M.childVisit s a t := by
      exact_mod_cast hseq.toCountUpdates.child_monotone s a hut.le
    have hlarge := (div_le_iff₀ hβ).1 ((le_max_right _ _).trans hr)
    nlinarith [mul_le_mul_of_nonneg_left hroot hβ.le]

/-! ## Depth bounds -/

namespace DepthProfile

noncomputable def sqrtSimulationCount : ℕ → ℝ :=
  fun n => Real.sqrt (n : ℝ)

noncomputable def loglogSimulationCount : ℕ → ℝ :=
  fun n => Real.log (Real.log (n : ℝ))

noncomputable def nOverThreads (T : ℕ → ℕ) : ℕ → ℝ :=
  fun n => (n : ℝ) / (T n : ℝ)

end DepthProfile

private theorem uniform_optimal_visit_gap {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
    (huniform : M.UniformValueConsistency) :
    ∃ C : ℝ, 0 < C ∧ ∀ s t, 1 ≤ M.parentVisit s t →
      (M.parentVisit s t : ℝ) - (M.childVisit s (M.isBest s) t : ℝ) ≤
        C * Real.sqrt (M.parentVisit s t : ℝ) := by
  classical
  obtain ⟨b, hb, hfinite⟩ := hreg.finite_branching
  obtain ⟨Δ, hΔ, hgaps⟩ := hreg.gap_lower
  obtain ⟨mε, hvalues⟩ := huniform (Δ / 4) (by positivity)
  let K : ℝ := (mε : ℝ) + 1
  let A : ℝ := 2 * c / Δ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hupper : ∀ s a, M.Suboptimal s a → ∀ t,
      (M.childVisit s a t : ℝ) ≤ K + A * Real.sqrt (M.parentVisit s t : ℝ) :=
    fun s a ha t => suboptimal_visit_upper_of_value_estimates hc hseq hreg hΔ s a
      (hgaps s a ha) mε (hvalues s) t
  refine ⟨1 + (b : ℝ) * (K + A), by positivity, ?_⟩
  intro s t hm
  letI : Finite (M.Action s) := (hfinite s).1
  have ht : 1 ≤ Real.sqrt (M.parentVisit s t : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hm)
  have hsum := count_gap_sum_le hseq.toCountUpdates s t b (hfinite s).2
    (show 0 ≤ K + A * Real.sqrt (M.parentVisit s t : ℝ) by positivity)
    (fun a ha => hupper s a ha t)
  have hKmul := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hK ht)
    (show (0 : ℝ) ≤ (b : ℝ) by positivity)
  nlinarith

/-- A decreasing count profile ending at one. -/
private structure CountPath (N : ℕ → ℕ) (H n : ℕ) : Prop where
  root : N 0 = n
  leaf : N H = 1
  decreasing : ∀ x < H, N (x + 1) < N x

namespace CountPath

variable {N : ℕ → ℕ} {H n : ℕ} (h : CountPath N H n)
include h

private theorem drop {i j : ℕ} (hij : i ≤ j) (hj : j ≤ H) : N j + (j - i) ≤ N i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have hprev := ih (by omega)
    have hdec := h.decreasing j (by omega)
    omega

private theorem positive {x : ℕ} (hx : x ≤ H) : 1 ≤ N x := by
  have hd := h.drop hx (le_refl H)
  rw [h.leaf] at hd
  omega

private theorem cutoff (m : ℕ) (hm : 2 ≤ m) :
    ∃ J ≤ H, N J < m ∧ H ≤ J + m ∧ ∀ x < J, m ≤ N x := by
  have hex : ∃ x, N x < m := ⟨H, by rw [h.leaf]; omega⟩
  let J := Nat.find hex
  have hJ : N J < m := Nat.find_spec hex
  have hJH : J ≤ H := Nat.find_min' hex (by rw [h.leaf]; omega)
  refine ⟨J, hJH, hJ, ?_, ?_⟩
  · have hd := h.drop hJH (le_refl H)
    omega
  · intro x hx
    have := Nat.find_min hex hx
    omega

end CountPath

private theorem finite_chain_cutoff (N : ℕ → ℕ) (H m : ℕ)
    (hdec : ∀ x < H, N (x + 1) < N x) :
    ∃ J ≤ H, (J = H ∨ N J < m) ∧ H ≤ J + m ∧ ∀ x < J, m ≤ N x := by
  classical
  have hex : ∃ x, x = H ∨ (x ≤ H ∧ N x < m) := ⟨H, Or.inl rfl⟩
  let J := Nat.find hex
  have hJH : J ≤ H := Nat.find_min' hex (Or.inl rfl)
  have hJ : J = H ∨ N J < m := (Nat.find_spec hex).imp id And.right
  refine ⟨J, hJH, hJ, ?_, ?_⟩
  · rcases hJ with heq | hsmall
    · omega
    · have hdrop : ∀ j, J ≤ j → j ≤ H → N j + (j - J) ≤ N J := by
        intro j hj hjH
        induction j, hj using Nat.le_induction with
        | base => simp
        | succ j hj ih =>
          have hd := hdec j (by omega)
          have hp := ih (by omega)
          omega
      have := hdrop H hJH (le_refl H)
      omega
  · intro x hx
    have hn := Nat.find_min hex hx
    have hxH : x ≤ H := hx.le.trans hJH
    omega

/-! ### From selection counts `N` to arrival counts `N + 1` -/

private theorem sqrt_arrival_bounds (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) ∧
    Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (m : ℝ) ∧
    1 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (m : ℝ) by positivity)
  have hsq' := Real.sq_sqrt (show (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) by positivity)
  push_cast at hsq' ⊢
  refine ⟨Real.sqrt_le_sqrt (by linarith), ?_, Real.one_le_sqrt.mpr (by linarith)⟩
  nlinarith [Real.sqrt_nonneg (m : ℝ), Real.sqrt_nonneg ((m : ℝ) + 1)]

private theorem uniform_arrival_optimal_gap {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
    (hu : M.UniformValueConsistency) :
    ∃ C : ℝ, 0 < C ∧ ∀ s t, 1 ≤ M.arrivalCount s t →
      (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ≤
        C * Real.sqrt (M.arrivalCount s t : ℝ) := by
  obtain ⟨C, hC, hb⟩ := uniform_optimal_visit_gap hc hseq hreg hu
  refine ⟨C + 1, by linarith, ?_⟩
  intro s t _
  by_cases hm : M.parentVisit s t = 0
  · have hz : M.childVisit s (M.isBest s) t = 0 := by
      have := hseq.child_le_parent s (M.isBest s) t
      omega
    simp [MCTSModel.arrivalCount, hm, hz, hC.le]
  · have hm1 : 1 ≤ M.parentVisit s t := by omega
    have hg := hb s t hm1
    obtain ⟨hs, _, h1⟩ := sqrt_arrival_bounds (M.parentVisit s t) hm1
    have hmul := mul_le_mul_of_nonneg_left hs hC.le
    simp only [MCTSModel.arrivalCount, Nat.cast_add, Nat.cast_one] at *
    nlinarith

private theorem unvisited_arrival_bound {M : MCTSModel} {C : ℝ} (hC : 0 < C)
    (hb : ∀ s t, 1 ≤ M.arrivalCount s t →
      (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ≤
        C * Real.sqrt (M.arrivalCount s t : ℝ))
    (s : M.State) (t : ℕ) (hz : M.childVisit s (M.isBest s) t = 0) :
    (M.arrivalCount s t : ℝ) ≤ C ^ 2 := by
  have h := hb s t (Nat.succ_pos _)
  rw [hz, Nat.cast_zero, sub_zero] at h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M.arrivalCount s t : ℝ) by positivity)
  have hp : 0 < Real.sqrt (M.arrivalCount s t : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast (Nat.succ_pos (M.parentVisit s t)))
  have hle : Real.sqrt (M.arrivalCount s t : ℝ) ≤ C := by nlinarith
  nlinarith

private theorem uniform_arrival_optimal_difference {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
    (hu : M.UniformValueConsistency) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∃ m₀ : ℕ, ∀ s t,
      ¬ M.isTerminal s → m₀ ≤ M.arrivalCount s t →
      κ * Real.sqrt (M.arrivalCount s t : ℝ) ≤
        (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ∧
      (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ≤
        C * Real.sqrt (M.arrivalCount s t : ℝ) := by
  have hlocal_bonus_small {M : MCTSModel} {c : ℝ}
      (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
      (huniform : M.UniformValueConsistency) (ε : ℝ) (hε : 0 < ε) :
      ∃ m₀ : ℕ, ∀ s t, m₀ ≤ M.parentVisit s t →
        c * M.prior s (M.isBest s) * Real.sqrt (M.parentVisit s t : ℝ) /
          (1 + (M.childVisit s (M.isBest s) t : ℝ)) ≤ ε := by
    classical
    obtain ⟨C, hC, hgap⟩ := uniform_optimal_visit_gap hc hseq hreg huniform
    have hsqrt : Tendsto (fun m : ℕ => Real.sqrt (m : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hev : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧ max (2 * C) (2 * c / ε) ≤ Real.sqrt (m : ℝ) :=
      (eventually_ge_atTop 1).and (hsqrt.eventually (eventually_ge_atTop _))
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
    refine ⟨m₀, ?_⟩
    intro s t ht
    obtain ⟨hm, hlarge⟩ := hm₀ (M.parentVisit s t) ht
    have hmpos : (0 : ℝ) < (M.parentVisit s t : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
    have hspos := Real.sqrt_pos.2 hmpos
    have hsC : 2 * C ≤ Real.sqrt (M.parentVisit s t : ℝ) := (le_max_left _ _).trans hlarge
    have hsc : 2 * c / ε ≤ Real.sqrt (M.parentVisit s t : ℝ) := (le_max_right _ _).trans hlarge
    have hg := hgap s t hm
    have hsq := Real.sq_sqrt hmpos.le
    have hbig : 2 * C * Real.sqrt (M.parentVisit s t : ℝ) ≤ (M.parentVisit s t : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsC) hspos.le]
    have hbase := lemma3_bonus_bound_from_count_gap (C := C)
      (nstar := (M.childVisit s (M.isBest s) t : ℝ)) hmpos hc.le
      (M.prior_nonneg s (M.isBest s)) (by linarith) hbig
    letI : Finite (M.Action s) := hreg.finite_branching.choose_spec.2 s |>.1
    have hP : M.prior s (M.isBest s) ≤ 1 :=
      (Summable.of_finite.le_tsum (M.isBest s) (fun a _ => M.prior_nonneg s a)).trans_eq
        (M.prior_sum s)
    apply hbase.trans
    have hlast : 2 * c / Real.sqrt (M.parentVisit s t : ℝ) ≤ ε := by
      apply (div_le_iff₀ hspos).2
      have := (div_le_iff₀ hε).1 hsc
      nlinarith
    apply le_trans _ hlast
    apply div_le_div_of_nonneg_right _ hspos.le
    nlinarith
  have hlocal_suboptimal_gap {M : MCTSModel} {c : ℝ}
      (hseq : M.Sequential c) (s : M.State) [Finite (M.Action s)]
      (a : M.Action s) (ha : M.Suboptimal s a) (t : ℕ) :
      (M.childVisit s a t : ℝ) ≤
        (M.parentVisit s t : ℝ) - (M.childVisit s (M.isBest s) t : ℝ) := by
    classical
    letI : Fintype (M.Action s) := Fintype.ofFinite _
    apply (le_sub_iff_add_le).2
    norm_cast
    rw [hseq.toCountUpdates.count_identity s t,
      ← Finset.sum_pair (f := fun b => M.childVisit s b t) ha]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hlocal_selection_gap {M : MCTSModel} {c : ℝ}
      (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
      (huniform : M.UniformValueConsistency) :
      ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∃ m₀ : ℕ, ∀ s t,
        ¬ M.isTerminal s → m₀ ≤ M.parentVisit s t →
        κ * Real.sqrt (M.parentVisit s t : ℝ) ≤
          (M.parentVisit s t : ℝ) - (M.childVisit s (M.isBest s) t : ℝ) ∧
        (M.parentVisit s t : ℝ) - (M.childVisit s (M.isBest s) t : ℝ) ≤
          C * Real.sqrt (M.parentVisit s t : ℝ) := by
    classical
    obtain ⟨C, hC, hgap⟩ := uniform_optimal_visit_gap hc hseq hreg huniform
    obtain ⟨p₀, hp₀, hprior⟩ := hreg.suboptimal_prior
    obtain ⟨Δmax, hΔmax, huppergap⟩ := hreg.gap_upper
    obtain ⟨mval, hvalues⟩ := huniform 1 zero_lt_one
    obtain ⟨mbonus, hbonus⟩ :=
      hlocal_bonus_small hc hseq hreg huniform 1 zero_lt_one
    let B : ℝ := c * p₀ / (Δmax + 3)
    have hB : 0 < B := by dsimp [B]; positivity
    have hsqrt : Tendsto (fun m : ℕ => Real.sqrt (m : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hlarge : ∀ᶠ m : ℕ in atTop,
        1 ≤ m ∧ 2 * mval ≤ m ∧ 2 * mbonus ≤ m ∧
        max (2 * (C + 1)) (4 / B) ≤ Real.sqrt (m : ℝ) := by
      filter_upwards [eventually_ge_atTop (max 1 (max (2 * mval) (2 * mbonus))),
        hsqrt.eventually (eventually_ge_atTop _)] with m hm hs
      exact ⟨by omega, by omega, by omega, hs⟩
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hlarge
    refine ⟨B / 4, C, by positivity, hC, m₀, ?_⟩
    intro s t hnt ht
    obtain ⟨hm, hval, hb, hsize⟩ := hm₀ (M.parentVisit s t) ht
    let u := hseq.toCountUpdates.lastSelection s (M.isBest s) t
    have hus := last_optimal_parent_ge_half hseq hC s t hm (hgap s t hm)
      ((le_max_left _ _).trans hsize)
    have hval_u : mval ≤ M.parentVisit s u := by
      have hval' : (2 : ℝ) * (mval : ℝ) ≤ (M.parentVisit s t : ℝ) := by exact_mod_cast hval
      have : (mval : ℝ) ≤ (M.parentVisit s u : ℝ) := by linarith [hus.2.2]
      exact_mod_cast this
    have hbonus_u : mbonus ≤ M.parentVisit s u := by
      have hb' : (2 : ℝ) * (mbonus : ℝ) ≤ (M.parentVisit s t : ℝ) := by exact_mod_cast hb
      have : (mbonus : ℝ) ≤ (M.parentVisit s u : ℝ) := by linarith [hus.2.2]
      exact_mod_cast this
    obtain ⟨a, ha, hpa⟩ := hprior s hnt
    have hΔ : 0 < M.Gap s a := hreg.gap_lower.choose_spec.1.trans_le
      (hreg.gap_lower.choose_spec.2 s a ha)
    have hden : 0 < M.Gap s a + 3 * (1 : ℝ) := by linarith
    have hsel := hseq.argmax s (M.isBest s) u hus.2.1 a
    have hlow := theorem1_part1_lower_case (c := c) (P := M.prior s a)
      (by positivity : 0 < 1 + (M.childVisit s a u : ℝ)) hden hsel
      (hvalues s a u hval_u) (hvalues s (M.isBest s) u hval_u)
      (hbonus s u hbonus_u)
    have hcoef : B ≤ c * M.prior s a / (M.Gap s a + 3) := by
      dsimp [B]
      exact div_le_div₀ (mul_nonneg hc.le (M.prior_nonneg s a))
        (mul_le_mul_of_nonneg_left hpa hc.le) (by linarith) (by linarith [huppergap s a ha])
    have hs1 := Real.sqrt_nonneg (M.parentVisit s u : ℝ)
    have hs2 := Real.sqrt_nonneg (M.parentVisit s t : ℝ)
    have hsq1 := Real.sq_sqrt (show (0 : ℝ) ≤ (M.parentVisit s u : ℝ) by positivity)
    have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ (M.parentVisit s t : ℝ) by positivity)
    have hscompare : Real.sqrt (M.parentVisit s t : ℝ) / 2 ≤
        Real.sqrt (M.parentVisit s u : ℝ) := by nlinarith [hus.2.2]
    have hmul := mul_le_mul_of_nonneg_right hcoef hs1
    have hmul' := mul_le_mul_of_nonneg_left hscompare hB.le
    have hmono : (M.childVisit s a u : ℝ) ≤ (M.childVisit s a t : ℝ) := by
      exact_mod_cast hseq.toCountUpdates.child_monotone s a hus.1.le
    have hfour : 4 ≤ B * Real.sqrt (M.parentVisit s t : ℝ) := by
      have := (div_le_iff₀ hB).1 ((le_max_right _ _).trans hsize)
      nlinarith
    have hlower : B / 4 * Real.sqrt (M.parentVisit s t : ℝ) ≤ (M.childVisit s a t : ℝ) := by
      rw [← div_mul_eq_mul_div] at hlow
      dsimp [MCTSModel.Gap] at *
      nlinarith
    letI : Finite (M.Action s) := hreg.finite_branching.choose_spec.2 s |>.1
    letI : Fintype (M.Action s) := Fintype.ofFinite _
    exact ⟨hlower.trans (hlocal_suboptimal_gap hseq s a ha t), hgap s t hm⟩
  obtain ⟨κ, C, hκ, hC, m₀, hb⟩ := hlocal_selection_gap hc hseq hreg hu
  refine ⟨κ / 2, C + 1, by positivity, by linarith, max 2 (m₀ + 1), ?_⟩
  intro s t hnt ht
  have hm : m₀ ≤ M.parentVisit s t := by simp only [MCTSModel.arrivalCount] at ht; omega
  have hm1 : 1 ≤ M.parentVisit s t := by simp only [MCTSModel.arrivalCount] at ht; omega
  obtain ⟨hl, hupp⟩ := hb s t hnt hm
  obtain ⟨hs, hs2, h1⟩ := sqrt_arrival_bounds (M.parentVisit s t) hm1
  have hk := mul_le_mul_of_nonneg_left hs2 hκ.le
  have hmul := mul_le_mul_of_nonneg_left hs hC.le
  simp only [MCTSModel.arrivalCount, Nat.cast_add, Nat.cast_one] at *
  constructor <;> nlinarith

private theorem sqrtSimulationCount_succ_equiv :
    (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) =Θ[∞] DepthProfile.sqrtSimulationCount := by
  apply theta_of_eventual_sandwich
  · exact Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _)
  · exact Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _)
  · refine ⟨2, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (sqrt_arrival_bounds n hn).2.1
  · refine ⟨1, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [one_mul] using (sqrt_arrival_bounds n hn).1

/-- Theorem 1(2): uncapped optimal-path depth is Θ(√n). -/
theorem theorem1_part2 {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
    (huniform : M.UniformValueConsistency)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.OptimalPathCounts (V n) (H n) (n + 1) (state n) (time n)) :
    (fun n => (H n : ℝ)) =Θ[∞] DepthProfile.sqrtSimulationCount := by
  obtain ⟨κ, C, hκ, hC, m₀, hdrop⟩ :=
    uniform_arrival_optimal_difference hc hseq hreg huniform
  obtain ⟨C₀, hC₀, hgap⟩ := uniform_arrival_optimal_gap hc hseq hreg huniform
  obtain ⟨mend, hmend⟩ := exists_nat_gt (C₀ ^ 2)
  let m := max m₀ mend
  have hbounds : ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (m : ℝ) ≤ C * (H n : ℝ) ∧
      (H n : ℝ) ≤ (2 / κ) * Real.sqrt ((n + 1 : ℕ) : ℝ) + m := by
    filter_upwards [hpath] with n hn
    have hdec : ∀ x < H n, V n (x + 1) < V n x := by
      intro x hx
      obtain ⟨_, hp, hc⟩ := hn.2.2.2.2 x hx
      rw [hp, hc]
      exact Nat.lt_succ_of_le (hseq.child_le_parent _ _ _)
    obtain ⟨J, hJH, hsmall, htail, hbig⟩ := finite_chain_cutoff (V n) (H n) m hdec
    have hleaf : (V n J : ℝ) ≤ m := by
      rcases hsmall with heq | hsmall
      · rw [heq, hn.2.1]
        have hb := unvisited_arrival_bound hC₀ hgap _ _ hn.2.2.2.1
        have hm : (mend : ℝ) ≤ m := by exact_mod_cast le_max_right m₀ mend
        linarith
      · exact_mod_cast hsmall.le
    have hsteps : ∀ x < J,
        0 < (V n x : ℝ) ∧ 0 ≤ (V n (x + 1) : ℝ) ∧ (V n (x + 1) : ℝ) ≤ V n x ∧
        κ * Real.sqrt (V n x : ℝ) ≤ (V n x : ℝ) - V n (x + 1) ∧
        (V n x : ℝ) - V n (x + 1) ≤ C * Real.sqrt (V n x : ℝ) := by
      intro x hx
      have hxH := hx.trans_le hJH
      obtain ⟨hnt, hp, hc⟩ := hn.2.2.2.2 x hxH
      have hm : m₀ ≤ M.arrivalCount (state n x) (time n x) := by
        rw [← hp]
        exact (le_max_left m₀ mend).trans (hbig x hx)
      refine ⟨by exact_mod_cast Nat.zero_lt_of_lt (hdec x hxH), by positivity,
        by exact_mod_cast (hdec x hxH).le, ?_⟩
      simpa only [hp, hc] using hdrop _ _ hnt hm
    have hpotential : ∀ x < J,
        κ / 2 ≤ Real.sqrt (V n x : ℝ) - Real.sqrt (V n (x + 1) : ℝ) ∧
        Real.sqrt (V n x : ℝ) - Real.sqrt (V n (x + 1) : ℝ) ≤ C := by
      intro x hx
      obtain ⟨ha, hb, hab, hlo, hhi⟩ := hsteps x hx
      have hsa := Real.sqrt_pos.2 ha
      have hmono := Real.sqrt_le_sqrt hab
      have hprod := mul_nonneg (sub_nonneg.mpr hmono) (Real.sqrt_nonneg (V n (x + 1) : ℝ))
      constructor <;> nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt hb,
        sq_nonneg (Real.sqrt (V n x : ℝ) - Real.sqrt (V n (x + 1) : ℝ))]
    have hhi' := Finset.sum_le_sum (s := Finset.range J)
      (fun x hx => (hpotential x (Finset.mem_range.mp hx)).1)
    have hlo' := Finset.sum_le_sum (s := Finset.range J)
      (fun x hx => (hpotential x (Finset.mem_range.mp hx)).2)
    simp only [Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, hn.1] at hlo' hhi'
    have hJH' : (J : ℝ) ≤ H n := by exact_mod_cast hJH
    have htail' : (H n : ℝ) ≤ (J : ℝ) + m := by exact_mod_cast htail
    constructor
    · nlinarith [Real.sqrt_le_sqrt hleaf]
    · have hJ : (J : ℝ) ≤ (2 / κ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hκ).2
        nlinarith [Real.sqrt_nonneg (V n J : ℝ)]
      linarith
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  suffices htheta : (fun n => (H n : ℝ)) =Θ[∞]
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ)) from htheta.trans sqrtSimulationCount_succ_equiv
  constructor
  · apply Asymptotics.IsBigO.of_bound (2 / κ + (m : ℝ))
    filter_upwards [hbounds, hsqrt.eventually (eventually_ge_atTop 1)] with n hn hlarge
    simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (H n) (α := ℝ)),
      abs_of_nonneg (Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ))]
    nlinarith [le_mul_of_one_le_right (Nat.cast_nonneg m (α := ℝ)) hlarge, hn.2]
  · apply Asymptotics.IsBigO.of_bound (2 * C)
    filter_upwards [hbounds, hsqrt.eventually (eventually_ge_atTop (2 * Real.sqrt (m : ℝ)))]
      with n hn hlarge
    simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (H n) (α := ℝ)),
      abs_of_nonneg (Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ))]
    linarith [hn.1]

/-- Theorem 1(2), capped: the optimal path eventually reaches depth L. -/
theorem theorem1_part2_capped {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
    (huniform : M.UniformValueConsistency)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (L : ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.CappedOptimalPathCounts (V n) (H n) (n + 1) L (state n) (time n)) :
    ∀ᶠ n : ℕ in atTop, H n = L := by
  obtain ⟨C, hC, hgap⟩ := uniform_arrival_optimal_gap hc hseq hreg huniform
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  filter_upwards [hpath, hsqrt.eventually (eventually_gt_atTop (C * ((L : ℝ) + 1)))]
    with n hn hlarge
  by_contra hnot
  obtain ⟨hfront, _, hz⟩ := hn.2.2.1 (lt_of_le_of_ne hn.2.1 hnot)
  have hend : (V n (H n) : ℝ) ≤ C ^ 2 := by
    rw [hfront]
    exact unvisited_arrival_bound hC hgap _ _ hz
  have hsteps : ∀ x < H n,
      -C ≤ -Real.sqrt (V n x : ℝ) - -Real.sqrt (V n (x + 1) : ℝ) := by
    intro x hx
    obtain ⟨_, hp, hc⟩ := hn.2.2.2 x hx
    have hg := hgap (state n x) (time n x) (Nat.succ_pos _)
    rw [← hp, ← hc] at hg
    have hlt : V n (x + 1) < V n x := by
      rw [hp, hc]
      exact Nat.lt_succ_of_le (hseq.child_le_parent _ _ _)
    have hpos : 0 < (V n x : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hlt
    have hspos := Real.sqrt_pos.2 hpos
    have hmono := Real.sqrt_le_sqrt (show (V n (x + 1) : ℝ) ≤ V n x by exact_mod_cast hlt.le)
    nlinarith [Real.sq_sqrt hpos.le,
      Real.sq_sqrt (Nat.cast_nonneg (V n (x + 1)) (α := ℝ)),
      mul_nonneg (sub_nonneg.mpr hmono) (Real.sqrt_nonneg (V n (x + 1) : ℝ))]
  have hsum := Finset.sum_le_sum (s := Finset.range (H n))
    (fun x hx => hsteps x (Finset.mem_range.mp hx))
  simp only [Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  simp only [hn.1] at hsum
  have hL : (H n : ℝ) ≤ L := by exact_mod_cast hn.2.1
  have hfront_le : Real.sqrt (V n (H n) : ℝ) ≤ C := Real.sqrt_le_iff.mpr ⟨hC.le, hend⟩
  have hscaled := mul_le_mul_of_nonneg_left hL hC.le
  nlinarith

/-- Theorem 1(3): every root-to-leaf path has depth O(√n). -/
theorem theorem1_part3 {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c) (hreg : Assumption.Regularity M)
    (huniform : M.UniformValueConsistency)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (action : ∀ n x, M.Action (state n x))
    (hpath : ∀ᶠ n : ℕ in atTop, V n 0 = n + 1 ∧ ∀ x < H n,
      ¬ M.isTerminal (state n x) ∧
      V n x = M.arrivalCount (state n x) (time n x) ∧
      V n (x + 1) = M.childVisit (state n x) (action n x) (time n x)) :
    (fun n => (H n : ℝ)) =O[∞] DepthProfile.sqrtSimulationCount := by
  have hgap : ∃ κ : ℝ, 0 < κ ∧ ∃ m₀ : ℕ, ∀ s a t,
      ¬ M.isTerminal s → m₀ ≤ M.arrivalCount s t →
      κ * Real.sqrt (M.arrivalCount s t : ℝ) ≤
        (M.arrivalCount s t : ℝ) - M.childVisit s a t := by
    obtain ⟨κ, _, hκ, _, mopt, hopt⟩ :=
      uniform_arrival_optimal_difference hc hseq hreg huniform
    obtain ⟨Δ, hΔ, hgaps⟩ := hreg.gap_lower
    obtain ⟨mε, hvalues⟩ := huniform (Δ / 4) (by positivity)
    let K : ℝ := (mε : ℝ) + 1
    let A : ℝ := 2 * c / Δ
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hA : 0 < A := by dsimp [A]; positivity
    have hupper : ∀ s a, M.Suboptimal s a → ∀ t,
        (M.childVisit s a t : ℝ) ≤ K + A * Real.sqrt (M.parentVisit s t : ℝ) :=
      fun s a ha t => suboptimal_visit_upper_of_value_estimates hc hseq hreg hΔ s a
        (hgaps s a ha) mε (hvalues s) t
    have hsqrt : Tendsto (fun m : ℕ => Real.sqrt (m : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1
      ((eventually_ge_atTop mopt).and (hsqrt.eventually (eventually_ge_atTop (K + A + 2))))
    refine ⟨min κ 1, lt_min hκ zero_lt_one, m₀, ?_⟩
    intro s a t hnt ht
    obtain ⟨hmopt, hsize⟩ := hm₀ (M.arrivalCount s t) ht
    by_cases ha : a = M.isBest s
    · subst a
      exact (mul_le_mul_of_nonneg_right (min_le_left κ 1)
        (Real.sqrt_nonneg _)).trans (hopt s t hnt hmopt).1
    · have hu := hupper s a ha t
      have hroot : Real.sqrt (M.parentVisit s t : ℝ) ≤
          Real.sqrt (M.arrivalCount s t : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (M.parentVisit s t))
      have hs1 : 1 ≤ Real.sqrt (M.arrivalCount s t : ℝ) := by linarith
      have hs0 := Real.sqrt_nonneg (M.arrivalCount s t : ℝ)
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (M.arrivalCount s t) (α := ℝ)),
        mul_le_mul_of_nonneg_left hroot hA.le, le_mul_of_one_le_right hK hs1,
        mul_le_mul_of_nonneg_right hsize hs0,
        mul_le_mul_of_nonneg_right (min_le_right κ 1) hs0]
  obtain ⟨κ, hκ, m₀, hdrop⟩ := hgap
  suffices hroot : (fun n => (H n : ℝ)) =O[∞]
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ)) from
    hroot.trans sqrtSimulationCount_succ_equiv.1
  apply Asymptotics.IsBigO.of_bound (2 / κ + (m₀ : ℝ))
  filter_upwards [hpath] with n hn
  have hdec : ∀ x < H n, V n (x + 1) < V n x := by
    intro x hx
    obtain ⟨_, hparent, hchild⟩ := hn.2 x hx
    rw [hparent, hchild]
    exact Nat.lt_succ_of_le (hseq.child_le_parent _ _ _)
  obtain ⟨J, hJH, _, htail, hbig⟩ := finite_chain_cutoff (V n) (H n) m₀ hdec
  have hsteps : ∀ x < J,
      κ / 2 ≤ Real.sqrt (V n x : ℝ) - Real.sqrt (V n (x + 1) : ℝ) := by
    intro x hx
    have hxH := hx.trans_le hJH
    obtain ⟨hnt, hparent, hchild⟩ := hn.2 x hxH
    have hg := hdrop (state n x) (action n x) (time n x) hnt
      (by simpa only [← hparent] using hbig x hx)
    rw [← hparent, ← hchild] at hg
    have hpos : 0 < (V n x : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (hdec x hxH)
    have hspos := Real.sqrt_pos.2 hpos
    nlinarith [Real.sq_sqrt hpos.le,
      Real.sq_sqrt (Nat.cast_nonneg (V n (x + 1)) (α := ℝ)),
      sq_nonneg (Real.sqrt (V n x : ℝ) - Real.sqrt (V n (x + 1) : ℝ))]
  have htotal := Finset.sum_le_sum (s := Finset.range J)
    (fun x hx => hsteps x (Finset.mem_range.mp hx))
  simp only [Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at htotal
  simp only [hn.1] at htotal
  have hJ : (J : ℝ) ≤ (2 / κ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hκ).2
    nlinarith [Real.sqrt_nonneg (V n J : ℝ)]
  have htail' : (H n : ℝ) ≤ (J : ℝ) + m₀ := by exact_mod_cast htail
  have hlarge : 1 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast Nat.succ_pos n)
  have hm := le_mul_of_one_le_right (Nat.cast_nonneg m₀ (α := ℝ)) hlarge
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (H n) (α := ℝ)),
    abs_of_nonneg (Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ))]
  nlinarith

/-- Corollary 1.1: consecutive suboptimal actions with small priors have depth O(log log n). -/
theorem corollary11 {M : MCTSModel} {c Δmin : ℝ}
    (hc : 0 < c) (hseq : M.Sequential c)
    (huniform : M.UniformValueConsistency)
    (hΔ : 0 < Δmin) (hgaps : ∀ s a, M.Suboptimal s a → Δmin ≤ M.Gap s a)
    (V : ℕ → ℕ → ℕ) (d : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (action : ∀ n x, M.Action (state n x))
    (hpath : ∀ᶠ n : ℕ in atTop, V n 0 ≤ n + 1 ∧ 1 ≤ V n (d n) ∧ ∀ x < d n,
      M.Suboptimal (state n x) (action n x) ∧
      c * M.prior (state n x) (action n x) < Δmin / 4 ∧
      V n x = M.arrivalCount (state n x) (time n x) ∧
      V n (x + 1) = M.childVisit (state n x) (action n x) (time n x)) :
    (fun n => (d n : ℝ)) =O[∞] DepthProfile.loglogSimulationCount := by
  -- Small priors give a square-root recurrence.
  have hrec : ∃ m₀ : ℕ, ∀ s a t, M.Suboptimal s a →
      c * M.prior s a < Δmin / 4 → m₀ ≤ M.arrivalCount s t →
      (M.childVisit s a t : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt (M.arrivalCount s t : ℝ) := by
    let ε := Δmin / 8
    obtain ⟨mε, hvalues⟩ := huniform ε (by dsimp [ε]; positivity)
    have hsqrt : Tendsto (fun m : ℕ => Real.sqrt (m : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1
      (hsqrt.eventually (eventually_ge_atTop (2 * ((mε : ℝ) + 1))))
    refine ⟨m₀ + 1, ?_⟩
    intro s a t ha hp ht
    have hm : m₀ ≤ M.parentVisit s t := by
      simp only [MCTSModel.arrivalCount] at ht
      omega
    have hg := hgaps s a ha
    have hgap : 0 < M.Gap s a - 2 * ε := by dsimp [ε]; linarith
    have hb := suboptimal_visit_upper_bound hc hseq s a mε hgap
      (fun u hu => ⟨hvalues s a u hu, hvalues s (M.isBest s) u hu⟩) t
    have hcoef : c * M.prior s a / (M.Gap s a - 2 * ε) ≤ 1 / 2 := by
      apply (div_le_iff₀ hgap).2
      dsimp [ε]
      linarith
    have hlarge := hm₀ (M.parentVisit s t) hm
    have hroot : Real.sqrt (M.parentVisit s t : ℝ) ≤ Real.sqrt (M.arrivalCount s t : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (M.parentVisit s t))
    apply hb.trans
    apply max_le
    · linarith
    · exact (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hroot (by norm_num))
  obtain ⟨m₀, hrec⟩ := hrec
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let A := |Real.log (Real.log (4 : ℝ))|
  have hA : 0 ≤ A := abs_nonneg _
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply Asymptotics.IsBigO.of_bound ((1 + Real.log 2 + A) / Real.log 2 + (m₀ : ℝ))
  filter_upwards [hpath, eventually_ge_atTop 5, hloglog.eventually (eventually_ge_atTop 1)]
    with n hn hn5 hlarge
  have hpos : ∀ x ≤ d n, (1 : ℝ) ≤ V n x := by
    intro x hx
    by_cases heq : x = d n
    · exact_mod_cast (heq ▸ hn.2.1 : 1 ≤ V n x)
    · obtain ⟨_, _, hp, _⟩ := hn.2.2 x (by omega)
      rw [hp]
      exact_mod_cast Nat.succ_pos (M.parentVisit (state n x) (time n x))
  have hdec : ∀ x < d n, V n (x + 1) < V n x := by
    intro x hx
    obtain ⟨_, _, hp, hc⟩ := hn.2.2 x hx
    rw [hp, hc]
    exact Nat.lt_succ_of_le (hseq.child_le_parent _ _ _)
  obtain ⟨J, hJd, _, htail, hbig⟩ := finite_chain_cutoff (V n) (d n) m₀ hdec
  -- Each large-count step decreases log(log(4V)) by at least log 2.
  have hsteps : ∀ x < J, Real.log 2 ≤
      Real.log (Real.log (4 * (V n x : ℝ))) - Real.log (Real.log (4 * (V n (x + 1) : ℝ))) := by
    intro x hx
    have hxD := hx.trans_le hJd
    obtain ⟨ha, hp, hparent, hchild⟩ := hn.2.2 x hxD
    have hb := hrec (state n x) (action n x) (time n x) ha hp
      (by simpa only [← hparent] using hbig x hx)
    rw [← hparent, ← hchild] at hb
    have hpx := hpos x hxD.le
    have hpy := hpos (x + 1) (Nat.succ_le_of_lt hxD)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (V n (x + 1)) (α := ℝ)) hb 2
    norm_num [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (V n x) (α := ℝ))] at hsq
    have hsquare : (4 * (V n (x + 1) : ℝ)) ^ 2 ≤ 4 * (V n x : ℝ) := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < (4 * (V n (x + 1) : ℝ)) ^ 2) hsquare
    rw [Real.log_pow] at hlog
    have hlogx : 0 < Real.log (4 * (V n x : ℝ)) := Real.log_pos (by linarith)
    have hlogy : 0 < Real.log (4 * (V n (x + 1) : ℝ)) := Real.log_pos (by linarith)
    have hhalf : Real.log (4 * (V n (x + 1) : ℝ)) ≤ Real.log (4 * (V n x : ℝ)) / 2 := by
      norm_num at hlog
      linarith
    have hh := Real.log_le_log hlogy hhalf
    rw [Real.log_div hlogx.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    linarith
  have htotal := Finset.sum_le_sum (s := Finset.range J)
    (fun x hx => hsteps x (Finset.mem_range.mp hx))
  simp only [Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at htotal
  have hnreal : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  have hv0 := hpos 0 (Nat.zero_le _)
  have hvJ := hpos J hJd
  have hroot_count : (V n 0 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hn.1
  have hroot_log : Real.log (Real.log (4 * (V n 0 : ℝ))) ≤
      Real.log 2 + Real.log (Real.log (n : ℝ)) := by
    have hbound : 4 * (V n 0 : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 5)]
    have hh := Real.log_le_log (by positivity : 0 < 4 * (V n 0 : ℝ)) hbound
    simp only [Real.log_pow, Nat.cast_ofNat] at hh
    have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hh' := Real.log_le_log (Real.log_pos (by linarith : 1 < 4 * (V n 0 : ℝ))) hh
    simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hln.ne'] using hh'
  have hleaf_log : Real.log (Real.log (4 : ℝ)) ≤ Real.log (Real.log (4 * (V n J : ℝ))) :=
    Real.log_le_log (Real.log_pos (by norm_num : (1 : ℝ) < 4))
      (Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith))
  have hJ : (J : ℝ) ≤ (1 + Real.log 2 + A) / Real.log 2 * Real.log (Real.log (n : ℝ)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hlog2).2
    have hscale := le_mul_of_one_le_right (show 0 ≤ Real.log 2 + A by positivity) hlarge
    have hneg := neg_le_abs (Real.log (Real.log (4 : ℝ)))
    dsimp only [A] at hscale ⊢
    linarith
  have htail' : (d n : ℝ) ≤ (J : ℝ) + m₀ := by exact_mod_cast htail
  have hm := le_mul_of_one_le_right (Nat.cast_nonneg m₀ (α := ℝ)) hlarge
  simp only [DepthProfile.loglogSimulationCount, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (d n) (α := ℝ)),
    abs_of_nonneg (show 0 ≤ Real.log (Real.log (n : ℝ)) by linarith)]
  nlinarith

/-! ## Variable exploration -/

namespace DepthIntegral

noncomputable def exploration (c : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ m in (1 : ℝ)..(n : ℝ), 1 / (c m * Real.sqrt m)

noncomputable def critical (L : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ m in (1 : ℝ)..(n : ℝ), 1 / (m * L m)

end DepthIntegral

/-- Bounded positive potential drops along a path with a bounded tail. -/
private structure IntegralPath (H : ℕ → ℕ) (I : ℕ → ℝ) where
  potential : ℕ → ℕ → ℝ
  length : ℕ → ℕ
  κ : ℝ
  C : ℝ
  endpoint : ℝ
  tail : ℝ
  δ : ℝ
  κ_pos : 0 < κ
  C_pos : 0 < C
  endpoint_nonneg : 0 ≤ endpoint
  tail_nonneg : 0 ≤ tail
  δ_pos : 0 < δ
  paths : ∀ᶠ n : ℕ in atTop,
    1 ≤ H n ∧ δ ≤ I n ∧ potential n 0 = I n ∧
    0 ≤ potential n (length n) ∧ potential n (length n) ≤ endpoint ∧
    length n ≤ H n ∧ (H n : ℝ) ≤ (length n : ℝ) + tail ∧
    ∀ x < length n,
      κ ≤ potential n x - potential n (x + 1) ∧
      potential n x - potential n (x + 1) ≤ C

private noncomputable def integralPotential (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ m in (1 : ℝ)..u, g m

private def IntegrableFromOne (g : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable g volume a b

private theorem integralPotential_mono {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Ici 1)) (hg : ∀ x ≥ 1, 0 ≤ g x)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    integralPotential g a ≤ integralPotential g b := by
  exact intervalIntegral.integral_mono_interval le_rfl ha hab
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => hg x hx.1.le)
    ((hcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc (ha.trans hab))

private theorem reciprocal_integral_rectangles {f : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Ici 1)) (hp : ∀ x ≥ 1, 0 < f x)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hmono : MonotoneOn f (Set.Icc a b)) :
    (b - a) / f b ≤ (∫ x in a..b, 1 / f x) ∧
      (∫ x in a..b, 1 / f x) ≤ (b - a) / f a := by
  have hrec : ContinuousOn (fun x => 1 / f x) (Set.Ici 1) :=
    continuousOn_const.div hc (fun x hx => (hp x hx).ne')
  have hint := (hrec.mono (fun _ hx => (le_min ha (ha.trans hab)).trans hx.1)).intervalIntegrable
    (μ := MeasureTheory.volume)
  have hlow := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (continuous_const.intervalIntegrable a b :
      IntervalIntegrable (fun _ : ℝ => 1 / f b) MeasureTheory.volume a b) hint
    (fun x hx => one_div_le_one_div_of_le (hp x (ha.trans hx.1))
      (hmono hx ⟨hab, le_rfl⟩ hx.2))
  have hupp := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab hint
    (continuous_const.intervalIntegrable a b :
      IntervalIntegrable (fun _ : ℝ => 1 / f a) MeasureTheory.volume a b)
    (fun x hx => one_div_le_one_div_of_le (hp a ha)
      (hmono ⟨le_rfl, hab⟩ hx hx.1))
  constructor
  · simpa [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using hlow
  · simpa [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using hupp

private theorem depth_theta_of_additive_bounds {H : ℕ → ℕ} {I : ℕ → ℝ}
    {κ C R δ : ℝ} (hκ : 0 < κ) (hC : 0 < C) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hbounds : ∀ᶠ n : ℕ in atTop,
      1 ≤ H n ∧ δ ≤ I n ∧ κ * (H n : ℝ) ≤ I n + R ∧
      I n ≤ C * (H n : ℝ) + R) :
    (fun n => (H n : ℝ)) =Θ[∞] I := by
  apply theta_of_eventual_sandwich
  · exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · exact hbounds.mono (fun _ hn => hδ.le.trans hn.2.1)
  · refine ⟨(1 + R / δ) / κ, by positivity, ?_⟩
    filter_upwards [hbounds] with n hn
    have hRI : R ≤ R / δ * I n := by
      have := mul_le_mul_of_nonneg_left hn.2.1 (div_nonneg hR hδ.le)
      simpa [div_mul_cancel₀ _ hδ.ne'] using this
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hκ).2
    nlinarith [hn.2.2.1]
  · refine ⟨1 / (C + R), by positivity, ?_⟩
    filter_upwards [hbounds] with n hn
    have hH : (1 : ℝ) ≤ H n := by exact_mod_cast hn.1
    have hRH : R ≤ R * (H n : ℝ) := le_mul_of_one_le_right hR hH
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hC hR)).2
    nlinarith [hn.2.2.2]

private theorem depth_theta_of_integral_path {H : ℕ → ℕ} {I : ℕ → ℝ}
    (h : IntegralPath H I) : (fun n => (H n : ℝ)) =Θ[∞] I := by
  let R := h.endpoint + h.κ * h.tail
  have hR : 0 ≤ R := add_nonneg h.endpoint_nonneg (mul_nonneg h.κ_pos.le h.tail_nonneg)
  have hbounds : ∀ᶠ n : ℕ in atTop,
      1 ≤ H n ∧ h.δ ≤ I n ∧ h.κ * (H n : ℝ) ≤ I n + R ∧
      I n ≤ h.C * (H n : ℝ) + R := by
    filter_upwards [h.paths] with n hn
    obtain ⟨hH, hδ, hroot, hzero, hend, hJH, htail, hsteps⟩ := hn
    have hsum := And.intro
      (Finset.sum_le_sum (s := Finset.range (h.length n))
        (fun x hx => (hsteps x (Finset.mem_range.mp hx)).1))
      (Finset.sum_le_sum (s := Finset.range (h.length n))
        (fun x hx => (hsteps x (Finset.mem_range.mp hx)).2))
    simp only [Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hsum
    rw [hroot] at hsum
    have hJH' : (h.length n : ℝ) ≤ (H n : ℝ) := by exact_mod_cast hJH
    have htail' := mul_le_mul_of_nonneg_left htail h.κ_pos.le
    have hJHmul := mul_le_mul_of_nonneg_left hJH' h.C_pos.le
    have hslack := mul_nonneg h.κ_pos.le h.tail_nonneg
    dsimp [R]
    exact ⟨hH, hδ, by nlinarith [hsum.1, h.endpoint_nonneg], by nlinarith [hsum.2]⟩
  exact depth_theta_of_additive_bounds h.κ_pos h.C_pos hR h.δ_pos hbounds

/-! ## Regular variation -/

/-- Positive measurable slow variation on `[1, ∞)`, with pointwise ratio limits. -/
structure SlowlyVarying (L : ℝ → ℝ) : Prop where
  measurable : AEMeasurable L
    (MeasureTheory.volume.restrict (Set.Ici 1))
  positive : ∀ x : ℝ, 1 ≤ x → 0 < L x
  ratio : ∀ lam : ℝ, 0 < lam →
    Tendsto (fun x : ℝ => L (lam * x) / L x) atTop (𝓝 1)

/-- Positive continuous slow variation on `[1, ∞)`. -/
structure ContinuousSlowlyVarying (L : ℝ → ℝ) : Prop where
  continuous : ContinuousOn L (Set.Ici 1)
  positive : ∀ x : ℝ, 1 ≤ x → 0 < L x
  ratio : ∀ lam : ℝ, 0 < lam →
    Tendsto (fun x : ℝ => L (lam * x) / L x) atTop (𝓝 1)

private theorem rpow_form_mul_sqrt {c L : ℝ → ℝ} {α : ℝ}
    (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x) :
    ∀ x ≥ 1, c x * Real.sqrt x = Real.rpow x (α + 1 / 2) * L x := by
  intro x hx
  change c x * Real.sqrt x = x ^ (α + 1 / 2) * L x
  rw [hform x hx, Real.rpow_add (by linarith : 0 < x), ← Real.sqrt_eq_rpow]
  change Real.rpow x α * L x * Real.sqrt x = (Real.rpow x α * Real.sqrt x) * L x
  ring

private theorem regular_variation_doubling_limit {c L : ℝ → ℝ} {α : ℝ}
    (hL : ContinuousSlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x) :
    Tendsto (fun x : ℝ => c (2 * x) / c x) atTop (𝓝 (Real.rpow 2 α)) := by
  have ht := (hL.ratio 2 (by norm_num)).const_mul (Real.rpow 2 α)
  apply (show Tendsto (fun x => Real.rpow 2 α * (L (2 * x) / L x)) atTop
    (𝓝 (Real.rpow 2 α)) from by simpa using ht).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := by linarith
  rw [hform x hx, hform (2 * x) (by linarith),
    show Real.rpow (2 * x) α = Real.rpow 2 α * Real.rpow x α from
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxpos.le]
  field_simp [(Real.rpow_pos_of_pos hxpos α).ne', (hL.positive x hx).ne']

private theorem regular_variation_index_le_half {c L : ℝ → ℝ} {α : ℝ}
    (hL : ContinuousSlowlyVarying L)
    (hc : ∀ᶠ n : ℕ in atTop, c n = Real.rpow (n : ℝ) α * L n)
    (hbound : (fun n : ℕ => c n) =O[∞] DepthProfile.sqrtSimulationCount) : α ≤ 1 / 2 := by
  have hlocal_ratio_le_one {a : ℕ → ℝ} {r C : ℝ}
      (hpos : ∀ᶠ k in atTop, 0 < a k)
      (hbound : ∀ᶠ k in atTop, a k ≤ C)
      (hratio : Tendsto (fun k => a (k + 1) / a k) atTop (𝓝 r)) : r ≤ 1 := by
    by_contra hr
    have hr1 : 1 < r := lt_of_not_ge hr
    let q := (1 + r) / 2
    have hq : 1 < q := by dsimp [q]; linarith
    have hqr : q < r := by dsimp [q]; linarith
    have hstep : ∀ᶠ k in atTop, q * a k ≤ a (k + 1) := by
      filter_upwards [hpos, hratio.eventually (lt_mem_nhds hqr)] with k hk hratio_k
      exact ((lt_div_iff₀ hk).1 hratio_k).le
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (hpos.and (hbound.and hstep))
    have hdiv : Tendsto (fun k => a (k + K)) atTop atTop := by
      apply tendsto_atTop_of_geom_le (by simpa using (hK K (le_refl K)).1) hq
      intro k
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hK (k + K) (by omega)).2.2
    obtain ⟨k, hk⟩ := (hdiv.eventually (eventually_gt_atTop C)).exists
    exact (not_lt_of_ge (hK (k + K) (by omega)).2.1) hk
  let p : ℕ → ℝ := fun k => (2 : ℝ) ^ k
  let a : ℕ → ℝ := fun k => Real.rpow (p k) (α - 1 / 2) * L (p k)
  have hp : ∀ k, 0 < p k := fun k => pow_pos (by norm_num) k
  have hpNat : Tendsto (fun k : ℕ => (2 : ℕ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hpReal : Tendsto p atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hpOne : ∀ k, 1 ≤ p k := fun _ => one_le_pow₀ (by norm_num)
  have ha : ∀ k, 0 < a k := fun k =>
    mul_pos (Real.rpow_pos_of_pos (hp k) _) (hL.positive _ (hpOne k))
  obtain ⟨C, hC, hCbound⟩ := hbound.exists_pos
  have habound : ∀ᶠ k in atTop, a k ≤ C := by
    filter_upwards [hpNat.eventually hc, hpNat.eventually hCbound.bound] with k hck hk
    have hrepr : c ((2 : ℕ) ^ k) = Real.rpow (p k) α * L (p k) := by
      simpa [p] using hck
    have heq : a k = c ((2 : ℕ) ^ k) / Real.sqrt (p k) := by
      rw [hrepr]
      dsimp [a]
      rw [Real.rpow_sub (hp k), ← Real.sqrt_eq_rpow]
      ring
    rw [heq]
    apply (div_le_iff₀ (Real.sqrt_pos.2 (hp k))).2
    have hcle : c ((2 : ℕ) ^ k) ≤ C * Real.sqrt (p k) := by
      have := (le_abs_self (c ((2 : ℕ) ^ k))).trans
        (by simpa [DepthProfile.sqrtSimulationCount, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), p] using hk)
      exact this
    exact hcle
  have hratio_eq : ∀ k, a (k + 1) / a k =
      Real.rpow 2 (α - 1 / 2) * (L (2 * p k) / L (p k)) := by
    intro k
    have hLk : L (p k) ≠ 0 := (hL.positive _ (hpOne k)).ne'
    have hrk : Real.rpow (p k) (α - 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos (hp k) _).ne'
    have hsucc : p (k + 1) = 2 * p k := by simp [p, pow_succ, mul_comm]
    dsimp [a]
    rw [hsucc, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (hp k).le]
    field_simp [hrk, hLk]
    exact mul_div_cancel_left₀ _ (ne_of_gt (Real.rpow_pos_of_pos (hp k) _))
  have hratio : Tendsto (fun k => a (k + 1) / a k) atTop
      (𝓝 (Real.rpow 2 (α - 1 / 2))) := by
    have h := ((hL.ratio 2 (by norm_num)).comp hpReal).const_mul (Real.rpow 2 (α - 1 / 2))
    simpa only [hratio_eq, mul_one] using h
  have hle := hlocal_ratio_le_one (Filter.Eventually.of_forall ha) habound hratio
  by_contra hα
  have hpos : 0 < α - 1 / 2 := by linarith
  have hgt : 1 < Real.rpow 2 (α - 1 / 2) := Real.one_lt_rpow (by norm_num) hpos
  linarith

private theorem exploration_eq_critical_of_sqrt_form {c L : ℝ → ℝ}
    (hc : ∀ m : ℝ, 1 ≤ m → c m = Real.sqrt m * L m) :
    DepthIntegral.exploration c =ᶠ[atTop] DepthIntegral.critical L := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp [DepthIntegral.exploration, DepthIntegral.critical]
  apply intervalIntegral.integral_congr
  intro m hm
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Set.uIcc_of_le hn'] at hm
  dsimp only
  rw [hc m hm.1]
  congr 1
  have hs := Real.sq_sqrt (show 0 ≤ m by linarith [hm.1])
  calc
    (Real.sqrt m * L m) * Real.sqrt m = (Real.sqrt m) ^ 2 * L m := by ring
    _ = m * L m := by rw [hs]

/-! ## Finite depth caps -/

private theorem finite_depth_capped_rate (H : ℕ → ℕ) (L : ℕ) (I : ℕ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hI : ∀ᶠ n : ℕ in atTop, δ ≤ I n)
    (hdepth : ∀ᶠ n : ℕ in atTop, H n ≤ L ∧ (L = 0 ∨ 1 ≤ H n)) :
    (fun n => (H n : ℝ)) =Θ[∞] (fun n => min (L : ℝ) (I n)) := by
  by_cases hL : L = 0
  · apply Filter.EventuallyEq.isTheta
    filter_upwards [hdepth, hI] with n hn hi
    have hH : H n = 0 := by omega
    simp [hH, hL, min_eq_left (hδ.le.trans hi)]
  · have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hL)
    let q := min (L : ℝ) δ
    have hq : 0 < q := lt_min hLp hδ
    apply theta_of_eventual_sandwich
    · exact Filter.Eventually.of_forall (fun n => by positivity)
    · filter_upwards [hI] with n hn
      exact le_min hLp.le (hδ.le.trans hn)
    · refine ⟨(L : ℝ) / q, div_pos hLp hq, ?_⟩
      filter_upwards [hdepth, hI] with n hn hi
      have hH : (H n : ℝ) ≤ L := by exact_mod_cast hn.1
      have hmin : q ≤ min (L : ℝ) (I n) := min_le_min (le_refl _) hi
      have hmul := mul_le_mul_of_nonneg_left hmin (div_pos hLp hq).le
      rw [div_mul_cancel₀ _ hq.ne'] at hmul
      exact hH.trans hmul
    · refine ⟨1 / (L : ℝ), one_div_pos.mpr hLp, ?_⟩
      filter_upwards [hdepth] with n hn
      have hH : (1 : ℝ) ≤ H n := by exact_mod_cast hn.2.resolve_left hL
      have hmul := mul_le_mul_of_nonneg_left (min_le_left (L : ℝ) (I n))
        (one_div_pos.mpr hLp).le
      rw [one_div_mul_cancel hLp.ne'] at hmul
      exact hmul.trans hH

/-! ## Variable-coefficient visit bounds -/

namespace ExplorationSchedule

noncomputable def mass (c : ℝ → ℝ) (m : ℝ) : ℝ := c m * Real.sqrt m

end ExplorationSchedule

structure Assumption.ExplorationSchedule (c : ℝ → ℝ) where
  threshold : ℕ
  threshold_pos : 1 ≤ threshold
  positive : ∀ x ≥ 1, 0 < c x
  continuous : ContinuousOn c (Set.Ici 1)
  monotone : MonotoneOn (ExplorationSchedule.mass c) (Set.Ici (threshold : ℝ))

private theorem regular_variation_of_schedule {c L : ℝ → ℝ} {α : ℝ}
    (hc : Assumption.ExplorationSchedule c)
    (hL : ContinuousSlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x) :
    -(1 / 2 : ℝ) ≤ α ∧ (α < 1 / 2 → c =O[∞] Real.sqrt) ∧ (1 / 2 < α → Real.sqrt =O[∞] c) := by
  have hlocal_iterate_upper {f : ℝ → ℝ} {q D : ℝ} (hq : 0 ≤ q) (hD : 0 ≤ D)
      (hd : ∀ x : ℝ, q ≤ x → f (2 * x) ≤ D * f x) {y : ℝ} (hy : q ≤ y) :
      ∀ j : ℕ, f ((2 : ℝ) ^ j * y) ≤ D ^ j * f y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have harg : q ≤ 2 ^ j * y := hy.trans (le_mul_of_one_le_left (hq.trans hy) hpow)
      have hh := hd (2 ^ j * y) harg
      have hm := mul_le_mul_of_nonneg_left ih hD
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh.trans hm
  have hlocal_iterate_lower {f : ℝ → ℝ} {q D : ℝ} (hq : 0 ≤ q) (hD : 0 ≤ D)
      (hd : ∀ x : ℝ, q ≤ x → D * f x ≤ f (2 * x)) {y : ℝ} (hy : q ≤ y) :
      ∀ j : ℕ, D ^ j * f y ≤ f ((2 : ℝ) ^ j * y) := by
    have hneg : ∀ x : ℝ, q ≤ x → -f (2 * x) ≤ D * (-f x) := by
      intro x hx
      simpa only [mul_neg, neg_le_neg_iff] using hd x hx
    simpa only [mul_neg, neg_le_neg_iff] using
      (hlocal_iterate_upper (f := fun x => -f x) hq hD hneg hy)
  have hlocal_comparison {f g : ℝ → ℝ} {M : ℝ}
      (hM : 0 < M) (hfM : 0 < f M) (hgM : 0 < g M)
      (hfmono : MonotoneOn f (Set.Ici M)) (hgmono : MonotoneOn g (Set.Ici M))
      (hf : ∀ x ≥ M, f (2 * x) ≤ 2 * f x)
      (hg : ∀ x ≥ M, 2 * g x ≤ g (2 * x)) :
      ∃ B : ℝ, 0 < B ∧ ∀ x ≥ M, f x ≤ B * g x := by
    let B := 2 * f M / g M
    have hB : 0 < B := by dsimp [B]; positivity
    refine ⟨B, hB, ?_⟩
    intro x hx
    obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near ((one_le_div hM).2 hx) (by norm_num : (1 : ℝ) < 2)
    have hlo : (2 : ℝ) ^ k * M ≤ x := (le_div_iff₀ hM).1 hk
    have hhi : x < (2 : ℝ) ^ (k + 1) * M := (div_lt_iff₀ hM).1 hk'
    have hpow : ∀ j : ℕ, M ≤ (2 : ℝ) ^ j * M := fun j =>
      le_mul_of_one_le_left hM.le (one_le_pow₀ (by norm_num))
    have hu := (hfmono hx (hpow (k + 1)) hhi.le).trans
      (hlocal_iterate_upper hM.le (by norm_num : (0 : ℝ) ≤ 2) hf (le_refl M) (k + 1))
    have hl := (hlocal_iterate_lower hM.le (by norm_num : (0 : ℝ) ≤ 2) hg
      (le_refl M) k).trans (hgmono (hpow k) hx hlo)
    have hs := mul_le_mul_of_nonneg_left hl hB.le
    have heq : B * ((2 : ℝ) ^ k * g M) = (2 : ℝ) ^ (k + 1) * f M := by
      dsimp [B]
      rw [pow_succ]
      field_simp
    rw [heq] at hs
    exact hu.trans hs
  have hlocal_mass_ratio {c L : ℝ → ℝ} {α : ℝ}
      (hL : ContinuousSlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x) :
      Tendsto (fun x : ℝ => ExplorationSchedule.mass c (2 * x) / ExplorationSchedule.mass c x)
        atTop (𝓝 (Real.rpow 2 (α + 1 / 2))) := by
    apply regular_variation_doubling_limit (c := ExplorationSchedule.mass c) hL
    intro x hx
    exact rpow_form_mul_sqrt hform x hx
  have hlocal_threshold {c : ℝ → ℝ}
      (hc : Assumption.ExplorationSchedule c) (K : ℝ) :
      ∃ M : ℝ, 1 ≤ M ∧ K ≤ M ∧ (∀ x ≥ 1, 0 < ExplorationSchedule.mass c x) ∧
        MonotoneOn (ExplorationSchedule.mass c) (Set.Ici M) := by
    refine ⟨max (hc.threshold : ℝ) (max 1 K), (le_max_left 1 K).trans (le_max_right _ _),
      (le_max_right 1 K).trans (le_max_right _ _), fun x hx =>
        mul_pos (hc.positive x hx) (Real.sqrt_pos.2 (by linarith)), ?_⟩
    intro x hx y hy hxy
    exact hc.monotone ((le_max_left (hc.threshold : ℝ) (max 1 K)).trans hx)
      ((le_max_left (hc.threshold : ℝ) (max 1 K)).trans hy) hxy
  have hlocal_cancel_sqrt {f g : ℝ → ℝ} {M B : ℝ} (hM1 : 1 ≤ M)
      (hpos : ∀ x ≥ 1, 0 < f x ∧ 0 < g x)
      (hb : ∀ x ≥ M, f x * Real.sqrt x ≤ B * (g x * Real.sqrt x)) :
      f =O[∞] g := by
    apply Asymptotics.IsBigO.of_bound B
    filter_upwards [eventually_ge_atTop M] with x hx
    have hx1 := hM1.trans hx
    obtain ⟨hf, hg⟩ := hpos x hx1
    have hh : f x ≤ B * g x := by
      apply le_of_mul_le_mul_right (a := Real.sqrt x) _ (Real.sqrt_pos.2 (by linarith))
      simpa only [mul_assoc] using hb x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hf.le, abs_of_nonneg hg.le] using hh
  have hlocal_subcritical {c L : ℝ → ℝ} {α : ℝ}
      (hc : Assumption.ExplorationSchedule c) (hL : ContinuousSlowlyVarying L)
      (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x) (hα : α < 1 / 2) :
      c =O[∞] Real.sqrt := by
    have hr : Real.rpow 2 (α + 1 / 2) < 2 := by
      simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (show α + 1 / 2 < 1 by linarith)
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      ((hlocal_mass_ratio hL hform).eventually (gt_mem_nhds hr))
    obtain ⟨M, hM1, hKM, hfp, hmono⟩ := hlocal_threshold hc K
    have hd : ∀ x ≥ M, ExplorationSchedule.mass c (2 * x) ≤ 2 * ExplorationSchedule.mass c x :=
      fun x hx => ((div_lt_iff₀ (hfp x (hM1.trans hx))).1 (hK x (hKM.trans hx))).le
    obtain ⟨B, _, hb⟩ := hlocal_comparison (g := id) (by linarith) (hfp M hM1)
      (show (0 : ℝ) < M by linarith) hmono monotoneOn_id hd (fun _ _ => le_rfl)
    apply hlocal_cancel_sqrt (B := B) hM1
      (fun x hx => ⟨hc.positive x hx, Real.sqrt_pos.2 (by linarith)⟩)
    intro x hx
    simpa only [ExplorationSchedule.mass, Real.mul_self_sqrt (by linarith : 0 ≤ x)] using hb x hx
  have hlocal_supercritical {c L : ℝ → ℝ} {α : ℝ}
      (hc : Assumption.ExplorationSchedule c) (hL : ContinuousSlowlyVarying L)
      (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x) (hα : 1 / 2 < α) :
      Real.sqrt =O[∞] c := by
    have hr : 2 < Real.rpow 2 (α + 1 / 2) := by
      simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (show 1 < α + 1 / 2 by linarith)
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      ((hlocal_mass_ratio hL hform).eventually (lt_mem_nhds hr))
    obtain ⟨M, hM1, hKM, hfp, hmono⟩ := hlocal_threshold hc K
    have hd : ∀ x ≥ M, 2 * ExplorationSchedule.mass c x ≤ ExplorationSchedule.mass c (2 * x) :=
      fun x hx => ((lt_div_iff₀ (hfp x (hM1.trans hx))).1 (hK x (hKM.trans hx))).le
    obtain ⟨B, _, hb⟩ := hlocal_comparison (f := id) (by linarith)
      (show (0 : ℝ) < M by linarith) (hfp M hM1) monotoneOn_id hmono (fun _ _ => le_rfl) hd
    apply hlocal_cancel_sqrt (B := B) hM1
      (fun x hx => ⟨Real.sqrt_pos.2 (by linarith), hc.positive x hx⟩)
    intro x hx
    simpa only [ExplorationSchedule.mass, Real.mul_self_sqrt (by linarith : 0 ≤ x)] using hb x hx
  refine ⟨?_, hlocal_subcritical hc hL hform, hlocal_supercritical hc hL hform⟩
  by_contra hh
  have hα : α + 1 / 2 < 0 := by linarith
  have hr : Real.rpow 2 (α + 1 / 2) < 1 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hα
  have hl := (hlocal_mass_ratio hL hform).eventually (gt_mem_nhds hr)
  obtain ⟨x, hx, hrx⟩ := ((eventually_ge_atTop (hc.threshold : ℝ)).and hl).exists
  have hx1 : 1 ≤ x := (by exact_mod_cast hc.threshold_pos : (1 : ℝ) ≤ hc.threshold).trans hx
  have hxy : x ≤ 2 * x := by linarith
  have hle := hc.monotone hx (hx.trans hxy) hxy
  have hp : 0 < ExplorationSchedule.mass c x :=
    mul_pos (hc.positive x hx1) (Real.sqrt_pos.2 (by linarith))
  have hlt := (div_lt_iff₀ hp).1 hrx
  linarith

private theorem scheduled_optimal_share_of_prior {M : MCTSModel} {c : ℝ → ℝ}
    (hseq : M.Scheduled c) (hc : ∀ x ≥ 1, 0 < c x)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ m₀ : ℕ, ∀ s t,
      ¬ M.isTerminal s → m₀ ≤ M.parentVisit s t →
      θ * (M.parentVisit s t : ℝ) ≤ M.childVisit s (M.isBest s) t := by
  have hlocal_prior_comparison {M : MCTSModel} {c : ℝ → ℝ}
      (hseq : M.Scheduled c) (s : M.State) (a : M.Action s) (t : ℕ)
      (hsel : M.selectedAt s a t)
      (hvalues : M.searchValue s a t ≤ M.searchValue s (M.isBest s) t)
      (hF : 0 < ExplorationSchedule.mass c (M.parentVisit s t)) :
      M.prior s (M.isBest s) * (1 + (M.childVisit s a t : ℝ)) ≤
        M.prior s a * (1 + (M.childVisit s (M.isBest s) t : ℝ)) := by
    have hs := hseq.argmax s a t hsel (M.isBest s)
    simp only [MCTSModel.puctScore, mul_assoc] at hs
    rw [mul_left_comm (c _) (M.prior s (M.isBest s)), mul_left_comm (c _) (M.prior s a),
      ← ExplorationSchedule.mass] at hs
    have hb : M.prior s (M.isBest s) * ExplorationSchedule.mass c (M.parentVisit s t) /
        (1 + (M.childVisit s (M.isBest s) t : ℝ)) ≤
        M.prior s a * ExplorationSchedule.mass c (M.parentVisit s t) /
          (1 + (M.childVisit s a t : ℝ)) := by linarith
    have hm := (div_le_div_iff₀ (by positivity : 0 < 1 + (M.childVisit s (M.isBest s) t : ℝ))
      (by positivity : 0 < 1 + (M.childVisit s a t : ℝ))).1 hb
    apply (mul_le_mul_iff_left₀ hF).1
    convert hm using 1 <;> ring
  obtain ⟨p, hp, hprior⟩ := hopt
  obtain ⟨Δ, hΔ, hg⟩ := hreg.gap_lower
  obtain ⟨mv, hv⟩ := hu (Δ / 4) (by positivity)
  let m := max 1 mv
  obtain ⟨b, hb, hf⟩ := hreg.finite_branching
  have hsub : ∀ s a t, ¬ M.isTerminal s → M.Suboptimal s a →
      (M.childVisit s a t : ℝ) ≤ (p * m + 1 + M.childVisit s (M.isBest s) t) / p := by
    intro s a t hnt ha
    have hnstar : (0 : ℝ) ≤ M.childVisit s (M.isBest s) t := by positivity
    apply (le_div_iff₀ hp).2
    by_cases hz : M.childVisit s a t = 0
    · simp only [hz, Nat.cast_zero, zero_mul]; positivity
    let u := hseq.toCountUpdates.lastSelection s a t
    obtain ⟨hut, hsel, hcount⟩ :=
      hseq.toCountUpdates.lastSelection_spec s a t (Nat.pos_of_ne_zero hz)
    change u < t at hut
    change M.selectedAt s a u at hsel
    change M.childVisit s a t = M.childVisit s a u + 1 at hcount
    by_cases hm : m ≤ M.parentVisit s u
    · have hmu : mv ≤ M.parentVisit s u := (le_max_right _ _).trans hm
      have hi := abs_le.mp (hv s a u hmu)
      have hs := abs_le.mp (hv s (M.isBest s) u hmu)
      have horder : M.searchValue s a u ≤ M.searchValue s (M.isBest s) u := by
        have hgap := hg s a ha
        dsimp [MCTSModel.Gap] at hgap
        linarith [hi.2, hs.1]
      have hcomp := hlocal_prior_comparison hseq s a u hsel horder
        (by
          have hm1 : 1 ≤ M.parentVisit s u := (le_max_left _ _).trans hm
          exact mul_pos (hc _ (by exact_mod_cast hm1))
            (Real.sqrt_pos.2 (by exact_mod_cast (Nat.zero_lt_of_lt hm1))))
      letI : Finite (M.Action s) := (hf s).1
      letI := Fintype.ofFinite (M.Action s)
      have hP : M.prior s a ≤ 1 :=
        (Summable.of_finite.le_tsum a (fun b _ => M.prior_nonneg s b)).trans_eq
          (M.prior_sum s)
      have hlo := mul_le_mul_of_nonneg_right (hprior s hnt)
        (show (0 : ℝ) ≤ 1 + (M.childVisit s a u : ℝ) by positivity)
      have hhi := mul_le_mul_of_nonneg_right hP
        (show (0 : ℝ) ≤ 1 + (M.childVisit s (M.isBest s) u : ℝ) by positivity)
      have hmono : (M.childVisit s (M.isBest s) u : ℝ) ≤ M.childVisit s (M.isBest s) t := by
        exact_mod_cast hseq.toCountUpdates.child_monotone s (M.isBest s) hut.le
      have hcnt : (M.childVisit s a t : ℝ) = (M.childVisit s a u : ℝ) + 1 := by
        exact_mod_cast hcount
      nlinarith [Nat.cast_nonneg m (α := ℝ)]
    · have hle := hseq.child_le_parent s a u
      have hn : M.childVisit s a t ≤ m := by omega
      have hm' : (M.childVisit s a t : ℝ) ≤ m := by exact_mod_cast hn
      nlinarith
  let D : ℝ := 1 + (b : ℝ) / p
  let C : ℝ := (b : ℝ) * ((m : ℝ) + 1 / p)
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by
    have : 0 ≤ (b : ℝ) / p := by positivity
    dsimp [D]
    linarith
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (2 * C)
  refine ⟨1 / (2 * D), by positivity, ?_, m₀, ?_⟩
  · apply (div_lt_one (by positivity)).2
    linarith
  · intro s t hnt ht
    letI : Finite (M.Action s) := (hf s).1
    have hgap := count_gap_sum_le hseq.toCountUpdates s t b (hf s).2
      (show 0 ≤ (p * m + 1 + M.childVisit s (M.isBest s) t) / p by positivity)
      (fun a ha => hsub s a t hnt ha)
    have hid : (M.childVisit s (M.isBest s) t : ℝ) +
        (b : ℝ) * ((p * m + 1 + M.childVisit s (M.isBest s) t) / p) =
        C + D * M.childVisit s (M.isBest s) t := by
      dsimp [C, D]; field_simp; ring
    have hlarge : 2 * C ≤ (M.parentVisit s t : ℝ) := hm₀.trans (by exact_mod_cast ht)
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * D)).2
    linarith

private theorem frontier_bound_of_optimal_share {M : MCTSModel} {θ : ℝ} {m₀ : ℕ} (hθ : 0 < θ)
    (hr : ∀ s t, ¬ M.isTerminal s → m₀ ≤ M.parentVisit s t →
      θ * (M.parentVisit s t : ℝ) ≤ M.childVisit s (M.isBest s) t) :
    ∃ B : ℕ, ∀ s t, ¬ M.isTerminal s → M.childVisit s (M.isBest s) t = 0 →
      M.arrivalCount s t ≤ B := by
  refine ⟨max 1 m₀, ?_⟩
  intro s t hnt hz
  by_contra h
  have hm : m₀ ≤ M.parentVisit s t := by simp only [MCTSModel.arrivalCount] at h; omega
  have hm1 : 1 ≤ M.parentVisit s t := by simp only [MCTSModel.arrivalCount] at h; omega
  have hb := hr s t hnt hm
  rw [hz, Nat.cast_zero] at hb
  have hp : 0 < θ * (M.parentVisit s t : ℝ) :=
    mul_pos hθ (by exact_mod_cast (by omega : 0 < M.parentVisit s t))
  linarith

/-! ## Saturated depth estimates -/

noncomputable def DepthIntegral.saturated (c : ℝ → ℝ) (n : ℕ) : ℝ :=
  Real.log (n : ℝ) + DepthIntegral.exploration c n

private theorem exploration_integrand_continuous {c : ℝ → ℝ}
    (hc : Assumption.ExplorationSchedule c) :
    ContinuousOn (fun x => 1 / ExplorationSchedule.mass c x) (Set.Ici 1) := by
  apply continuousOn_const.div (hc.continuous.mul Real.continuous_sqrt.continuousOn)
  intro x hx
  change 1 ≤ x at hx
  exact (mul_pos (hc.positive x hx) (Real.sqrt_pos.2 (by linarith [hx]))).ne'

private theorem integralPotential_mono_of_integrable {g : ℝ → ℝ}
    (hi : IntegrableFromOne g) (hg : ∀ x ≥ 1, 0 ≤ g x)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    integralPotential g a ≤ integralPotential g b := by
  exact intervalIntegral.integral_mono_interval le_rfl ha hab
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => hg x hx.1.le)
    (hi 1 b le_rfl (ha.trans hab))

private theorem positive_integral_lower {g : ℝ → ℝ}
    (hi : IntegrableFromOne g) (hp : ∀ x ≥ 1, 0 < g x) :
    ∃ δ > 0, ∀ n : ℝ, 2 ≤ n → δ ≤ integralPotential g n := by
  have hδ : 0 < integralPotential g 2 :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hi 1 2 le_rfl (by norm_num))
      (fun x hx => hp x hx.1.le) (by norm_num)
  refine ⟨integralPotential g 2, hδ, fun n hn => ?_⟩
  exact integralPotential_mono_of_integrable hi (fun x hx => (hp x hx).le) (by norm_num) hn

private theorem positive_integral_comparison_of_integrable {f g : ℝ → ℝ}
    (hf : IntegrableFromOne f) (hg : IntegrableFromOne g)
    (hfp : ∀ x ≥ 1, 0 < f x) (hgp : ∀ x ≥ 1, 0 < g x)
    {C : ℝ} (hC : 0 < C) (hle : ∀ᶠ x : ℝ in atTop, f x ≤ C * g x) :
    (fun n : ℕ => integralPotential f n) =O[∞]
      (fun n : ℕ => integralPotential g n) := by
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.1 hle
  obtain ⟨m, hm⟩ := exists_nat_ge (max 2 r)
  have hm2 : (2 : ℝ) ≤ m := (le_max_left _ _).trans hm
  have hm1 : (1 : ℝ) ≤ m := by linarith
  obtain ⟨δ, hδ, hδbound⟩ := positive_integral_lower hg hgp
  let K := integralPotential f m
  have hK : 0 ≤ K :=
    intervalIntegral.integral_nonneg hm1 (fun x hx => (hfp x hx.1).le)
  apply Asymptotics.IsBigO.of_bound (C + K / δ)
  filter_upwards [eventually_ge_atTop m] with n hn
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 := hm1.trans hmn
  have hδn : δ ≤ integralPotential g n := hδbound n (hm2.trans hmn)
  have hcmp := intervalIntegral.integral_mono_on (μ := volume) hmn
    (hf m n hm1 hmn) ((hg m n hm1 hmn).const_mul C)
    (fun x hx => hr x (((le_max_right 2 r).trans hm).trans hx.1))
  rw [intervalIntegral.integral_const_mul, ← intervalIntegral.integral_interval_sub_left
    (hf 1 n le_rfl hn1) (hf 1 m le_rfl hm1),
    ← intervalIntegral.integral_interval_sub_left
      (hg 1 n le_rfl hn1) (hg 1 m le_rfl hm1)] at hcmp
  change integralPotential f n - integralPotential f m ≤
    C * (integralPotential g n - integralPotential g m) at hcmp
  have hg0 : 0 ≤ integralPotential g m :=
    intervalIntegral.integral_nonneg hm1 (fun x hx => (hgp x hx.1).le)
  have hgN : 0 ≤ integralPotential g n :=
    intervalIntegral.integral_nonneg hn1 (fun x hx => (hgp x hx.1).le)
  have hfN : 0 ≤ integralPotential f n :=
    intervalIntegral.integral_nonneg hn1 (fun x hx => (hfp x hx.1).le)
  have hscale := mul_le_mul_of_nonneg_left hδn (div_nonneg hK hδ.le)
  rw [div_mul_cancel₀ _ hδ.ne'] at hscale
  simp only [Real.norm_eq_abs, abs_of_nonneg hfN, abs_of_nonneg hgN]
  dsimp [K] at *
  nlinarith [mul_nonneg hC.le hg0]

private theorem positive_integral_comparison {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ici 1)) (hg : ContinuousOn g (Set.Ici 1))
    (hfp : ∀ x ≥ 1, 0 < f x) (hgp : ∀ x ≥ 1, 0 < g x)
    {C : ℝ} (hC : 0 < C) (hle : ∀ᶠ x : ℝ in atTop, f x ≤ C * g x) :
    (fun n : ℕ => integralPotential f n) =O[∞] (fun n : ℕ => integralPotential g n) := by
  exact positive_integral_comparison_of_integrable
    (fun a b ha hab => (hf.mono (fun _ hx => ha.trans hx.1)).intervalIntegrable_of_Icc hab)
    (fun a b ha hab => (hg.mono (fun _ hx => ha.trans hx.1)).intervalIntegrable_of_Icc hab)
    hfp hgp hC hle

private theorem nonnegative_add_theta_right {f g : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : ∀ᶠ n in atTop, 0 ≤ g n)
    (hfg : f =O[∞] g) : (fun n => f n + g n) =Θ[∞] g := by
  refine ⟨hfg.add (Asymptotics.isBigO_refl g atTop), Asymptotics.IsBigO.of_bound 1 ?_⟩
  filter_upwards [hf, hg] with n hn hm
  simpa only [Real.norm_of_nonneg hm, Real.norm_of_nonneg (add_nonneg hn hm), one_mul] using
    le_add_of_nonneg_left hn

private theorem saturated_depth_weak {c : ℝ → ℝ} (hc : Assumption.ExplorationSchedule c)
    (hbound : c =O[∞] Real.sqrt) :
    DepthIntegral.saturated c =Θ[∞] DepthIntegral.exploration c := by
  have hlocal_log_upper {c : ℝ → ℝ} (hc : Assumption.ExplorationSchedule c)
      (hbound : c =O[∞] Real.sqrt) :
      (fun n : ℕ => Real.log (n : ℝ)) =O[∞] DepthIntegral.exploration c := by
    obtain ⟨B, hB, hb⟩ := hbound.exists_pos
    have ho := positive_integral_comparison (show ContinuousOn (fun x : ℝ => 1 / x) (Set.Ici 1) from
        continuousOn_const.div continuousOn_id
          (fun _ hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))
      (exploration_integrand_continuous hc)
      (fun x hx => one_div_pos.mpr (by linarith))
      (fun x hx => one_div_pos.mpr
        (mul_pos (hc.positive x hx) (Real.sqrt_pos.2 (by linarith)))) hB (by
          filter_upwards [hb.bound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
          have hp := hc.positive x hx1
          have hx0 : 0 < x := by linarith
          simp only [Real.norm_eq_abs, abs_of_nonneg hp.le,
            abs_of_nonneg (Real.sqrt_nonneg _)] at hx
          have hh := mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg x)
          rw [mul_assoc, Real.mul_self_sqrt hx0.le] at hh
          dsimp [ExplorationSchedule.mass]
          rw [mul_one_div]
          exact (div_le_div_iff₀ hx0 (mul_pos hp (Real.sqrt_pos.2 hx0))).2 (by nlinarith))
    exact ho.congr' (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      simpa [integralPotential] using integral_one_div_of_pos
        (by norm_num : (0 : ℝ) < 1)
        (show (0 : ℝ) < n by exact_mod_cast Nat.zero_lt_of_lt hn)) Filter.EventuallyEq.rfl
  apply nonnegative_add_theta_right _ _ (hlocal_log_upper hc hbound)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact Real.log_nonneg (by exact_mod_cast hn)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply intervalIntegral.integral_nonneg (by exact_mod_cast hn)
    intro x hx
    have hp := hc.positive x hx.1
    positivity

private theorem saturated_depth_strong {c : ℝ → ℝ} (hc : Assumption.ExplorationSchedule c)
    (hbound : Real.sqrt =O[∞] c) :
    DepthIntegral.saturated c =Θ[∞] (fun n : ℕ => Real.log (n : ℝ)) := by
  have hlocal_integral_upper {c : ℝ → ℝ} (hc : Assumption.ExplorationSchedule c)
      (hbound : Real.sqrt =O[∞] c) :
      DepthIntegral.exploration c =O[∞] (fun n : ℕ => Real.log (n : ℝ)) := by
    obtain ⟨B, hB, hb⟩ := hbound.exists_pos
    have ho := positive_integral_comparison (exploration_integrand_continuous hc)
      (show ContinuousOn (fun x : ℝ => 1 / x) (Set.Ici 1) from
        continuousOn_const.div continuousOn_id
          (fun _ hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))
      (fun x hx => one_div_pos.mpr
        (mul_pos (hc.positive x hx) (Real.sqrt_pos.2 (by linarith))))
      (fun x hx => one_div_pos.mpr (by linarith)) hB (by
          filter_upwards [hb.bound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
          have hp := hc.positive x hx1
          have hx0 : 0 < x := by linarith
          simp only [Real.norm_eq_abs, abs_of_nonneg hp.le,
            abs_of_nonneg (Real.sqrt_nonneg _)] at hx
          have hh := mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg x)
          rw [Real.mul_self_sqrt hx0.le] at hh
          dsimp [ExplorationSchedule.mass]
          rw [mul_one_div]
          exact (div_le_div_iff₀ (mul_pos hp (Real.sqrt_pos.2 hx0)) hx0).2 (by nlinarith))
    exact ho.congr' Filter.EventuallyEq.rfl (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      simpa [integralPotential] using integral_one_div_of_pos
        (by norm_num : (0 : ℝ) < 1)
        (show (0 : ℝ) < n by exact_mod_cast Nat.zero_lt_of_lt hn))
  have hh := nonnegative_add_theta_right (f := DepthIntegral.exploration c)
    (g := fun n : ℕ => Real.log (n : ℝ)) (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      apply intervalIntegral.integral_nonneg (by exact_mod_cast hn)
      intro x hx
      have hp := hc.positive x hx.1
      positivity) (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact Real.log_nonneg (by exact_mod_cast hn)) (hlocal_integral_upper hc hbound)
  simpa only [DepthIntegral.saturated, add_comm] using hh

/-! ## Measurable exploration estimates -/

/-- Boundedness on each compact interval in `[1, ∞)`. -/
def LocallyBounded (f : ℝ → ℝ) : Prop :=
  ∀ b ≥ (1 : ℝ), Bornology.IsBounded (f '' Set.Icc 1 b)

/-- Exploration mass is eventually nondecreasing up to a fixed factor. -/
private structure Assumption.CountExplorationSchedule (c : ℝ → ℝ) where
  threshold : ℕ
  threshold_pos : 1 ≤ threshold
  positive : ∀ x ≥ 1, 0 < c x
  A : ℝ
  A_one : 1 ≤ A
  monotone : ∀ x y : ℝ, (threshold : ℝ) ≤ x → x ≤ y →
    ExplorationSchedule.mass c x ≤ A * ExplorationSchedule.mass c y

/-- Measurable schedules with bounded oscillation and fixed-ratio growth. -/
private structure Assumption.GeneralExplorationSchedule (c : ℝ → ℝ)
    extends Assumption.CountExplorationSchedule c where
  integrable : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
    IntervalIntegrable (fun x => 1 / ExplorationSchedule.mass c x) MeasureTheory.volume a b
  scaling : ∀ η : ℝ, 0 < η → η < 1 →
    ∃ R : ℝ, 0 < R ∧ ∃ m : ℕ, ∀ x y : ℝ, (m : ℝ) ≤ x →
      η * x ≤ y → y ≤ x →
      ExplorationSchedule.mass c x ≤ R * ExplorationSchedule.mass c y

private def countSchedule_of_schedule {c : ℝ → ℝ}
    (hc : Assumption.ExplorationSchedule c) : Assumption.CountExplorationSchedule c := {
  threshold := hc.threshold
  threshold_pos := hc.threshold_pos
  positive := hc.positive
  A := 1
  A_one := le_rfl
  monotone := fun _ _ hx hxy => by
    simpa only [one_mul] using hc.monotone hx (hx.trans hxy) hxy }

private theorem general_uniform_arrival_upper {M : MCTSModel} {c : ℝ → ℝ}
    (hseq : M.Scheduled c) (hc : Assumption.CountExplorationSchedule c)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency) :
    ∃ C : ℝ, 0 < C ∧ ∀ s t, hc.threshold ≤ M.parentVisit s t →
      (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ≤
        C * ExplorationSchedule.mass c (M.parentVisit s t) := by
  have hlocal_suboptimal_upper {M : MCTSModel} {c : ℝ → ℝ} {ε : ℝ}
      (hseq : M.Scheduled c) (hc : Assumption.CountExplorationSchedule c)
      (s : M.State) (a : M.Action s) (m₀ : ℕ)
      (hm₀ : hc.threshold ≤ m₀) (hgap : 0 < M.Gap s a - 2 * ε)
      (hv : ∀ t, m₀ ≤ M.parentVisit s t →
        |M.searchValue s a t - M.value s a| ≤ ε ∧
        |M.searchValue s (M.isBest s) t - M.value s (M.isBest s)| ≤ ε) :
      ∀ t, (M.childVisit s a t : ℝ) ≤ max (m₀ : ℝ)
        (M.prior s a / (M.Gap s a - 2 * ε) * hc.A *
          ExplorationSchedule.mass c (M.parentVisit s t)) := by
    intro t
    by_cases hz : M.childVisit s a t = 0
    · rw [hz, Nat.cast_zero]
      exact (Nat.cast_nonneg m₀).trans (le_max_left _ _)
    let u := hseq.toCountUpdates.lastSelection s a t
    obtain ⟨hut, hsel, hcount⟩ :=
      hseq.toCountUpdates.lastSelection_spec s a t (Nat.pos_of_ne_zero hz)
    change u < t at hut
    change M.selectedAt s a u at hsel
    change M.childVisit s a t = M.childVisit s a u + 1 at hcount
    by_cases hm : m₀ ≤ M.parentVisit s u
    · obtain ⟨hi, hstar⟩ := hv u hm
      have hs := hseq.argmax s a u hsel (M.isBest s)
      simp only [MCTSModel.puctScore, mul_assoc] at hs
      rw [mul_left_comm (c _) (M.prior s (M.isBest s)), mul_left_comm (c _) (M.prior s a),
        ← ExplorationSchedule.mass] at hs
      have hb : 0 ≤ M.prior s (M.isBest s) *
          ExplorationSchedule.mass c (M.parentVisit s u) /
            (1 + (M.childVisit s (M.isBest s) u : ℝ)) := by
        have := M.prior_nonneg s (M.isBest s)
        have hF : 0 ≤ ExplorationSchedule.mass c (M.parentVisit s u) :=
          mul_nonneg (hc.positive _ (by
            exact_mod_cast hc.threshold_pos.trans (hm₀.trans hm))).le (Real.sqrt_nonneg _)
        positivity
      have hcompare : M.searchValue s (M.isBest s) u ≤ M.searchValue s a u +
          M.prior s a * ExplorationSchedule.mass c (M.parentVisit s u) /
            (1 + (M.childVisit s a u : ℝ)) := by linarith
      have hbonus : M.Gap s a - 2 * ε ≤
          M.prior s a * ExplorationSchedule.mass c (M.parentVisit s u) /
            (1 + (M.childVisit s a u : ℝ)) := by
        dsimp [MCTSModel.Gap]
        linarith [(abs_le.mp hi).2, (abs_le.mp hstar).1]
      have hupper : (M.childVisit s a u : ℝ) ≤
          M.prior s a * ExplorationSchedule.mass c (M.parentVisit s u) /
            (M.Gap s a - 2 * ε) - 1 := by
        have hmul := (le_div_iff₀ (by positivity : 0 < 1 + (M.childVisit s a u : ℝ))).1 hbonus
        apply (le_sub_iff_add_le).2
        apply (le_div_iff₀ hgap).2
        nlinarith
      have hmono := hc.monotone _ _
        (show (hc.threshold : ℝ) ≤ M.parentVisit s u by exact_mod_cast hm₀.trans hm)
        (show (M.parentVisit s u : ℝ) ≤ M.parentVisit s t by
          exact_mod_cast hseq.toCountUpdates.parent_monotone s hut.le)
      have hcoef : 0 ≤ M.prior s a / (M.Gap s a - 2 * ε) :=
        div_nonneg (M.prior_nonneg s a) hgap.le
      have hmul := mul_le_mul_of_nonneg_left hmono hcoef
      have hcnt : (M.childVisit s a t : ℝ) = (M.childVisit s a u : ℝ) + 1 := by
        exact_mod_cast hcount
      apply le_trans _ (le_max_right _ _)
      dsimp [MCTSModel.Gap] at *
      rw [← div_mul_eq_mul_div] at hupper
      linarith
    · have hle := hseq.child_le_parent s a u
      have hn : M.childVisit s a t ≤ m₀ := by omega
      exact (show (M.childVisit s a t : ℝ) ≤ m₀ by exact_mod_cast hn).trans (le_max_left _ _)
  have hlocal_uniform_upper {M : MCTSModel} {c : ℝ → ℝ}
      (hseq : M.Scheduled c) (hc : Assumption.CountExplorationSchedule c)
      (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency) :
      ∃ K A : ℝ, 0 ≤ K ∧ 0 < A ∧ ∀ s a t, M.Suboptimal s a →
        (M.childVisit s a t : ℝ) ≤ K + A * ExplorationSchedule.mass c (M.parentVisit s t) := by
    obtain ⟨Δ, hΔ, hg⟩ := hreg.gap_lower
    obtain ⟨mv, hv⟩ := hu (Δ / 4) (by positivity)
    let m := max mv hc.threshold
    have hApos : 0 < hc.A := lt_of_lt_of_le zero_lt_one hc.A_one
    refine ⟨m, 2 / Δ * hc.A, by positivity, by positivity, ?_⟩
    intro s a t ha
    letI : Finite (M.Action s) := (hreg.finite_branching.choose_spec.2 s).1
    have hgap : 0 < M.Gap s a - 2 * (Δ / 4) := by have := hg s a ha; linarith
    have hb := hlocal_suboptimal_upper hseq hc s a m (le_max_right _ _) hgap
      (fun t ht => ⟨hv s a t ((le_max_left _ _).trans ht),
        hv s (M.isBest s) t ((le_max_left _ _).trans ht)⟩) t
    have hp : M.prior s a ≤ 1 :=
      (Summable.of_finite.le_tsum a (fun b _ => M.prior_nonneg s b)).trans_eq
        (M.prior_sum s)
    have hcoef : M.prior s a / (M.Gap s a - 2 * (Δ / 4)) ≤ 2 / Δ := by
      apply (div_le_div_iff₀ hgap hΔ).2
      have := hg s a ha
      nlinarith
    have hF : 0 ≤ ExplorationSchedule.mass c (M.parentVisit s t) := by
      by_cases hm : M.parentVisit s t = 0
      · simp [hm, ExplorationSchedule.mass]
      · exact mul_nonneg (hc.positive _ (by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm)).le (Real.sqrt_nonneg _)
    have hcoefA := mul_le_mul_of_nonneg_right hcoef hApos.le
    have hm := mul_le_mul_of_nonneg_right hcoefA hF
    apply hb.trans
    have hprod : 0 ≤ (2 / Δ * hc.A) * ExplorationSchedule.mass c (M.parentVisit s t) := by
      positivity
    apply max_le <;> linarith [Nat.cast_nonneg m (α := ℝ)]
  obtain ⟨K, A, hK, hA, hb⟩ := hlocal_uniform_upper hseq hc hreg hu
  obtain ⟨b, hbpos, hf⟩ := hreg.finite_branching
  have hApos : 0 < hc.A := lt_of_lt_of_le zero_lt_one hc.A_one
  let δ := ExplorationSchedule.mass c hc.threshold / hc.A
  have hδ : 0 < δ := div_pos
    (mul_pos (hc.positive _ (by exact_mod_cast hc.threshold_pos))
      (Real.sqrt_pos.2 (by exact_mod_cast (Nat.zero_lt_of_lt hc.threshold_pos)))) hApos
  refine ⟨((b : ℝ) * K + 1) / δ + (b : ℝ) * A, by positivity, ?_⟩
  intro s t hm
  letI : Finite (M.Action s) := (hf s).1
  have hδF : δ ≤ ExplorationSchedule.mass c (M.parentVisit s t) := by
    apply (div_le_iff₀ hApos).2
    simpa only [mul_comm] using hc.monotone _ _ (le_refl _) (by exact_mod_cast hm)
  have hF := hδ.le.trans hδF
  have hg := count_gap_sum_le hseq.toCountUpdates s t b (hf s).2
    (show 0 ≤ K + A * ExplorationSchedule.mass c (M.parentVisit s t) by positivity)
    (fun a ha => hb s a t ha)
  have hmul := mul_le_mul_of_nonneg_left hδF
    (show 0 ≤ ((b : ℝ) * K + 1) / δ by positivity)
  rw [div_mul_cancel₀ _ hδ.ne'] at hmul
  simp only [MCTSModel.arrivalCount, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- A count path with bounded positive integral increments. -/
private structure Assumption.GeneralIntegralCountPath (N : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (c : ℝ → ℝ) where
  threshold : ℕ
  threshold_ge : 2 ≤ threshold
  κ : ℝ
  C : ℝ
  θ : ℝ
  κ_pos : 0 < κ
  C_pos : 0 < C
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  integrable : IntegrableFromOne (fun x => 1 / (c x * Real.sqrt x))
  positive : ∀ x ≥ 1, 0 < c x
  paths : ∀ᶠ n : ℕ in atTop, CountPath (N n) (H n) n
  retention : ∀ᶠ n : ℕ in atTop, ∀ x < H n, threshold ≤ N n x →
    θ * (N n x : ℝ) ≤ (N n (x + 1) : ℝ)
  steps : ∀ᶠ n : ℕ in atTop, ∀ x < H n, threshold ≤ N n x →
    κ ≤ ∫ y in (N n (x + 1) : ℝ)..(N n x : ℝ), 1 / (c y * Real.sqrt y) ∧
    (∫ y in (N n (x + 1) : ℝ)..(N n x : ℝ), 1 / (c y * Real.sqrt y)) ≤ C

private theorem general_reciprocal_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (1 / a + 1 / b) / 2 ≤ 1 / min a b ∧ 1 / min a b ≤ 1 / a + 1 / b := by
  by_cases h : a ≤ b
  · rw [min_eq_left h]
    have hh := one_div_le_one_div_of_le ha h
    constructor <;> linarith [one_div_pos.mpr ha, one_div_pos.mpr hb]
  · rw [min_eq_right (le_of_not_ge h)]
    have hh := one_div_le_one_div_of_le hb (le_of_not_ge h)
    constructor <;> linarith [one_div_pos.mpr ha, one_div_pos.mpr hb]

private theorem scheduled_selected_optimal_gap_lower {M : MCTSModel} {c : ℝ → ℝ}
    (hseq : M.Scheduled c) (hc : ∀ x ≥ 1, 0 < c x)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s)) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ q : ℕ, ∀ s t,
      ¬ M.isTerminal s → q ≤ M.parentVisit s t →
      M.selectedAt s (M.isBest s) t →
      κ * min (ExplorationSchedule.mass c (M.parentVisit s t)) (M.parentVisit s t : ℝ) ≤
        (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t := by
  have selected_score_lower {F m A θ p z : ℝ}
      (hF : 0 < F) (hm : 0 < m) (hA : 0 < A)
      (hθ : 0 < θ) (hz : 0 ≤ z)
      (hb : p * F ≤ (A + F / (θ * m)) * z) :
      p / (A + 1 / θ) * min F m ≤ z := by
    have hD : 0 < A + 1 / θ := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hD).2
    by_cases hFm : F ≤ m
    · rw [min_eq_left hFm]
      have hfrac : F / (θ * m) ≤ 1 / θ := by
        apply (div_le_div_iff₀ (by positivity) hθ).2
        nlinarith
      have hh := mul_le_mul_of_nonneg_right hfrac hz
      nlinarith
    · rw [min_eq_right (le_of_not_ge hFm)]
      have hratio : 1 ≤ F / m := (one_le_div hm).2 (le_of_not_ge hFm)
      have ha := mul_le_mul_of_nonneg_left hratio hA.le
      have heq : (A + 1 / θ) * (F / m) = A * (F / m) + F / (θ * m) := by field_simp
      have hh : p * F ≤ ((A + 1 / θ) * (F / m)) * z := by
        rw [heq]; nlinarith [mul_le_mul_of_nonneg_right ha hz]
      have hh' := mul_le_mul_of_nonneg_right hh hm.le
      have heq' : (A + 1 / θ) * (F / m) * z * m = (A + 1 / θ) * z * F := by field_simp
      rw [heq'] at hh'
      nlinarith
  have suboptimal_child_le_arrival_gap {M : MCTSModel}
      (h : M.CountUpdates) (s : M.State) [Finite (M.Action s)]
      (a : M.Action s) (ha : M.Suboptimal s a) (t : ℕ) :
      (M.childVisit s a t : ℝ) + 1 ≤
        (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t := by
    classical
    letI := Fintype.ofFinite (M.Action s)
    have hsum := h.count_identity s t
    have he := Finset.sum_erase_add (Finset.univ : Finset (M.Action s))
      (fun b => M.childVisit s b t) (Finset.mem_univ (M.isBest s))
    have hlo := Finset.single_le_sum (fun b _ => Nat.zero_le (M.childVisit s b t))
      (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩)
    rw [← he] at hsum
    dsimp only at hsum
    have hn : M.childVisit s a t + M.childVisit s (M.isBest s) t ≤ M.parentVisit s t := by omega
    have hr : (M.childVisit s a t : ℝ) + M.childVisit s (M.isBest s) t ≤ M.parentVisit s t := by
      exact_mod_cast hn
    simp only [MCTSModel.arrivalCount, Nat.cast_add, Nat.cast_one]
    linarith
  obtain ⟨θ, hθ, _, mr, hshare⟩ :=
    scheduled_optimal_share_of_prior hseq hc hreg hu hopt
  obtain ⟨mv, hv⟩ := hu 1 zero_lt_one
  obtain ⟨Δmax, hΔmax, hgap⟩ := hreg.gap_upper
  obtain ⟨p₀, hp₀, hp⟩ := hreg.suboptimal_prior
  refine ⟨p₀ / (Δmax + 2 + 1 / θ), by positivity, max 1 (max mr mv), ?_⟩
  intro s t hnt ht hsel
  have hm1 : 1 ≤ M.parentVisit s t := (le_max_left _ _).trans ht
  have hmr : mr ≤ M.parentVisit s t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hmv : mv ≤ M.parentVisit s t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  letI : Finite (M.Action s) := (hreg.finite_branching.choose_spec.2 s).1
  letI := Fintype.ofFinite (M.Action s)
  have hPstar : M.prior s (M.isBest s) ≤ 1 :=
    (Summable.of_finite.le_tsum (M.isBest s) (fun b _ => M.prior_nonneg s b)).trans_eq
      (M.prior_sum s)
  have hmPos : 0 < (M.parentVisit s t : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hm1
  have hF : 0 < ExplorationSchedule.mass c (M.parentVisit s t) :=
    mul_pos (hc _ (by exact_mod_cast hm1)) (Real.sqrt_pos.2 hmPos)
  have hbonus : M.prior s (M.isBest s) * ExplorationSchedule.mass c (M.parentVisit s t) /
      (1 + (M.childVisit s (M.isBest s) t : ℝ)) ≤
      ExplorationSchedule.mass c (M.parentVisit s t) / (θ * M.parentVisit s t) := by
    have hr := hshare s t hnt hmr
    have hmass := mul_le_of_le_one_left hF.le hPstar
    apply (div_le_div_iff₀ (by positivity) (mul_pos hθ hmPos)).2
    have h1 := mul_le_mul_of_nonneg_right hmass (mul_pos hθ hmPos).le
    have h2 := mul_le_mul_of_nonneg_left hr hF.le
    nlinarith
  obtain ⟨a, ha, hpa⟩ := hp s hnt
  have hs := hseq.argmax s (M.isBest s) t hsel a
  simp only [MCTSModel.puctScore, mul_assoc] at hs
  rw [mul_left_comm (c _) (M.prior s (M.isBest s)), mul_left_comm (c _) (M.prior s a),
    ← ExplorationSchedule.mass] at hs
  have hb : M.prior s a * ExplorationSchedule.mass c (M.parentVisit s t) /
      (1 + (M.childVisit s a t : ℝ)) ≤
      Δmax + 2 + ExplorationSchedule.mass c (M.parentVisit s t) / (θ * M.parentVisit s t) := by
    have hi := abs_le.mp (hv s a t hmv)
    have ho := abs_le.mp (hv s (M.isBest s) t hmv)
    have hg := hgap s a ha
    dsimp [MCTSModel.Gap] at hg
    linarith
  have hproduct := (div_le_iff₀ (by positivity : 0 < 1 + (M.childVisit s a t : ℝ))).1 hb
  have hplower := mul_le_mul_of_nonneg_right hpa hF.le
  have hlocal := selected_score_lower hF hmPos
    (show 0 < Δmax + 2 by positivity) hθ
    (show 0 ≤ 1 + (M.childVisit s a t : ℝ) by positivity) (hplower.trans hproduct)
  have hgapCount := suboptimal_child_le_arrival_gap hseq.toCountUpdates s a ha t
  linarith

private theorem scheduled_depth_capped_of_optimal_share {M : MCTSModel}
    (hshare_data : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ m₀ : ℕ, ∀ s t,
      ¬ M.isTerminal s → m₀ ≤ M.parentVisit s t →
      θ * (M.parentVisit s t : ℝ) ≤ M.childVisit s (M.isBest s) t)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (L : ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.CappedOptimalPathCounts (V n) (H n) (n + 1) L (state n) (time n)) :
    ∀ᶠ n : ℕ in atTop, H n = L := by
  obtain ⟨θ, hθ, hθ1, m₀, hshare⟩ := hshare_data
  obtain ⟨B, hfrontier⟩ := frontier_bound_of_optimal_share hθ hshare
  let η := θ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by dsimp [η]; linarith
  have hpowers : Antitone (fun k : ℕ => η ^ k) := by
    apply antitone_nat_of_succ_le
    intro k
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hη.le _) hη1
  have hlarge : ∀ᶠ n : ℕ in atTop,
      ((max (m₀ + 2) B : ℕ) : ℝ) / η ^ L < ((n + 1 : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
      (eventually_gt_atTop _)
  filter_upwards [hpath, hlarge] with n hn hlarge
  have hroot := (div_lt_iff₀ (pow_pos hη L)).1 hlarge
  have hpref : ∀ k ≤ H n, η ^ k * ((n + 1 : ℕ) : ℝ) ≤ V n k := by
    intro k
    induction k with
    | zero => intro _; simp [hn.1]
    | succ k ih =>
      intro hk
      have hkH : k < H n := Nat.lt_of_succ_le hk
      have hprev := ih hkH.le
      have hscale := mul_le_mul_of_nonneg_right (hpowers (hkH.le.trans hn.2.1))
        (Nat.cast_nonneg (n + 1) (α := ℝ))
      have hmin : max (m₀ + 2) B ≤ V n k := by
        exact_mod_cast (show ((max (m₀ + 2) B : ℕ) : ℝ) ≤ V n k by linarith)
      obtain ⟨hnt, hv, hv'⟩ := hn.2.2.2 k hkH
      have hp : m₀ ≤ M.parentVisit (state n k) (time n k) := by
        simp only [MCTSModel.arrivalCount] at hv
        omega
      have hs := hshare _ _ hnt hp
      rw [← hv'] at hs
      have hvreal : (V n k : ℝ) = (M.parentVisit (state n k) (time n k) : ℝ) + 1 := by
        rw [hv]
        simp [MCTSModel.arrivalCount]
      have hp1 : (1 : ℝ) ≤ M.parentVisit (state n k) (time n k) := by
        have : 1 ≤ M.parentVisit (state n k) (time n k) := by
          simp only [MCTSModel.arrivalCount] at hv
          omega
        exact_mod_cast this
      have hstep : η * (V n k : ℝ) ≤ V n (k + 1) := by
        dsimp [η]
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hprev hη.le
      rw [pow_succ]
      nlinarith
  by_contra hnot
  obtain ⟨hv, hnt, hz⟩ := hn.2.2.1 (lt_of_le_of_ne hn.2.1 hnot)
  have hend : (V n (H n) : ℝ) ≤ B := by
    rw [hv]
    exact_mod_cast hfrontier _ _ hnt hz
  have hlast := hpref (H n) le_rfl
  have hscale := mul_le_mul_of_nonneg_right (hpowers hn.2.1)
    (Nat.cast_nonneg (n + 1) (α := ℝ))
  have hB : (B : ℝ) ≤ (max (m₀ + 2) B : ℕ) := by exact_mod_cast le_max_right _ _
  linarith

set_option maxHeartbeats 1600000 in
-- Local subproofs share one elaboration budget.
/-- Integral depth estimate under eventually nondecreasing exploration mass. -/
private theorem scheduled_puct_depth {M : MCTSModel} {c : ℝ → ℝ}
    (hseq : M.Scheduled c) (hc : Assumption.ExplorationSchedule c)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s))
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.OptimalPathCounts (V n) (H n) (n + 1) (state n) (time n)) :
    (fun n => (H n : ℝ)) =Θ[∞] DepthIntegral.saturated c := by
  let shiftedMass (c : ℝ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
    min (ExplorationSchedule.mass c (max (q : ℝ) (x - 2))) (max (q : ℝ) (x - 2))
  have shiftedMass_properties {c : ℝ → ℝ} (hc : Assumption.ExplorationSchedule c)
      {q : ℕ} (hq : hc.threshold ≤ q) :
      Continuous (shiftedMass c q) ∧
      (∀ x, 0 < shiftedMass c q x) ∧
      Monotone (shiftedMass c q) ∧
      (∀ x, (q : ℝ) + 2 ≤ x → shiftedMass c q x ≤ x) := by
    let k : ℝ → ℝ := fun x => max (q : ℝ) (x - 2)
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hc.threshold_pos.trans hq
    have hk : Continuous k := continuous_const.max (continuous_id.sub continuous_const)
    have hk1 : ∀ x, 1 ≤ k x := fun x => hq1.trans (le_max_left _ _)
    have hmass : Continuous (fun x => ExplorationSchedule.mass c (k x)) := by
      apply (hc.continuous.comp_continuous hk hk1).mul
      exact Real.continuous_sqrt.comp hk
    refine ⟨hmass.min hk, ?_, ?_, ?_⟩
    · intro x
      apply lt_min
      · exact mul_pos (hc.positive _ (hk1 x)) (Real.sqrt_pos.2 (by linarith [hk1 x]))
      · exact lt_of_lt_of_le zero_lt_one (hk1 x)
    · intro x y hxy
      have hkxy : k x ≤ k y := max_le_max_left _ (sub_le_sub_right hxy _)
      apply min_le_min
      · exact hc.monotone (by exact
          (show (hc.threshold : ℝ) ≤ q by exact_mod_cast hq).trans (le_max_left _ _))
          (by exact
          (show (hc.threshold : ℝ) ≤ q by exact_mod_cast hq).trans (le_max_left _ _)) hkxy
      · exact hkxy
    · intro x hx
      apply (min_le_right _ _).trans
      exact max_le (by linarith) (by linarith)
  have scheduled_shifted_integral_lower
      (q : ℕ) (hq : hc.threshold ≤ q) :
      ∃ κ : ℝ, 0 < κ ∧ ∃ T : ℕ, ∀ s t,
        ¬ M.isTerminal s → T ≤ M.arrivalCount s t →
        κ ≤ ∫ y in (M.childVisit s (M.isBest s) t : ℝ)..(M.arrivalCount s t : ℝ),
          1 / shiftedMass c q y := by
    obtain ⟨κ, hκ, ql, hlower⟩ :=
      scheduled_selected_optimal_gap_lower hseq hc.positive hreg hu hopt
    obtain ⟨θ, hθ, _, mr, hshare⟩ :=
      scheduled_optimal_share_of_prior hseq hc.positive hreg hu hopt
    let K := max q ql
    obtain ⟨R, hR⟩ := exists_nat_ge (((K : ℝ) + 1) / θ)
    refine ⟨κ, hκ, max mr R + 1, ?_⟩
    intro s t hnt ht
    have hm : max mr R ≤ M.parentVisit s t := by
      simp only [MCTSModel.arrivalCount] at ht
      omega
    have hshare_t := hshare s t hnt ((le_max_left _ _).trans hm)
    have hRcount : (R : ℝ) ≤ M.parentVisit s t := by
      exact_mod_cast (le_max_right mr R).trans hm
    have hbig : (K : ℝ) + 1 ≤ M.childVisit s (M.isBest s) t := by
      have hh := (div_le_iff₀ hθ).1 (hR.trans hRcount)
      nlinarith
    have hstar : 0 < M.childVisit s (M.isBest s) t := by
      have : (0 : ℝ) < M.childVisit s (M.isBest s) t := by
        linarith [Nat.cast_nonneg (α := ℝ) K]
      exact_mod_cast this
    let u := hseq.toCountUpdates.lastSelection s (M.isBest s) t
    obtain ⟨hut, hsel, hcount⟩ := hseq.toCountUpdates.lastSelection_spec s (M.isBest s) t hstar
    change u < t at hut
    change M.selectedAt s (M.isBest s) u at hsel
    change M.childVisit s (M.isBest s) t = M.childVisit s (M.isBest s) u + 1 at hcount
    have hKu : K ≤ M.parentVisit s u := by
      have hle := hseq.child_le_parent s (M.isBest s) u
      have hcountR : (M.childVisit s (M.isBest s) t : ℝ) =
          M.childVisit s (M.isBest s) u + 1 := by exact_mod_cast hcount
      have hleR : (M.childVisit s (M.isBest s) u : ℝ) ≤ M.parentVisit s u := by exact_mod_cast hle
      have : (K : ℝ) ≤ M.parentVisit s u := by linarith
      exact_mod_cast this
    have hqu : q ≤ M.parentVisit s u := (le_max_left _ _).trans hKu
    have hqlu : ql ≤ M.parentVisit s u := (le_max_right _ _).trans hKu
    have hlow := hlower s u hnt hqlu hsel
    let g := min (ExplorationSchedule.mass c (M.parentVisit s u)) (M.parentVisit s u : ℝ)
    have hu1 : 1 ≤ M.parentVisit s u := hc.threshold_pos.trans (hq.trans hqu)
    have hu1R : (1 : ℝ) ≤ M.parentVisit s u := by exact_mod_cast hu1
    have hgpos : 0 < g := lt_min
      (mul_pos (hc.positive _ hu1R) (Real.sqrt_pos.2 (by linarith))) (by linarith)
    let a : ℝ := M.childVisit s (M.isBest s) t
    let b : ℝ := M.arrivalCount s t
    let z : ℝ := (M.parentVisit s u : ℝ) + 2
    have haz : a ≤ z := by
      have hh := hseq.child_le_parent s (M.isBest s) u
      have hnat : M.childVisit s (M.isBest s) t ≤ M.parentVisit s u + 2 := by omega
      dsimp [a, z]
      exact_mod_cast hnat
    have hzb : z ≤ b := by
      have hstep := hseq.parent_selected s (M.isBest s) u hsel
      have hmono := hseq.toCountUpdates.parent_monotone s (show u + 1 ≤ t by omega)
      have hnat : M.parentVisit s u + 2 ≤ M.arrivalCount s t := by
        simp only [MCTSModel.arrivalCount]
        omega
      dsimp [z, b]
      exact_mod_cast hnat
    obtain ⟨hfc, hfp, _, _⟩ := shiftedMass_properties hc hq
    have hic : Continuous (fun y => 1 / shiftedMass c q y) :=
      continuous_const.div hfc (fun y => (hfp y).ne')
    have hfupper : ∀ y ∈ Set.Icc a z, shiftedMass c q y ≤ g := by
      intro y hy
      have harg : max (q : ℝ) (y - 2) ≤ M.parentVisit s u := by
        apply max_le
        · exact_mod_cast hqu
        · dsimp [z] at hy
          linarith [hy.2]
      have harg0 : (hc.threshold : ℝ) ≤ max (q : ℝ) (y - 2) :=
        (show (hc.threshold : ℝ) ≤ q by exact_mod_cast hq).trans (le_max_left _ _)
      exact min_le_min (hc.monotone harg0 (harg0.trans harg) harg) harg
    have hrect : (z - a) / g ≤ ∫ y in a..z, 1 / shiftedMass c q y := by
      have hh := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) haz
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / g) volume a z)
        (hic.intervalIntegrable a z) (fun y hy => one_div_le_one_div_of_le (hfp y) (hfupper y hy))
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] using hh
    have hkl : κ ≤ (z - a) / g := by
      apply (le_div_iff₀ hgpos).2
      dsimp [MCTSModel.arrivalCount] at hlow
      push_cast at hlow
      have hcountR : a = (M.childVisit s (M.isBest s) u : ℝ) + 1 := by
        dsimp [a]
        exact_mod_cast hcount
      dsimp [g] at *
      dsimp [z]
      linarith
    have hmono := intervalIntegral.integral_mono_interval (μ := volume) (le_refl a) haz hzb
      (Filter.Eventually.of_forall (fun y => (one_div_pos.mpr (hfp y)).le))
      (hic.intervalIntegrable a b)
    exact hkl.trans (hrect.trans hmono)
  have scheduled_optimal_edge_integral_upper
      {q : ℕ} (hq : hc.threshold ≤ q) {C : ℝ} (hC : 0 < C)
      (hupper : ∀ s t, q ≤ M.parentVisit s t →
        (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ≤
          C * ExplorationSchedule.mass c (M.parentVisit s t)) :
      ∃ B : ℝ, 0 < B ∧ ∀ s t,
        (q : ℝ) + 2 ≤ M.childVisit s (M.isBest s) t →
        (∫ y in (M.childVisit s (M.isBest s) t : ℝ)..(M.arrivalCount s t : ℝ),
          1 / shiftedMass c q y) ≤
          B * (1 + Real.log (shiftedMass c q (M.arrivalCount s t) /
            shiftedMass c q (M.childVisit s (M.isBest s) t))) := by
    have parent_count_attained (h : M.CountUpdates)
        (s : M.State) (t k : ℕ) (hk : k ≤ M.parentVisit s t) :
        ∃ j ≤ t, M.parentVisit s j = k := by
      classical
      induction t with
      | zero =>
        have hk0 : k = 0 := by simpa [h.parent_initial] using hk
        exact ⟨0, le_rfl, by simp [h.parent_initial, hk0]⟩
      | succ t ih =>
        by_cases hkt : k ≤ M.parentVisit s t
        · obtain ⟨j, hj, he⟩ := ih hkt
          exact ⟨j, Nat.le_trans hj (Nat.le_succ _), he⟩
        · refine ⟨t + 1, le_rfl, ?_⟩
          by_cases hsel : ∃ a, M.selectedAt s a t
          · obtain ⟨a, ha⟩ := hsel
            have hp := h.parent_selected s a t ha
            omega
          · have hnone : ∀ a, ¬ M.selectedAt s a t := by simpa using hsel
            have hp := h.parent_idle s t hnone
            omega
    have monotone_interval_reciprocal_bound
        {f : ℝ → ℝ} {v m B : ℝ}
        (hvm : v ≤ m) (hB : 0 < B)
        (hf : ContinuousOn f (Set.Icc v m))
        (hpos : ∀ y ∈ Set.Icc v m, 0 < f y)
        (hmono : MonotoneOn f (Set.Icc v m))
        (hhistory : ∀ y ∈ Set.Icc v m, y - v ≤ B * f y) :
        (∫ y in v..m, 1 / f y) ≤ B * (1 + Real.log (f m / f v)) := by
      have hv : v ∈ Set.Icc v m := ⟨le_rfl, hvm⟩
      have hm : m ∈ Set.Icc v m := ⟨hvm, le_rfl⟩
      have hfv : 0 < f v := hpos v hv
      have hfm : 0 < f m := hpos m hm
      have hinv : ContinuousOn (fun y => 1 / f y) (Set.Icc v m) :=
        continuousOn_const.div hf (fun y hy => (hpos y hy).ne')
      have hlog : 0 ≤ Real.log (f m / f v) :=
        Real.log_nonneg ((le_div_iff₀ hfv).2 (by simpa using hmono hv hm hvm))
      have hfirst : ∀ z ∈ Set.Icc v m,
          (∫ y in v..z, 1 / f y) ≤ (z - v) / f v := by
        intro z hz
        have hcont := hinv.mono (show Set.Icc v z ⊆ Set.Icc v m from
          fun y hy => ⟨hy.1, hy.2.trans hz.2⟩)
        have hcmp := intervalIntegral.integral_mono_on (μ := volume) hz.1
          (hcont.intervalIntegrable_of_Icc hz.1)
          (continuous_const.intervalIntegrable v z : IntervalIntegrable
            (fun _ : ℝ => 1 / f v) volume v z)
          (fun y hy => one_div_le_one_div_of_le hfv
            (hmono hv ⟨hy.1, hy.2.trans hz.2⟩ hy.1))
        simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] using hcmp
      by_cases hshort : m - v ≤ B * f v
      · have hsmall : (m - v) / f v ≤ B := (div_le_iff₀ hfv).2 hshort
        have hlarge : B ≤ B * (1 + Real.log (f m / f v)) := by nlinarith
        exact (hfirst m hm).trans (hsmall.trans hlarge)
      · let z := v + B * f v
        have hvz : v < z := by dsimp [z]; nlinarith [mul_pos hB hfv]
        have hzm : z < m := by dsimp [z]; linarith
        have hz : z ∈ Set.Icc v m := ⟨hvz.le, hzm.le⟩
        have hzv : z - v = B * f v := by dsimp [z]; ring
        have hfirstB : (∫ y in v..z, 1 / f y) ≤ B := by
          simpa [hzv, hfv.ne'] using hfirst z hz
        have hsecond_cont : ContinuousOn (fun y : ℝ => B * (1 / (y - v)))
            (Set.Icc z m) := by
          apply ContinuousOn.const_mul
          apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
          intro y hy
          dsimp
          linarith [hy.1]
        have hsecond : (∫ y in z..m, 1 / f y) ≤
            B * Real.log ((m - v) / (B * f v)) := by
          have hcont := hinv.mono (show Set.Icc z m ⊆ Set.Icc v m from
            fun y hy => ⟨hvz.le.trans hy.1, hy.2⟩)
          have hcmp := intervalIntegral.integral_mono_on (μ := volume) hzm.le
            (hcont.intervalIntegrable_of_Icc hzm.le)
            (hsecond_cont.intervalIntegrable_of_Icc hzm.le) (fun y hy => by
              have hyv : 0 < y - v := by linarith [hy.1]
              have hyp : 0 < f y := hpos y ⟨hvz.le.trans hy.1, hy.2⟩
              rw [mul_one_div]
              apply (div_le_div_iff₀ hyp hyv).2
              simpa only [one_mul] using hhistory y ⟨hvz.le.trans hy.1, hy.2⟩)
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_comp_sub_right,
            integral_one_div_of_pos (by linarith : 0 < z - v) (by linarith : 0 < m - v),
            hzv] at hcmp
          exact hcmp
        have hlogcmp : Real.log ((m - v) / (B * f v)) ≤ Real.log (f m / f v) := by
          apply Real.log_le_log (div_pos (by linarith) (mul_pos hB hfv))
          apply (div_le_div_iff₀ (mul_pos hB hfv) hfv).2
          have hlast := hhistory m hm
          nlinarith
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          (μ := volume)
          ((hinv.mono (show Set.Icc v z ⊆ Set.Icc v m from
            fun y hy => ⟨hy.1, hy.2.trans hzm.le⟩)).intervalIntegrable_of_Icc hvz.le)
          ((hinv.mono (show Set.Icc z m ⊆ Set.Icc v m from
            fun y hy => ⟨hvz.le.trans hy.1, hy.2⟩)).intervalIntegrable_of_Icc hzm.le)
        have hscale := mul_le_mul_of_nonneg_left hlogcmp hB.le
        linarith
    let f := shiftedMass c q
    let δ := min (ExplorationSchedule.mass c (q : ℝ)) (q : ℝ)
    have hq1 : 1 ≤ q := hc.threshold_pos.trans hq
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq1
    have hδ : 0 < δ := lt_min
      (mul_pos (hc.positive _ (by exact_mod_cast hq1)) (Real.sqrt_pos.2 hqpos)) hqpos
    obtain ⟨hf, hfp, hfm, _⟩ := shiftedMass_properties hc hq
    have hδf : ∀ y, δ ≤ f y := by
      intro y
      dsimp [δ, f, shiftedMass]
      exact min_le_min
        (hc.monotone (show (hc.threshold : ℝ) ≤ q by exact_mod_cast hq)
          ((show (hc.threshold : ℝ) ≤ q by exact_mod_cast hq).trans (le_max_left _ _))
          (le_max_left _ _)) (le_max_left _ _)
    let A := max C 2
    have hA : 0 < A := hC.trans_le (le_max_left _ _)
    let B := A + 2 / δ
    have hB : 0 < B := by positivity
    refine ⟨B, hB, ?_⟩
    intro s t ha
    let a : ℝ := M.childVisit s (M.isBest s) t
    let b : ℝ := M.arrivalCount s t
    have hab : a ≤ b := by
      have hc := hseq.child_le_parent s (M.isBest s) t
      dsimp [a, b, MCTSModel.arrivalCount]
      exact_mod_cast hc.trans (Nat.le_succ _)
    apply monotone_interval_reciprocal_bound hab hB hf.continuousOn
      (fun y _ => hfp y) (hfm.monotoneOn _)
    intro y hy
    have hqy : (q : ℝ) ≤ y - 2 := by dsimp [a] at hy; linarith [hy.1]
    have hy2 : 0 ≤ y - 2 := hqpos.le.trans hqy
    let k : ℕ := ⌊y - 2⌋₊
    have hqk : q ≤ k := Nat.le_floor hqy
    have hkle : (k : ℝ) ≤ y - 2 := Nat.floor_le hy2
    have hyk : y - 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one (y - 2)
    have hkm : k ≤ M.parentVisit s t := by
      have hbm : b = (M.parentVisit s t : ℝ) + 1 := by
        simp [b, MCTSModel.arrivalCount]
      have hk : (k : ℝ) ≤ M.parentVisit s t := by linarith [hy.2]
      exact_mod_cast hk
    obtain ⟨j, hjt, hjk⟩ := parent_count_attained hseq.toCountUpdates s t k hkm
    have hchild : (M.childVisit s (M.isBest s) j : ℝ) ≤ a := by
      dsimp [a]
      exact_mod_cast hseq.toCountUpdates.child_monotone s (M.isBest s) hjt
    have hgapF := hupper s j (hjk.symm ▸ hqk)
    have hgap2 : (M.arrivalCount s j : ℝ) - M.childVisit s (M.isBest s) j ≤
        2 * (k : ℝ) := by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hq1.trans hqk
      simp only [MCTSModel.arrivalCount, hjk, Nat.cast_add, Nat.cast_one]
      nlinarith [Nat.cast_nonneg (M.childVisit s (M.isBest s) j) (α := ℝ)]
    have hgap : (M.arrivalCount s j : ℝ) - M.childVisit s (M.isBest s) j ≤
        A * min (ExplorationSchedule.mass c (k : ℝ)) (k : ℝ) := by
      rw [hjk] at hgapF
      have hF : 0 ≤ ExplorationSchedule.mass c (k : ℝ) := by
        exact mul_nonneg (hc.positive _ (by exact_mod_cast hq1.trans hqk)).le
          (Real.sqrt_nonneg _)
      by_cases hFk : ExplorationSchedule.mass c (k : ℝ) ≤ (k : ℝ)
      · rw [min_eq_left hFk]
        exact hgapF.trans (mul_le_mul_of_nonneg_right (le_max_left C 2) hF)
      · rw [min_eq_right (le_of_not_ge hFk)]
        exact hgap2.trans (mul_le_mul_of_nonneg_right (le_max_right C 2) (Nat.cast_nonneg _))
    have hmin : min (ExplorationSchedule.mass c (k : ℝ)) (k : ℝ) ≤ f y := by
      dsimp [f, shiftedMass]
      rw [max_eq_right hqy]
      apply min_le_min
      · exact hc.monotone (show (hc.threshold : ℝ) ≤ k by exact_mod_cast hq.trans hqk)
          ((show (hc.threshold : ℝ) ≤ k by exact_mod_cast hq.trans hqk).trans hkle) hkle
      · exact hkle
    have hwidth : y - a ≤ (M.arrivalCount s j : ℝ) -
        M.childVisit s (M.isBest s) j + 2 := by
      simp only [MCTSModel.arrivalCount, hjk, Nat.cast_add, Nat.cast_one]
      linarith
    have htwo : 2 ≤ 2 / δ * f y := by
      have hm := mul_le_mul_of_nonneg_left (hδf y) (show 0 ≤ 2 / δ by positivity)
      simpa [div_mul_cancel₀ _ hδ.ne'] using hm
    have hm := mul_le_mul_of_nonneg_left hmin hA.le
    change y - a ≤ B * f y
    dsimp [B]
    nlinarith
  have optimal_path_depth_from_integral_steps
      (hseq : M.CountUpdates) {f : ℝ → ℝ}
      (hf : Continuous f) (hfp : ∀ y, 0 < f y) (hfm : Monotone f)
      {κ C η : ℝ} (hκ : 0 < κ) (hC : 0 < C) (hη : 0 < η) (hη1 : η ≤ 1)
      (T : ℕ) (hT : 2 ≤ T)
      (hsmall : ∀ y, (T : ℝ) ≤ y → f y ≤ y)
      (hfront : ∀ s t, ¬ M.isTerminal s → M.childVisit s (M.isBest s) t = 0 →
        M.arrivalCount s t < T)
      (hsteps : ∀ s t, ¬ M.isTerminal s → T ≤ M.arrivalCount s t →
        κ ≤ ∫ y in (M.childVisit s (M.isBest s) t : ℝ)..(M.arrivalCount s t : ℝ), 1 / f y ∧
        (∫ y in (M.childVisit s (M.isBest s) t : ℝ)..(M.arrivalCount s t : ℝ), 1 / f y) ≤
          C * (1 + Real.log (f (M.arrivalCount s t) / f (M.childVisit s (M.isBest s) t))) ∧
        η * (M.arrivalCount s t : ℝ) ≤ M.childVisit s (M.isBest s) t)
      (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
      (hpath : ∀ᶠ n : ℕ in atTop,
        M.OptimalPathCounts (V n) (H n) (n + 1) (state n) (time n)) :
      (fun n => (H n : ℝ)) =Θ[∞]
        (fun n => integralPotential (fun y => 1 / f y) ((n : ℝ) + 1)) := by
    have depth_theta_of_logarithmic_path
        {H J : ℕ → ℕ} {I : ℕ → ℝ} {V P Q : ℕ → ℕ → ℝ}
        {κ C θ endpoint tail T lower δ : ℝ}
        (hκ : 0 < κ) (hC : 0 < C) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
        (hend : 0 ≤ endpoint) (htail : 0 ≤ tail) (hδ : 0 < δ)
        (hpaths : ∀ᶠ n : ℕ in atTop,
          1 ≤ H n ∧ δ ≤ I n ∧ P n 0 = I n ∧
          0 ≤ P n (J n) ∧ P n (J n) ≤ endpoint ∧
          J n ≤ H n ∧ (H n : ℝ) ≤ (J n : ℝ) + tail ∧
          0 < V n (J n) ∧ V n (J n) ≤ T ∧
          Q n 0 ≤ Real.log (V n 0) ∧ lower ≤ Q n (J n) ∧
          ∀ x < J n, 0 < V n x ∧ θ * V n x ≤ V n (x + 1) ∧
            κ ≤ P n x - P n (x + 1) ∧
            P n x - P n (x + 1) ≤ C * (1 + Q n x - Q n (x + 1))) :
        (fun n => (H n : ℝ)) =Θ[∞] I := by
      let A := C * (1 - Real.log θ)
      have hlogθ : Real.log θ ≤ 0 := Real.log_nonpos hθ.le hθ1
      have hA : 0 < A := mul_pos hC (by linarith)
      let R := endpoint + C * |Real.log T - lower| + κ * tail
      have hR : 0 ≤ R := by positivity
      have hbounds : ∀ᶠ n : ℕ in atTop,
          1 ≤ H n ∧ δ ≤ I n ∧ κ * (H n : ℝ) ≤ I n + R ∧
          I n ≤ A * (H n : ℝ) + R := by
        filter_upwards [hpaths] with n hn
        obtain ⟨hH, hI, hroot, hzero, he, hJH, ht, hv, hvT, hqroot, hqlower, hs⟩ := hn
        have hlogs : ∀ x < J n,
            Real.log (V n x) - Real.log (V n (x + 1)) ≤ -Real.log θ := by
          intro x hx
          obtain ⟨hvp, hr, _, _⟩ := hs x hx
          have hl := Real.log_le_log (mul_pos hθ hvp) hr
          rw [Real.log_mul hθ.ne' hvp.ne'] at hl
          linarith
        have hlogsum := Finset.sum_le_sum (s := Finset.range (J n))
          (fun x hx => hlogs x (Finset.mem_range.mp hx))
        simp only [Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
          nsmul_eq_mul] at hlogsum
        have hlogend : Real.log (V n (J n)) ≤ Real.log T := Real.log_le_log hv hvT
        have hq : Q n 0 - Q n (J n) ≤
            (J n : ℝ) * (-Real.log θ) + Real.log T - lower := by linarith
        have hlo := Finset.sum_le_sum (s := Finset.range (J n))
          (fun x hx => (hs x (Finset.mem_range.mp hx)).2.2.1)
        have hup := Finset.sum_le_sum (s := Finset.range (J n))
          (fun x hx => (hs x (Finset.mem_range.mp hx)).2.2.2)
        simp only [Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
          nsmul_eq_mul] at hlo
        have hsumformula : (∑ x ∈ Finset.range (J n),
            C * (1 + Q n x - Q n (x + 1))) =
            C * ((J n : ℝ) + (Q n 0 - Q n (J n))) := by
          simp only [← Finset.mul_sum]
          congr 1
          simp_rw [show ∀ x, 1 + Q n x - Q n (x + 1) =
            1 + (Q n x - Q n (x + 1)) by intro x; ring]
          simp only [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_const,
            Finset.card_range, nsmul_eq_mul, mul_one]
        rw [Finset.sum_range_sub', hsumformula, hroot] at hup
        rw [hroot] at hlo
        have hJH' : (J n : ℝ) ≤ (H n : ℝ) := by exact_mod_cast hJH
        have habs : Real.log T - lower ≤ |Real.log T - lower| := le_abs_self _
        have hm := mul_le_mul_of_nonneg_left hq hC.le
        have hAJ := mul_le_mul_of_nonneg_left hJH' hA.le
        refine ⟨hH, hI, ?_, ?_⟩
        · dsimp [R]
          nlinarith [mul_nonneg hC.le (abs_nonneg (Real.log T - lower))]
        · dsimp [A] at hAJ
          dsimp [A, R]
          nlinarith [mul_le_mul_of_nonneg_left habs hC.le, mul_nonneg hκ.le htail]
      exact depth_theta_of_additive_bounds hκ hA hR hδ hbounds
    classical
    let g := fun y => 1 / f y
    have hg : Continuous g := continuous_const.div hf (fun y => (hfp y).ne')
    have hgp : ∀ y, 0 < g y := fun y => one_div_pos.mpr (hfp y)
    have hpotmono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
        integralPotential g a ≤ integralPotential g b := by
      exact intervalIntegral.integral_mono_interval le_rfl ha hab
        ((ae_restrict_mem measurableSet_Ioc).mono fun y _ => (hgp y).le)
        (hg.intervalIntegrable 1 b)
    have hpotpos {a : ℝ} (ha : 1 ≤ a) : 0 ≤ integralPotential g a := by
      have := hpotmono (le_refl 1) ha
      simpa [integralPotential] using this
    have hδ : 0 < integralPotential g 2 :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hg.intervalIntegrable 1 2)
        (fun y _ => hgp y) (by norm_num)
    have hdata : ∀ᶠ n : ℕ in atTop,
        V n 0 = n + 1 ∧ V n (H n) < T ∧
        (∀ x ≤ H n, 1 ≤ V n x) ∧ (∀ x < H n, V n (x + 1) < V n x) := by
      filter_upwards [hpath] with n hn
      refine ⟨hn.1, ?_, ?_, ?_⟩
      · rw [hn.2.1]
        exact hfront _ _ hn.2.2.1 hn.2.2.2.1
      · intro x hx
        by_cases he : x = H n
        · subst x
          rw [hn.2.1]
          exact Nat.succ_pos _
        · obtain ⟨_, hp, _⟩ := hn.2.2.2.2 x (lt_of_le_of_ne hx he)
          rw [hp]
          exact Nat.succ_pos _
      · intro x hx
        obtain ⟨_, hp, hc⟩ := hn.2.2.2.2 x hx
        rw [hp, hc]
        exact Nat.lt_succ_of_le (hseq.child_le_parent _ _ _)
    let J : ℕ → ℕ := fun n => if hd : ∀ x < H n, V n (x + 1) < V n x then
        (finite_chain_cutoff (V n) (H n) T hd).choose else 0
    apply depth_theta_of_logarithmic_path
      (H := H) (J := J)
      (I := fun n => integralPotential g ((n : ℝ) + 1))
      (V := fun n x => (V n x : ℝ))
      (P := fun n x => integralPotential g (V n x))
      (Q := fun n x => Real.log (f (V n x)))
      (endpoint := integralPotential g T) (tail := T) (T := T)
      (lower := Real.log (f 0)) (δ := integralPotential g 2)
      hκ hC hη hη1 (hpotpos (by exact_mod_cast (show 1 ≤ T by omega)))
      (Nat.cast_nonneg T) hδ
    filter_upwards [hpath, hdata, eventually_ge_atTop T] with n hn hd hnT
    have hj : J n ≤ H n ∧ (J n = H n ∨ V n (J n) < T) ∧
        H n ≤ J n + T ∧ ∀ x < J n, T ≤ V n x := by
      simpa only [J, dif_pos hd.2.2.2] using
        (finite_chain_cutoff (V n) (H n) T hd.2.2.2).choose_spec
    have hje : V n (J n) < T := by
      rcases hj.2.1 with he | hh
      · simpa [he] using hd.2.1
      · exact hh
    have hjpos : 1 ≤ V n (J n) := hd.2.2.1 _ hj.1
    have hHpos : 1 ≤ H n := by
      by_contra hh
      have hz : H n = 0 := by omega
      have he := hd.2.1
      rw [hz, hd.1] at he
      omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    refine ⟨hHpos, hpotmono (by norm_num) (by linarith), ?_,
      hpotpos (by exact_mod_cast hjpos), hpotmono (by exact_mod_cast hjpos)
        (by exact_mod_cast hje.le), hj.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hd.1, Nat.cast_add, Nat.cast_one]
    · exact_mod_cast hj.2.2.1
    · exact_mod_cast (show 0 < V n (J n) by omega)
    · exact_mod_cast hje.le
    · apply Real.log_le_log (hfp _)
      exact hsmall _ (by rw [hd.1]; exact_mod_cast (show T ≤ n + 1 by omega))
    · exact Real.log_le_log (hfp 0) (hfm (Nat.cast_nonneg _))
    · intro x hx
      have hxH := hx.trans_le hj.1
      obtain ⟨hnt, hp, hc⟩ := hn.2.2.2.2 x hxH
      have hbig : T ≤ M.arrivalCount (state n x) (time n x) := by
        rw [← hp]
        exact hj.2.2.2 x hx
      obtain ⟨hlo, hup, hret⟩ := hsteps _ _ hnt hbig
      rw [← hp, ← hc] at hlo hup hret
      have hdiff : integralPotential g (V n x) - integralPotential g (V n (x + 1)) =
          ∫ y in (V n (x + 1) : ℝ)..(V n x : ℝ), g y := by
        exact intervalIntegral.integral_interval_sub_left
          (hg.intervalIntegrable 1 _) (hg.intervalIntegrable 1 _)
      refine ⟨by exact_mod_cast (show 0 < V n x from lt_of_lt_of_le Nat.zero_lt_one
        (hd.2.2.1 x hxH.le)), hret, ?_, ?_⟩
      · simpa only [hdiff] using hlo
      · rw [hdiff]
        rw [Real.log_div (hfp _).ne' (hfp _).ne'] at hup
        simpa only [add_sub_assoc] using hup
  have positive_monotone_integral_shift {f : ℝ → ℝ}
      (hf : Continuous f) (hp : ∀ x, 0 < f x) (hm : Monotone f) :
      (fun n : ℕ => integralPotential (fun y => 1 / f y) ((n : ℝ) + 1))
        =Θ[∞] (fun n : ℕ => integralPotential (fun y => 1 / f (y + 2)) n) := by
    let g := fun y => 1 / f y
    let r := fun y => g (y + 2)
    have hg : Continuous g := continuous_const.div hf (fun x => (hp x).ne')
    have hr : Continuous r := hg.comp (continuous_id.add continuous_const)
    have hgp : ∀ x, 0 < g x := fun x => one_div_pos.mpr (hp x)
    have hrp : ∀ x, 0 < r x := fun x => hgp (x + 2)
    let δ := integralPotential r 2
    have hδ : 0 < δ := by
      apply intervalIntegral.integral_pos (by norm_num : (1 : ℝ) < 2) hr.continuousOn
      · intro x hx; exact (hrp x).le
      · exact ⟨1, by constructor <;> norm_num, hrp 1⟩
    let K := integralPotential g 3
    have hK : 0 ≤ K := intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ => (hgp x).le)
    have hbound : ∀ᶠ n : ℕ in atTop,
        δ ≤ integralPotential r n ∧
        integralPotential r n ≤ integralPotential g ((n : ℝ) + 1) ∧
        integralPotential g ((n : ℝ) + 1) ≤ K + integralPotential r n := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by linarith
      have hnsub : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      refine ⟨integralPotential_mono hr.continuousOn (fun x _ => (hrp x).le)
        (by norm_num) hn2, ?_, ?_⟩
      · have hcmp := intervalIntegral.integral_mono_on (μ := volume) hn1
          (hr.intervalIntegrable 1 n) (hg.intervalIntegrable 1 n)
          (fun y _ => one_div_le_one_div_of_le (hp y) (hm (by linarith : y ≤ y + 2)))
        exact hcmp.trans (integralPotential_mono hg.continuousOn (fun x _ => (hgp x).le)
          hn1 (by linarith))
      · have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hg.intervalIntegrable 1 3) (hg.intervalIntegrable 3 ((n : ℝ) + 1))
        have hchange : (∫ y in (3 : ℝ)..((n : ℝ) + 1), g y) =
            integralPotential r ((n : ℝ) - 1) := by
          dsimp [integralPotential, r]
          rw [intervalIntegral.integral_comp_add_right]
          congr 1 <;> ring
        have hlast := integralPotential_mono hr.continuousOn (fun x _ => (hrp x).le)
          hnsub (show (n : ℝ) - 1 ≤ n by linarith)
        rw [hchange] at hsplit
        change K + integralPotential r ((n : ℝ) - 1) =
          integralPotential g ((n : ℝ) + 1) at hsplit
        linarith
    apply theta_of_eventual_sandwich
    · exact hbound.mono (fun n hn => hδ.le.trans (hn.1.trans hn.2.1))
    · exact hbound.mono (fun n hn => hδ.le.trans hn.1)
    · refine ⟨1 + K / δ, by positivity, ?_⟩
      filter_upwards [hbound] with n hn
      have hmul := mul_le_mul_of_nonneg_left hn.1 (div_nonneg hK hδ.le)
      rw [div_mul_cancel₀ _ hδ.ne'] at hmul
      nlinarith [hn.2.2]
    · exact ⟨1, by norm_num, hbound.mono (fun n hn => by simpa only [one_mul] using hn.2.1)⟩
  have regularized_integral_equiv
      {q : ℕ} (hq : hc.threshold ≤ q) :
      (fun n : ℕ => integralPotential
        (fun y => 1 / shiftedMass c q (y + 2)) n)
        =Θ[∞] DepthIntegral.saturated c := by
    let r := fun y => 1 / shiftedMass c q (y + 2)
    let s := fun y => 1 / ExplorationSchedule.mass c y + 1 / y
    obtain ⟨hf, hp, hm, hb⟩ := shiftedMass_properties hc hq
    have hr : Continuous r :=
      continuous_const.div (hf.comp (continuous_id.add continuous_const))
        (fun y => (hp (y + 2)).ne')
    have hrp : ∀ y ≥ 1, 0 < r y := fun y _ => one_div_pos.mpr (hp (y + 2))
    have hi : ContinuousOn (fun y : ℝ => 1 / y) (Set.Ici 1) :=
      continuousOn_const.div continuousOn_id (fun y hy => ne_of_gt (lt_of_lt_of_le zero_lt_one hy))
    have hs : ContinuousOn s (Set.Ici 1) := (exploration_integrand_continuous hc).add hi
    have hsp : ∀ y ≥ 1, 0 < s y := by
      intro y hy
      exact add_pos (one_div_pos.mpr
        (mul_pos (hc.positive y hy) (Real.sqrt_pos.2 (by linarith)))) (by positivity)
    have hbounds : ∀ᶠ y : ℝ in atTop, r y ≤ s y ∧ s y ≤ 2 * r y := by
      filter_upwards [eventually_ge_atTop (max (q : ℝ) 1)] with y hy
      have hqy : (q : ℝ) ≤ y := (le_max_left _ _).trans hy
      have hy1 : 1 ≤ y := (le_max_right _ _).trans hy
      dsimp [r, s, shiftedMass]
      rw [add_sub_cancel_right, max_eq_right hqy]
      obtain ⟨hlo, hup⟩ := general_reciprocal_min
        (mul_pos (hc.positive y hy1) (Real.sqrt_pos.2 (by linarith))) (by linarith : 0 < y)
      dsimp only [ExplorationSchedule.mass] at hlo hup ⊢
      exact ⟨hup, by linarith⟩
    have htheta : (fun n : ℕ => integralPotential r n) =Θ[∞]
        (fun n : ℕ => integralPotential s n) := by
      constructor
      · apply positive_integral_comparison hr.continuousOn hs hrp hsp (by norm_num : (0 : ℝ) < 1)
        exact hbounds.mono (fun y hy => by simpa using hy.1)
      · exact positive_integral_comparison hs hr.continuousOn hsp hrp (by norm_num : (0 : ℝ) < 2)
          (hbounds.mono (fun _ hy => hy.2))
    have heq : (fun n : ℕ => integralPotential s n) =ᶠ[atTop] DepthIntegral.saturated c := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hlog : (∫ y in (1 : ℝ)..(n : ℝ), 1 / y) = Real.log (n : ℝ) := by
        simpa using integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1)
          (show (0 : ℝ) < n by linarith)
      dsimp [integralPotential, s]
      rw [intervalIntegral.integral_add
        (((exploration_integrand_continuous hc).mono
          Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hn1)
        ((hi.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hn1), hlog]
      simp only [DepthIntegral.saturated, DepthIntegral.exploration,
        ExplorationSchedule.mass, add_comm]
    exact htheta.trans heq.isTheta
  let q := hc.threshold
  let f := shiftedMass c q
  obtain ⟨hf, hfp, hfm, hsmall⟩ := shiftedMass_properties hc (le_refl q)
  obtain ⟨κ, hκ, Tl, hl⟩ := scheduled_shifted_integral_lower q le_rfl
  obtain ⟨C, hC, hupp⟩ := general_uniform_arrival_upper hseq (countSchedule_of_schedule hc) hreg hu
  obtain ⟨B, hB, hb⟩ := scheduled_optimal_edge_integral_upper (le_refl q) hC hupp
  obtain ⟨θ, hθ, hθ1, mr, hshare⟩ :=
    scheduled_optimal_share_of_prior hseq hc.positive hreg hu hopt
  obtain ⟨K, hfront⟩ := frontier_bound_of_optimal_share hθ hshare
  let η := θ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by dsimp [η]; linarith
  obtain ⟨R, hR⟩ := exists_nat_ge (((q : ℝ) + 2) / η)
  let T := max (max (max 2 (q + 2)) (max Tl (mr + 1))) (max R (K + 1))
  have hT2 : 2 ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hTq : q + 2 ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hTl : Tl ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hTmr : mr + 1 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hTR : R ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTK : K + 1 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hd : (fun n => (H n : ℝ)) =Θ[∞]
      (fun n => integralPotential (fun y => 1 / f y) ((n : ℝ) + 1)) := by
    apply optimal_path_depth_from_integral_steps hseq.toCountUpdates hf hfp hfm
      hκ hB hη hη1 T hT2 _ _ _ V H state time hpath
    · intro y hy
      exact hsmall y ((show (q : ℝ) + 2 ≤ T by exact_mod_cast hTq).trans hy)
    · intro s t hnt hz
      exact lt_of_le_of_lt (hfront s t hnt hz) (lt_of_lt_of_le (Nat.lt_succ_self K) hTK)
    · intro s t hnt ht
      have hm : mr ≤ M.parentVisit s t := by
        have hh := hTmr.trans ht
        simp only [MCTSModel.arrivalCount] at hh
        omega
      have hm1 : 1 ≤ M.parentVisit s t := by
        have hh := hT2.trans ht
        simp only [MCTSModel.arrivalCount] at hh
        omega
      have hhalf : (M.arrivalCount s t : ℝ) / 2 ≤ M.parentVisit s t := by
        simp only [MCTSModel.arrivalCount, Nat.cast_add, Nat.cast_one]
        have : (1 : ℝ) ≤ M.parentVisit s t := by exact_mod_cast hm1
        linarith
      have hr : η * (M.arrivalCount s t : ℝ) ≤ M.childVisit s (M.isBest s) t := by
        have hh := mul_le_mul_of_nonneg_left hhalf hθ.le
        have hh' := hshare s t hnt hm
        dsimp [η]
        nlinarith
      have ha : (q : ℝ) + 2 ≤ M.childVisit s (M.isBest s) t := by
        have hh : ((q : ℝ) + 2) / η ≤ M.arrivalCount s t := hR.trans
          (by exact_mod_cast hTR.trans ht)
        have hm := (div_le_iff₀ hη).1 hh
        nlinarith
      exact ⟨hl s t hnt (hTl.trans ht), hb s t ha, hr⟩
  exact hd.trans ((positive_monotone_integral_shift hf hfp hfm).trans
    (regularized_integral_equiv (le_refl q)))

/-- Theorem 2: integral and logarithmic depth rates for scheduled pUCT. -/
theorem theorem2 {M : MCTSModel} {c : ℝ → ℝ}
    (hseq : M.Scheduled c) (hc : Assumption.ExplorationSchedule c)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s))
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.OptimalPathCounts (V n) (H n) (n + 1) (state n) (time n)) :
    ((c =O[∞] Real.sqrt) → (fun n => (H n : ℝ)) =Θ[∞] DepthIntegral.exploration c) ∧
    ((Real.sqrt =O[∞] c) → (fun n => (H n : ℝ)) =Θ[∞] (fun n : ℕ => Real.log (n : ℝ))) := by
  have hdepth := scheduled_puct_depth hseq hc hreg hu hopt V H state time hpath
  exact ⟨fun hb => hdepth.trans (saturated_depth_weak hc hb),
    fun hb => hdepth.trans (saturated_depth_strong hc hb)⟩

/-- Theorem 2, capped: scheduled pUCT eventually reaches terminal depth L. -/
theorem theorem2_capped {M : MCTSModel} {c : ℝ → ℝ}
    (hseq : M.Scheduled c) (hc : Assumption.ExplorationSchedule c)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hregime : ((fun m : ℕ => ExplorationSchedule.mass c m) =o[∞] (fun m => (m : ℝ))) ∨
      ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s))
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (L : ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.CappedOptimalPathCounts (V n) (H n) (n + 1) L (state n) (time n)) :
    ∀ᶠ n : ℕ in atTop, H n = L := by
  let hg := countSchedule_of_schedule hc
  have hshare_data : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ m₀ : ℕ, ∀ s t,
      ¬ M.isTerminal s → m₀ ≤ M.parentVisit s t →
      θ * (M.parentVisit s t : ℝ) ≤ M.childVisit s (M.isBest s) t := by
    rcases hregime with hsub | hopt
    · obtain ⟨C, hC, hb⟩ := general_uniform_arrival_upper hseq hg hreg hu
      obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.1
        (hsub.bound (show (0 : ℝ) < 1 / (2 * C) by positivity))
      refine ⟨1 / 2, by norm_num, by norm_num, max hg.threshold m₁, ?_⟩
      intro s t _ hm
      have hupper := hb s t ((le_max_left _ _).trans hm)
      have hsmall := hm₁ (M.parentVisit s t) ((le_max_right _ _).trans hm)
      have hF : 0 ≤ ExplorationSchedule.mass c (M.parentVisit s t) :=
        mul_nonneg (hg.positive _ (by
          exact_mod_cast hg.threshold_pos.trans ((le_max_left _ _).trans hm))).le
          (Real.sqrt_nonneg _)
      simp only [Real.norm_eq_abs, abs_of_nonneg hF,
        abs_of_nonneg (Nat.cast_nonneg (M.parentVisit s t) (α := ℝ))] at hsmall
      have hmul := mul_le_mul_of_nonneg_left hsmall hC.le
      have heq : C * (1 / (2 * C) * (M.parentVisit s t : ℝ)) =
          (M.parentVisit s t : ℝ) / 2 := by field_simp
      rw [heq] at hmul
      simp only [MCTSModel.arrivalCount, Nat.cast_add, Nat.cast_one] at hupper
      linarith
    · exact scheduled_optimal_share_of_prior hseq hg.positive hreg hu hopt
  exact scheduled_depth_capped_of_optimal_share hshare_data V H L state time hpath

/-! ## Regularly varying depth rates -/

/-- Corollary 2.1: regularly varying depth rates when c = O(√m). -/
theorem corollary21 {M : MCTSModel} {c L : ℝ → ℝ} {α : ℝ}
    (hseq : M.Scheduled c) (hc : Assumption.ExplorationSchedule c)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s))
    (hbound : c =O[∞] Real.sqrt) (hL : ContinuousSlowlyVarying L)
    (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.OptimalPathCounts (V n) (H n) (n + 1) (state n) (time n)) :
    α ≤ 1 / 2 ∧
      (α < 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
        (fun n => Real.sqrt (n : ℝ) / c n)) ∧
      (α = 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞] DepthIntegral.critical L) := by
  have hhalving {f : ℝ → ℝ} {M q n : ℝ}
      (hc : ContinuousOn f (Set.Ici 1)) (hp : ∀ x ≥ 1, 0 < f x)
      (hM : 1 ≤ M) (hq : 0 < q) (hn : 2 * M ≤ n)
      (hmono : MonotoneOn f (Set.Ici M))
      (hdouble : ∀ x ≥ M, f (2 * x) ≤ q * f x) :
      (2 - q) * integralPotential (fun x => 1 / f x) n ≤
        2 * integralPotential (fun x => 1 / f x) M + q * (n / f n) := by
    let g := fun x => 1 / f x
    have hgc : ContinuousOn g (Set.Ici 1) :=
      continuousOn_const.div hc (fun x hx => (hp x hx).ne')
    have hgp : ∀ x ≥ 1, 0 ≤ g x := fun x hx => (one_div_pos.mpr (hp x hx)).le
    have hn1 : 1 ≤ n := by linarith
    have hhalf : M ≤ n / 2 := by linarith
    have hhalf1 : 1 ≤ n / 2 := hM.trans hhalf
    have htwoM : 1 ≤ 2 * M := by linarith
    have hscaled : ContinuousOn (fun x => g (x / 2)) (Set.uIcc (2 * M) n) := by
      apply hgc.comp (continuous_id.div_const 2).continuousOn
      intro x hx
      rw [Set.uIcc_of_le hn] at hx
      change 1 ≤ x / 2
      linarith [hx.1]
    have hcomp := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hn
      hscaled.intervalIntegrable
      (((hgc.mono (fun _ hx => (le_min htwoM hn1).trans hx.1)).intervalIntegrable).const_mul q)
      (fun x hx => by
        have hxm : M ≤ x / 2 := by linarith [hx.1]
        have hd : f x ≤ q * f (x / 2) := by
          simpa only [show 2 * (x / 2) = x by ring] using hdouble (x / 2) hxm
        have hfx := hp x (htwoM.trans hx.1)
        have hfh := hp (x / 2) (hM.trans hxm)
        dsimp [g]
        rw [← mul_div_assoc, mul_one]
        apply (div_le_div_iff₀ hfh hfx).2
        simpa [mul_comm] using hd)
    have hscale : (∫ x in 2 * M..n, g (x / 2)) = 2 * (∫ x in M..n / 2, g x) := by
      simp [intervalIntegral.integral_comp_div, smul_eq_mul]
    rw [hscale, intervalIntegral.integral_const_mul] at hcomp
    have hseg := intervalIntegral.integral_interval_sub_left (μ := MeasureTheory.volume)
      ((hgc.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hn1)
      ((hgc.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc htwoM)
    change integralPotential g n - integralPotential g (2 * M) = _ at hseg
    have htwo_nonneg := (show 0 ≤ integralPotential _ _ from
      intervalIntegral.integral_nonneg htwoM (fun x hx => hgp x hx.1))
    have hmain : 2 * (∫ x in M..n / 2, g x) ≤ q * integralPotential g n := by
      have hle : (∫ x in 2 * M..n, g x) ≤ integralPotential g n := by linarith
      exact hcomp.trans (mul_le_mul_of_nonneg_left hle hq.le)
    have hmonoseg : MonotoneOn f (Set.Icc (n / 2) n) := by
      apply hmono.mono
      intro x hx
      exact hhalf.trans hx.1
    have hrect := reciprocal_integral_rectangles hc hp hhalf1 (by linarith) hmonoseg
    have hd : f n ≤ q * f (n / 2) := by
      simpa only [show 2 * (n / 2) = n by ring] using hdouble (n / 2) hhalf
    have htail : (∫ x in n / 2..n, g x) ≤ q / 2 * (n / f n) := by
      apply hrect.2.trans
      have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ n by linarith)
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (hp _ hhalf1) (hp _ hn1)).2
      nlinarith
    have hsplit₁ := intervalIntegral.integral_interval_sub_left (μ := MeasureTheory.volume)
      ((hgc.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hhalf1)
      ((hgc.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hM)
    change integralPotential g (n / 2) - integralPotential g M = _ at hsplit₁
    have hsplit₂ := intervalIntegral.integral_interval_sub_left (μ := MeasureTheory.volume)
      ((hgc.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hn1)
      ((hgc.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hhalf1)
    change integralPotential g n - integralPotential g (n / 2) = _ at hsplit₂
    change (2 - q) * integralPotential g n ≤ 2 * integralPotential g M + q * (n / f n)
    nlinarith
  have hintegral_rate {f : ℝ → ℝ} {M q κ : ℝ}
      (hc : ContinuousOn f (Set.Ici 1)) (hp : ∀ x ≥ 1, 0 < f x)
      (hM : 1 ≤ M) (hq : 0 < q) (hq2 : q < 2) (hκ : 0 < κ)
      (hmono : MonotoneOn f (Set.Ici M))
      (hdouble : ∀ x ≥ M, f (2 * x) ≤ q * f x)
      (hroot : ∀ᶠ n : ℕ in atTop, κ * f n ≤ n) :
      (fun n : ℕ => integralPotential (fun x => 1 / f x) n) =Θ[∞]
        (fun n => (n : ℝ) / f n) := by
    let g := fun x => 1 / f x
    let A := integralPotential g M
    have hA : 0 ≤ A := (show 0 ≤ integralPotential _ _ from
      intervalIntegral.integral_nonneg hM (fun x hx => (one_div_pos.mpr (hp x hx.1)).le))
    have hgc : ContinuousOn g (Set.Ici 1) :=
      continuousOn_const.div hc (fun x hx => (hp x hx).ne')
    have hlarge : ∀ᶠ n : ℕ in atTop, 2 * M ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
    apply theta_of_eventual_sandwich
    · filter_upwards [hlarge] with n hn
      exact (show 0 ≤ integralPotential _ _ from
        intervalIntegral.integral_nonneg (by linarith)
          (fun x hx => (one_div_pos.mpr (hp x hx.1)).le))
    · filter_upwards [hlarge] with n hn
      exact div_nonneg (by positivity) (hp n (by linarith)).le
    · refine ⟨(2 * A / κ + q) / (2 - q),
        div_pos (add_pos_of_nonneg_of_pos (div_nonneg (by positivity) hκ.le) hq)
          (by linarith), ?_⟩
      filter_upwards [hlarge, hroot] with n hn hroot_n
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
      have hG : κ ≤ (n : ℝ) / f n := (le_div_iff₀ (hp n hn1)).2 hroot_n
      have hAG : 2 * A ≤ (2 * A / κ) * ((n : ℝ) / f n) := by
        have h : (2 * A / κ) * κ ≤ (2 * A / κ) * ((n : ℝ) / f n) :=
          mul_le_mul_of_nonneg_left hG (div_nonneg (by positivity) hκ.le)
        simpa [div_mul_cancel₀ _ hκ.ne'] using h
      have hself := hhalving hc hp hM hq hn hmono hdouble
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (show 0 < 2 - q by linarith)).2
      dsimp [A, g] at hAG ⊢
      nlinarith
    · refine ⟨1 / 2, by norm_num, ?_⟩
      filter_upwards [hlarge] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
      have hh : (1 : ℝ) ≤ (n : ℝ) / 2 := by linarith
      have hmonoseg : MonotoneOn f (Set.Icc ((n : ℝ) / 2) n) := by
        apply hmono.mono
        intro x hx
        change M ≤ x
        linarith [hx.1]
      have hrect := reciprocal_integral_rectangles hc hp hh (by linarith) hmonoseg
      have hsplit := intervalIntegral.integral_interval_sub_left (μ := MeasureTheory.volume)
        ((hgc.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hn1)
        ((hgc.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hh)
      change integralPotential g n - integralPotential g ((n : ℝ) / 2) = _ at hsplit
      have hnonneg := (show 0 ≤ integralPotential _ _ from
        intervalIntegral.integral_nonneg hh (fun x hx => (one_div_pos.mpr (hp x hx.1)).le))
      dsimp [g] at hsplit hnonneg
      have hhalf : (1 / 2 : ℝ) * ((n : ℝ) / f n) = ((n : ℝ) - (n : ℝ) / 2) / f n := by ring
      rw [hhalf]
      linarith [hrect.1]
  have hsubcritical {c L : ℝ → ℝ} {α κ m₀ : ℝ}
      (hcont : ContinuousOn c (Set.Ici 1)) (hpos : ∀ x ≥ 1, 0 < c x)
      (hmonotone : MonotoneOn (fun x => c x * Real.sqrt x) (Set.Ici m₀))
      (hκ : 0 < κ)
      (hroot : ∀ᶠ n : ℕ in atTop, κ * (c n * Real.sqrt (n : ℝ)) ≤ n)
      (hL : ContinuousSlowlyVarying L) (hα : α < 1 / 2)
      (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x) :
      DepthIntegral.exploration c =Θ[∞] (fun n => Real.sqrt (n : ℝ) / c n) := by
    let f := fun x => c x * Real.sqrt x
    let β := α + 1 / 2
    let r := Real.rpow 2 β
    let q := (r + 2) / 2
    have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
    have hr2 : r < 2 := by
      have hβ : β < 1 := by dsimp [β]; linarith
      simpa [r] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hβ
    have hq : 0 < q := by dsimp [q]; linarith
    have hq2 : q < 2 := by dsimp [q]; linarith
    have hrq : r < q := by dsimp [q]; linarith
    have hfc : ContinuousOn f (Set.Ici 1) := hcont.mul Real.continuous_sqrt.continuousOn
    have hfp : ∀ x ≥ 1, 0 < f x := fun x hx =>
      mul_pos (hpos x hx) (Real.sqrt_pos.2 (by linarith))
    have hrepr : ∀ x ≥ 1, f x = Real.rpow x β * L x := fun x hx => rpow_form_mul_sqrt hform x hx
    have hratio : Tendsto (fun x : ℝ => f (2 * x) / f x) atTop (𝓝 r) :=
      regular_variation_doubling_limit hL hrepr
    have hdouble_ev : ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ f (2 * x) ≤ q * f x := by
      filter_upwards [eventually_ge_atTop (1 : ℝ), hratio.eventually (gt_mem_nhds hrq)]
        with x hx hrat
      exact ⟨hx, ((div_lt_iff₀ (hfp x hx)).1 hrat).le⟩
    obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hdouble_ev
    let M : ℝ := max m₀ (max 1 M₀)
    have hM : 1 ≤ M := (le_max_left 1 M₀).trans (le_max_right _ _)
    have hmono : MonotoneOn f (Set.Ici M) := by
      intro x hx y hy hxy
      exact hmonotone ((le_max_left m₀ (max 1 M₀)).trans hx)
        ((le_max_left m₀ (max 1 M₀)).trans hy) hxy
    have hdouble : ∀ x ≥ M, f (2 * x) ≤ q * f x := by
      intro x hx
      exact (hM₀ x (((le_max_right 1 M₀).trans (le_max_right _ _)).trans hx)).2
    have heval := hintegral_rate hfc hfp hM hq hq2 hκ hmono hdouble hroot
    have heq : (fun n : ℕ => (n : ℝ) / f n) =ᶠ[atTop]
        (fun n => Real.sqrt (n : ℝ) / c n) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hn
      have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnpos).ne'
      dsimp [f]
      have hsq := Real.sq_sqrt hnpos.le
      field_simp
      rw [hsq]
    exact heval.trans heq.isTheta
  have hdepth := scheduled_puct_depth hseq hc hreg hu hopt V H state time hpath
  have hweak := hdepth.trans (saturated_depth_weak hc hbound)
  have hnBound : (fun n : ℕ => c n) =O[∞] DepthProfile.sqrtSimulationCount :=
    hbound.comp_tendsto tendsto_natCast_atTop_atTop
  have hindex : α ≤ 1 / 2 := regular_variation_index_le_half hL (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hform n (by exact_mod_cast hn)) hnBound
  refine ⟨hindex, ?_, ?_⟩
  · intro hα
    obtain ⟨C, hC, hb⟩ := hbound.exists_pos
    have hroot : ∀ᶠ n : ℕ in atTop, (1 / C) * (c n * Real.sqrt (n : ℝ)) ≤ n := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually hb.bound] with n hn
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
      have hm := mul_le_mul_of_nonneg_right ((le_abs_self (c n)).trans hn)
        (Real.sqrt_nonneg (n : ℝ))
      rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)] at hm
      rw [one_div_mul_eq_div]
      exact (div_le_iff₀ hC).2 (by nlinarith)
    exact hweak.trans (hsubcritical hc.continuous hc.positive
      hc.monotone (one_div_pos.mpr hC) hroot hL hα hform)
  · intro hα
    exact hweak.trans
      (exploration_eq_critical_of_sqrt_form (c := c) (L := L) (fun x hx => by
        rw [hform x hx, hα]
        exact congrArg (fun y => y * L x) (Real.sqrt_eq_rpow x).symm)).isTheta

/-- Corollary 2.1, capped: eventual terminal depth and both capped rates. -/
theorem corollary21_capped {M : MCTSModel} {c L : ℝ → ℝ} {α : ℝ}
    (hseq : M.Scheduled c) (hc : Assumption.ExplorationSchedule c)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s))
    (hbound : c =O[∞] Real.sqrt) (hL : ContinuousSlowlyVarying L)
    (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (D : ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.CappedOptimalPathCounts (V n) (H n) (n + 1) D (state n) (time n)) :
    (∀ᶠ n : ℕ in atTop, H n = D) ∧ α ≤ 1 / 2 ∧
      (α < 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
        (fun n => min (D : ℝ) (Real.sqrt (n : ℝ) / c n))) ∧
      (α = 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
        (fun n => min (D : ℝ) (DepthIntegral.critical L n))) := by
  have hcap := theorem2_capped hseq hc hreg hu (Or.inr hopt) V H D state time hpath
  have hdepth : ∀ᶠ n : ℕ in atTop, H n ≤ D ∧ (D = 0 ∨ 1 ≤ H n) := by
    filter_upwards [hcap] with n hn
    exact ⟨hn.le, (Nat.eq_zero_or_pos D).imp id (fun hD => hn ▸ hD)⟩
  have hnBound : (fun n : ℕ => c n) =O[∞] DepthProfile.sqrtSimulationCount :=
    hbound.comp_tendsto tendsto_natCast_atTop_atTop
  have hα : α ≤ 1 / 2 := regular_variation_index_le_half hL (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hform n (by exact_mod_cast hn)) hnBound
  obtain ⟨C, hC, hb⟩ := hnBound.exists_pos
  have hratio : ∀ᶠ n : ℕ in atTop, 1 / C ≤ Real.sqrt (n : ℝ) / c n := by
    filter_upwards [hb.bound, eventually_ge_atTop 1] with n hn hn1
    have hp : 0 < c n := by
      rw [hform n (by exact_mod_cast hn1)]
      exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast Nat.zero_lt_of_lt hn1) _)
        (hL.positive n (by exact_mod_cast hn1))
    simp only [DepthProfile.sqrtSimulationCount, Real.norm_eq_abs, abs_of_nonneg hp.le,
      abs_of_nonneg (Real.sqrt_nonneg _)] at hn
    apply (le_div_iff₀ hp).2
    have hscale := mul_le_mul_of_nonneg_left hn (one_div_pos.mpr hC).le
    simpa only [← mul_assoc, one_div_mul_cancel hC.ne', one_mul] using hscale
  -- The integral at 2 gives a positive lower bound.
  let g := fun x : ℝ => 1 / (x * L x)
  have hgc : ContinuousOn g (Set.Ici 1) := by
    apply continuousOn_const.div (continuousOn_id.mul hL.continuous)
    intro x hx
    change 1 ≤ x at hx
    change x * L x ≠ 0
    exact ne_of_gt (mul_pos (by linarith) (hL.positive x hx))
  have hgp : ∀ x ≥ 1, 0 < g x := fun x hx =>
    one_div_pos.mpr (mul_pos (by linarith) (hL.positive x hx))
  have hδ : 0 < integralPotential g 2 := by
    apply intervalIntegral.integral_pos (by norm_num : (1 : ℝ) < 2)
      (hgc.mono (fun _ hx => hx.1))
    · intro x hx
      exact (hgp x hx.1.le).le
    · exact ⟨1, by constructor <;> norm_num, hgp 1 (le_refl _)⟩
  have hcritical : ∀ᶠ n : ℕ in atTop, integralPotential g 2 ≤ DepthIntegral.critical L n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact integralPotential_mono hgc (fun x hx => (hgp x hx).le)
      (by norm_num) (by exact_mod_cast hn)
  exact ⟨hcap, hα,
    fun _ => finite_depth_capped_rate H D _ (one_div_pos.mpr hC) hratio hdepth,
    fun _ => finite_depth_capped_rate H D _ hδ hcritical hdepth⟩

/-- Corollary 2.2: all three depth regimes for regularly varying exploration schedules. -/
theorem corollary22 {M : MCTSModel} {c L : ℝ → ℝ} {α : ℝ}
    (hseq : M.Scheduled c) (hc : Assumption.ExplorationSchedule c)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s))
    (hL : ContinuousSlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.OptimalPathCounts (V n) (H n) (n + 1) (state n) (time n)) :
    -(1 / 2 : ℝ) ≤ α ∧
      (α < 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
        (fun n => Real.sqrt (n : ℝ) / c n)) ∧
      (α = 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
        (fun n => Real.log (n : ℝ) + DepthIntegral.critical L n)) ∧
      (1 / 2 < α → (fun n => (H n : ℝ)) =Θ[∞] (fun n : ℕ => Real.log (n : ℝ))) := by
  have hdepth := scheduled_puct_depth hseq hc hreg hu hopt V H state time hpath
  obtain ⟨hα, hsub, hsup⟩ := regular_variation_of_schedule hc hL hform
  refine ⟨hα, fun hα =>
    (corollary21 hseq hc hreg hu hopt (hsub hα) hL hform V H state time hpath).2.1 hα,
    fun hα => hdepth.trans (Filter.EventuallyEq.isTheta ?_),
    fun hα => hdepth.trans (saturated_depth_strong hc (hsup hα))⟩
  exact (exploration_eq_critical_of_sqrt_form (c := c) (L := L) (fun x hx => by
    rw [hform x hx, hα]
    exact congrArg (fun y => y * L x) (Real.sqrt_eq_rpow x).symm)).mono
    (fun n hn => by simp only [DepthIntegral.saturated, hn])

/-- Corollary 2.2, capped: eventual terminal depth and all three capped rates. -/
theorem corollary22_capped {M : MCTSModel} {c L : ℝ → ℝ} {α : ℝ}
    (hseq : M.Scheduled c) (hc : Assumption.ExplorationSchedule c)
    (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s))
    (hL : ContinuousSlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (D : ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.CappedOptimalPathCounts (V n) (H n) (n + 1) D (state n) (time n)) :
    (∀ᶠ n : ℕ in atTop, H n = D) ∧ -(1 / 2 : ℝ) ≤ α ∧
      (α < 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
        (fun n => min (D : ℝ) (Real.sqrt (n : ℝ) / c n))) ∧
      (α = 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
        (fun n => min (D : ℝ) (Real.log (n : ℝ) + DepthIntegral.critical L n))) ∧
      (1 / 2 < α → (fun n => (H n : ℝ)) =Θ[∞]
        (fun n : ℕ => min (D : ℝ) (Real.log (n : ℝ)))) := by
  obtain ⟨hα, hsub, -⟩ := regular_variation_of_schedule hc hL hform
  have hcap := theorem2_capped hseq hc hreg hu (Or.inr hopt) V H D state time hpath
  have hterminal : ∀ᶠ n : ℕ in atTop, H n ≤ D ∧ (D = 0 ∨ 1 ≤ H n) := by
    filter_upwards [hcap] with n hn
    exact ⟨hn.le, (Nat.eq_zero_or_pos D).imp id (fun hD => hn ▸ hD)⟩
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  refine ⟨hcap, hα,
    fun hα => (corollary21_capped hseq hc hreg hu hopt (hsub hα) hL hform
      V H D state time hpath).2.2.1 hα,
    fun _ => finite_depth_capped_rate H D _ (δ := 1) (by norm_num) ?_ hterminal,
    fun _ => finite_depth_capped_rate H D _ (δ := 1) (by norm_num) hlog hterminal⟩
  filter_upwards [hlog, eventually_ge_atTop 1] with n hn hn1
  have hi : 0 ≤ DepthIntegral.critical L n := by
    apply intervalIntegral.integral_nonneg (by exact_mod_cast hn1)
    intro x hx
    exact one_div_nonneg.mpr (mul_nonneg (by linarith [hx.1]) (hL.positive x hx.1).le)
  linarith

/-! ## Measurable depth rates -/

set_option maxHeartbeats 3000000 in
-- Local subproofs share one elaboration budget.
/-- Corollary 2.3: all three depth regimes for measurable regularly varying schedules. -/
theorem corollary23 {M : MCTSModel} {c L : ℝ → ℝ} {α : ℝ}
    (hseq : M.Scheduled c) (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s))
    (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x)
    (hα : -(1 / 2 : ℝ) < α)
    (hcBound : LocallyBounded c)
    (hInvBound : LocallyBounded (fun x => 1 / c x))
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.OptimalPathCounts (V n) (H n) (n + 1) (state n) (time n)) :
    (α < 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
      (fun n => Real.sqrt (n : ℝ) / c n)) ∧
    (α = 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
      (fun n => Real.log (n : ℝ) + DepthIntegral.critical L n)) ∧
    (1 / 2 < α → (fun n => (H n : ℝ)) =Θ[∞]
      (fun n : ℕ => Real.log (n : ℝ))) := by
  classical
  let completeCountPath (V : ℕ → ℕ) (H : ℕ) (x : ℕ) : ℕ :=
    if x ≤ H then V x else V H - (x - H)
  let capped (c : ℝ → ℝ) (x : ℝ) : ℝ :=
    min (c x) (Real.sqrt x)
  have capped_mass (c : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
      ExplorationSchedule.mass (capped c) x =
        min (ExplorationSchedule.mass c x) x := by
    simp only [ExplorationSchedule.mass, capped,
      min_mul_of_nonneg _ _ (Real.sqrt_nonneg x), Real.mul_self_sqrt hx]
  have reciprocal_integral_rectangles_of_integrable {f : ℝ → ℝ}
      (hi : IntegrableFromOne (fun x => 1 / f x)) (hp : ∀ x ≥ 1, 0 < f x)
      {a b A : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (_hA : 0 < A)
      (hmono : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → f x ≤ A * f y) :
      (b - a) / (A * f b) ≤ (∫ x in a..b, 1 / f x) ∧
        (∫ x in a..b, 1 / f x) ≤ A * (b - a) / f a := by
    have hlow := intervalIntegral.integral_mono_on (μ := volume) hab
      (continuous_const.intervalIntegrable a b :
        IntervalIntegrable (fun _ : ℝ => 1 / (A * f b)) volume a b)
      (hi a b ha hab)
      (fun x hx => one_div_le_one_div_of_le (hp x (ha.trans hx.1))
        (hmono x hx b ⟨hab, le_rfl⟩ hx.2))
    have hupp := intervalIntegral.integral_mono_on (μ := volume) hab
      (hi a b ha hab)
      (continuous_const.intervalIntegrable a b :
        IntervalIntegrable (fun _ : ℝ => A / f a) volume a b)
      (fun x hx => by
        apply (div_le_div_iff₀ (hp x (ha.trans hx.1)) (hp a ha)).2
        simpa using hmono a ⟨le_rfl, hab⟩ x hx hx.1)
    constructor
    · simpa [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc] using hlow
    · simpa [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc] using hupp
  have locallyBounded_div_sqrt {f : ℝ → ℝ} (hb : LocallyBounded f) :
      LocallyBounded (fun x => f x / Real.sqrt x) := by
    intro b hb1
    obtain ⟨C, hC⟩ := (hb b hb1).exists_norm_le
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, Set.forall_mem_image.mpr fun x hx => ?_⟩
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
    have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx.1
    exact (div_le_self (abs_nonneg _) hs).trans
      (by simpa using hC _ (Set.mem_image_of_mem _ hx))
  have regularlyVarying_ratio_limit {L : ℝ → ℝ} {ρ a : ℝ}
      (hr : ∀ a : ℝ, 0 < a →
        Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1)) (ha : 0 < a) :
      Tendsto (fun x : ℝ => ((a * x) ^ ρ * L (a * x)) / (x ^ ρ * L x))
        atTop (𝓝 (a ^ ρ)) := by
    have hh := (hr a ha).const_mul (a ^ ρ)
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.mul_rpow ha.le hx.le]
    field_simp [(Real.rpow_pos_of_pos hx ρ).ne']
  have regularlyVarying_almost_monotone {L : ℝ → ℝ} {ρ : ℝ}
      (hm : AEMeasurable L volume) (hp : ∀ x ≥ 1, 0 < L x)
      (hr : ∀ a : ℝ, 0 < a →
        Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
      (hρ : 0 < ρ) :
      ∃ M ≥ (1 : ℝ), ∀ x ≥ M, ∀ y ≥ x,
        x ^ ρ * L x ≤ 3 * (y ^ ρ * L y) := by
    have aemeasurable_scale_right {L : ℝ → ℝ}
        (hm : AEMeasurable L volume) (a : ℝ) : AEMeasurable (fun u => L (u * a)) volume := by
      by_cases ha : a = 0
      · simp only [ha, mul_zero]
        exact aemeasurable_const
      · simpa [Function.comp_def, smul_eq_mul, mul_comm] using
          hm.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul volume ha)
    have exists_outside_dilated_sets {s t : Set ℝ} {a : ℝ}
        (hs : volume s ≤ ENNReal.ofReal (1 / 4 : ℝ))
        (ht : volume t ≤ ENNReal.ofReal (1 / 4 : ℝ))
        (ha : 1 ≤ a) (ha' : a ≤ 2) :
        ∃ u ∈ Set.Icc (2 : ℝ) 4, u ∉ s ∧ u / a ∉ t := by
      have hap : 0 < a := by linarith
      let v := (fun u : ℝ => a⁻¹ * u) ⁻¹' t
      have hv : volume v ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
        dsimp [v]
        rw [Real.volume_preimage_mul_left (inv_ne_zero hap.ne')]
        simp only [inv_inv, abs_of_pos hap]
        calc
          ENNReal.ofReal a * volume t ≤ ENNReal.ofReal 2 * ENNReal.ofReal (1 / 4 : ℝ) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal ha') ht
          _ = ENNReal.ofReal (1 / 2 : ℝ) := by rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
      have hnot : ¬ Set.Icc (2 : ℝ) 4 ⊆ s ∪ v := by
        intro hsub
        have hm := (measure_mono hsub).trans ((measure_union_le s v).trans (add_le_add hs hv))
        rw [Real.volume_Icc, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
          ENNReal.ofReal_le_ofReal_iff (by norm_num)] at hm
        norm_num at hm
      obtain ⟨u, hu, huv⟩ := Set.not_subset.mp hnot
      refine ⟨u, hu, fun h => huv (Or.inl h), ?_⟩
      intro h
      apply huv (Or.inr ?_)
      simpa [v, div_eq_mul_inv, mul_comm] using h
    have slowlyVarying_seq_comparable {L : ℝ → ℝ}
        (hm : AEMeasurable L volume) (hp : ∀ x ≥ 1, 0 < L x)
        (hr : ∀ a : ℝ, 0 < a →
          Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
        {x y : ℕ → ℝ} (hx : Tendsto x atTop atTop)
        (hxy : ∀ n, x n ≤ y n ∧ y n ≤ 2 * x n) :
        ∀ᶠ n in atTop, L (x n) / 3 ≤ L (y n) ∧ L (y n) ≤ 3 * L (x n) := by
      have hy : Tendsto y atTop atTop :=
        tendsto_atTop_mono' atTop (Filter.Eventually.of_forall fun n => (hxy n).1) hx
      let f : ℕ → ℝ → ℝ := fun n u => L (u * x n) / L (x n)
      let g : ℕ → ℝ → ℝ := fun n u => L (u * y n) / L (y n)
      have hf : ∀ n, AEMeasurable (f n) volume := fun n =>
        (aemeasurable_scale_right hm (x n)).div_const _
      have hg : ∀ n, AEMeasurable (g n) volume := fun n =>
        (aemeasurable_scale_right hm (y n)).div_const _
      have hflim : ∀ᵐ u ∂volume, u ∈ Set.Icc (1 : ℝ) 4 →
          Tendsto (fun n => f n u) atTop (𝓝 1) := by
        apply Filter.Eventually.of_forall
        intro u hu
        exact (hr u (by linarith [hu.1])).comp hx
      have hglim : ∀ᵐ u ∂volume, u ∈ Set.Icc (1 : ℝ) 4 →
          Tendsto (fun n => g n u) atTop (𝓝 1) := by
        apply Filter.Eventually.of_forall
        intro u hu
        exact (hr u (by linarith [hu.1])).comp hy
      obtain ⟨s, _, _, hsvol, hsf⟩ := tendstoUniformlyOn_of_ae_tendsto
        (μ := volume.completion)
        (fun n => (hf n).nullMeasurable.measurable'.stronglyMeasurable)
        stronglyMeasurable_const
        (show MeasurableSet (Set.Icc (1 : ℝ) 4) from measurableSet_Icc).nullMeasurableSet
        (by simp : volume (Set.Icc (1 : ℝ) 4) ≠ ∞) hflim (by norm_num : (0 : ℝ) < 1 / 4)
      obtain ⟨t, _, _, htvol, htg⟩ := tendstoUniformlyOn_of_ae_tendsto
        (μ := volume.completion)
        (fun n => (hg n).nullMeasurable.measurable'.stronglyMeasurable)
        stronglyMeasurable_const
        (show MeasurableSet (Set.Icc (1 : ℝ) 4) from measurableSet_Icc).nullMeasurableSet
        (by simp : volume (Set.Icc (1 : ℝ) 4) ≠ ∞) hglim (by norm_num : (0 : ℝ) < 1 / 4)
      have hsf' := (Metric.tendstoUniformlyOn_iff.mp hsf) (1 / 2) (by norm_num)
      have htg' := (Metric.tendstoUniformlyOn_iff.mp htg) (1 / 2) (by norm_num)
      filter_upwards [hsf', htg', hx.eventually (eventually_ge_atTop (1 : ℝ))] with n hfn hgn hxn
      have hxp : 0 < x n := by linarith
      have hyp : 0 < y n := lt_of_lt_of_le hxp (hxy n).1
      have ha : 1 ≤ y n / x n := (le_div_iff₀ hxp).2 (by simpa using (hxy n).1)
      have ha' : y n / x n ≤ 2 := (div_le_iff₀ hxp).2 (hxy n).2
      obtain ⟨u, hu, hus, hut⟩ := exists_outside_dilated_sets hsvol htvol ha ha'
      have haup : 0 < y n / x n := div_pos hyp hxp
      have hu' : u / (y n / x n) ∈ Set.Icc (1 : ℝ) 4 := by
        constructor
        · apply (le_div_iff₀ haup).2
          nlinarith [hu.1]
        · apply (div_le_iff₀ haup).2
          nlinarith [hu.2]
      have huf := hfn u ⟨⟨by linarith [hu.1], hu.2⟩, hus⟩
      have hug := hgn (u / (y n / x n)) ⟨hu', hut⟩
      rw [Real.dist_eq, abs_lt] at huf hug
      have harg : u / (y n / x n) * y n = u * x n := by
        field_simp
      have hlx : 0 < L (x n) := hp _ hxn
      have hly : 0 < L (y n) := hp _ (hxn.trans (hxy n).1)
      change -(1 / 2 : ℝ) < 1 - L (u * x n) / L (x n) ∧
        1 - L (u * x n) / L (x n) < 1 / 2 at huf
      change -(1 / 2 : ℝ) < 1 - L (u / (y n / x n) * y n) / L (y n) ∧
        1 - L (u / (y n / x n) * y n) / L (y n) < 1 / 2 at hug
      rw [harg] at hug
      have hfxlo : L (x n) / 2 < L (u * x n) := by
        have := (lt_div_iff₀ hlx).1 (show (1 / 2 : ℝ) < L (u * x n) / L (x n) by linarith [huf.2])
        linarith
      have hfxhi : L (u * x n) < 3 * L (x n) / 2 := by
        have := (div_lt_iff₀ hlx).1 (show L (u * x n) / L (x n) < (3 / 2 : ℝ) by linarith [huf.1])
        linarith
      have hgylo : L (y n) / 2 < L (u * x n) := by
        have := (lt_div_iff₀ hly).1 (show (1 / 2 : ℝ) < L (u * x n) / L (y n) by linarith [hug.2])
        linarith
      have hgyhi : L (u * x n) < 3 * L (y n) / 2 := by
        have := (div_lt_iff₀ hly).1 (show L (u * x n) / L (y n) < (3 / 2 : ℝ) by linarith [hug.1])
        linarith
      constructor <;> linarith
    have slowlyVarying_dyadic_comparable {L : ℝ → ℝ}
        (hm : AEMeasurable L volume) (hp : ∀ x ≥ 1, 0 < L x)
        (hr : ∀ a : ℝ, 0 < a →
          Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1)) :
        ∃ M ≥ (1 : ℝ), ∀ x ≥ M, ∀ y, x ≤ y → y ≤ 2 * x →
          L x / 3 ≤ L y ∧ L y ≤ 3 * L x := by
      by_contra h
      push Not at h
      have hex : ∀ n : ℕ, ∃ x ≥ max 1 (n : ℝ), ∃ y,
          x ≤ y ∧ y ≤ 2 * x ∧ ¬ (L x / 3 ≤ L y ∧ L y ≤ 3 * L x) := by
        intro n
        obtain ⟨x, hxn, y, hxy, hyx, hbad⟩ := h (max 1 (n : ℝ)) (le_max_left _ _)
        exact ⟨x, hxn, y, hxy, hyx, fun hh => (hbad hh.1).not_ge hh.2⟩
      choose x hx y hxy hyx hbad using hex
      have hxt : Tendsto x atTop atTop :=
        tendsto_atTop_mono' atTop
          (Filter.Eventually.of_forall fun n => (le_max_right _ _).trans (hx n))
          tendsto_natCast_atTop_atTop
      have hcomp := slowlyVarying_seq_comparable hm hp hr hxt (fun n => ⟨hxy n, hyx n⟩)
      obtain ⟨n, hn⟩ := hcomp.exists
      exact hbad n hn
    obtain ⟨M, hM, hcomp⟩ := slowlyVarying_dyadic_comparable hm hp hr
    have hlim := regularlyVarying_ratio_limit (ρ := ρ) hr (by norm_num : (0 : ℝ) < 2)
    have he := hlim.eventually_const_le (Real.one_lt_rpow (by norm_num) hρ)
    obtain ⟨D, hD⟩ := eventually_atTop.mp he
    let T := max M D
    have hT : 1 ≤ T := hM.trans (le_max_left _ _)
    have hdoubling : ∀ x ≥ T, x ^ ρ * L x ≤ (2 * x) ^ ρ * L (2 * x) := by
      intro x hx
      have hxp : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hT.trans hx)
      have hf : 0 < x ^ ρ * L x := mul_pos (Real.rpow_pos_of_pos hxp _) (hp _ (hT.trans hx))
      have := (le_div_iff₀ hf).1 (hD x ((le_max_right _ _).trans hx))
      simpa using this
    refine ⟨T, hT, ?_⟩
    intro x hx y hxy
    have hxp : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hT.trans hx)
    have hyp : 0 < y := hxp.trans_le hxy
    obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near
      ((le_div_iff₀ hxp).2 (by simpa using hxy)) (by norm_num : (1 : ℝ) < 2)
    have hiter : Monotone (fun n : ℕ => ((2 : ℝ) ^ n * x) ^ ρ * L ((2 : ℝ) ^ n * x)) := by
      apply monotone_nat_of_le_succ
      intro n
      have hbase : T ≤ (2 : ℝ) ^ n * x :=
        hx.trans (le_mul_of_one_le_left hxp.le (one_le_pow₀ (by norm_num)))
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        hdoubling ((2 : ℝ) ^ n * x) hbase
    have hkx : (2 : ℝ) ^ k * x ≤ y := (le_div_iff₀ hxp).1 hk
    have hykx : y ≤ 2 * ((2 : ℝ) ^ k * x) := by
      have := (div_lt_iff₀ hxp).1 hk'
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using this.le
    have hbase : M ≤ (2 : ℝ) ^ k * x := by
      have hh : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      exact (le_max_left _ _).trans (hx.trans (by nlinarith))
    have hL := (hcomp ((2 : ℝ) ^ k * x) hbase y hkx hykx).1
    have hL' : L ((2 : ℝ) ^ k * x) ≤ 3 * L y := by linarith
    have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ k * x) hkx hρ.le
    calc
      x ^ ρ * L x ≤ ((2 : ℝ) ^ k * x) ^ ρ * L ((2 : ℝ) ^ k * x) := by
        simpa using hiter (Nat.zero_le k)
      _ ≤ y ^ ρ * (3 * L y) := mul_le_mul hrpow hL' (hp _ (hM.trans hbase)).le
        (Real.rpow_pos_of_pos hyp _).le
      _ = 3 * (y ^ ρ * L y) := by ring
  let tailExtend (f : ℝ → ℝ) (x : ℝ) : ℝ :=
    if 1 ≤ x then f x else 1
  have tailExtend_eq {f : ℝ → ℝ} {x : ℝ} (hx : 1 ≤ x) :
      tailExtend f x = f x := by simp [tailExtend, hx]
  have aemeasurable_tailExtend {f : ℝ → ℝ}
      (hf : AEMeasurable f (volume.restrict (Set.Ici (1 : ℝ)))) :
      AEMeasurable (tailExtend f) volume := by
    classical
    simpa only [tailExtend, Set.piecewise, Set.mem_Ici] using
      (AEStronglyMeasurable.piecewise measurableSet_Ici hf.aestronglyMeasurable
        aestronglyMeasurable_const).aemeasurable
  have integrableFromOne_of_aemeasurable_restrict {g : ℝ → ℝ}
      (hm : AEMeasurable g (volume.restrict (Set.Ici (1 : ℝ))))
      (hb : LocallyBounded g) : IntegrableFromOne g := by
    intro a b ha hab
    obtain ⟨C, hC⟩ := (hb b (ha.trans hab)).exists_norm_le
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
    apply IntegrableOn.of_bound measure_Icc_lt_top
      (hm.mono_measure (Measure.restrict_mono
        (fun x hx => ha.trans hx.1) le_rfl)).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hC _ (Set.mem_image_of_mem _ ⟨ha.trans hx.1, hx.2⟩)
  have exploration_integrable {c : ℝ → ℝ}
      (hm : AEMeasurable c (volume.restrict (Set.Ici (1 : ℝ))))
      (hb : LocallyBounded (fun x => 1 / c x)) :
      IntegrableFromOne (fun x => 1 / ExplorationSchedule.mass c x) := by
    apply integrableFromOne_of_aemeasurable_restrict
    · exact aemeasurable_const.div (hm.mul Real.continuous_sqrt.measurable.aemeasurable)
    · simpa only [ExplorationSchedule.mass, div_mul_eq_div_div] using locallyBounded_div_sqrt hb
  have reciprocal_identity_integrable : IntegrableFromOne (fun x : ℝ => 1 / x) := by
    intro a b ha hab
    have hc : ContinuousOn (fun x : ℝ => 1 / x) (Set.Icc a b) :=
      continuousOn_const.div continuousOn_id
        (fun x hx => (show 0 < x by linarith [hx.1]).ne')
    exact hc.intervalIntegrable_of_Icc hab
  have saturated_depth_weak {c : ℝ → ℝ}
      (hi : IntegrableFromOne (fun x => 1 / ExplorationSchedule.mass c x))
      (hp : ∀ x ≥ 1, 0 < c x)
      (hbound : c =O[∞] Real.sqrt) :
      DepthIntegral.saturated c =Θ[∞] DepthIntegral.exploration c := by
    have hip : ∀ x ≥ 1, 0 < 1 / ExplorationSchedule.mass c x := fun x hx =>
      one_div_pos.mpr (mul_pos (hp x hx) (Real.sqrt_pos.2 (by linarith)))
    obtain ⟨B, hB, hbig⟩ := hbound.exists_pos
    have ho := positive_integral_comparison_of_integrable
      reciprocal_identity_integrable hi (fun x hx => one_div_pos.mpr (by linarith)) hip hB (by
        filter_upwards [hbig.bound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
        have hcpos := hp x hx1
        have hx0 : 0 < x := by linarith
        simp only [Real.norm_eq_abs, abs_of_nonneg hcpos.le,
          abs_of_nonneg (Real.sqrt_nonneg _)] at hx
        have hh := mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg x)
        rw [mul_assoc, Real.mul_self_sqrt hx0.le] at hh
        dsimp [ExplorationSchedule.mass]
        rw [mul_one_div]
        exact (div_le_div_iff₀ hx0 (mul_pos hcpos (Real.sqrt_pos.2 hx0))).2 (by nlinarith))
    have hlog : (fun n : ℕ => Real.log (n : ℝ)) =O[∞] DepthIntegral.exploration c :=
      ho.congr' (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa [MCTSCharacterization.integralPotential] using integral_one_div_of_pos
          (by norm_num : (0 : ℝ) < 1)
          (show (0 : ℝ) < n by exact_mod_cast Nat.zero_lt_of_lt hn)) Filter.EventuallyEq.rfl
    apply nonnegative_add_theta_right _ _ hlog
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact Real.log_nonneg (by exact_mod_cast hn)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact intervalIntegral.integral_nonneg (by exact_mod_cast hn)
        (fun x hx => (hip x hx.1).le)
  have saturated_depth_strong {c : ℝ → ℝ}
      (hi : IntegrableFromOne (fun x => 1 / ExplorationSchedule.mass c x))
      (hp : ∀ x ≥ 1, 0 < c x)
      (hbound : Real.sqrt =O[∞] c) :
      DepthIntegral.saturated c =Θ[∞] (fun n : ℕ => Real.log (n : ℝ)) := by
    have hip : ∀ x ≥ 1, 0 < 1 / ExplorationSchedule.mass c x := fun x hx =>
      one_div_pos.mpr (mul_pos (hp x hx) (Real.sqrt_pos.2 (by linarith)))
    obtain ⟨B, hB, hbig⟩ := hbound.exists_pos
    have ho := positive_integral_comparison_of_integrable hi
      reciprocal_identity_integrable hip (fun x hx => one_div_pos.mpr (by linarith)) hB (by
        filter_upwards [hbig.bound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
        have hcpos := hp x hx1
        have hx0 : 0 < x := by linarith
        simp only [Real.norm_eq_abs, abs_of_nonneg hcpos.le,
          abs_of_nonneg (Real.sqrt_nonneg _)] at hx
        have hh := mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg x)
        rw [Real.mul_self_sqrt hx0.le] at hh
        dsimp [ExplorationSchedule.mass]
        rw [mul_one_div]
        exact (div_le_div_iff₀ (mul_pos hcpos (Real.sqrt_pos.2 hx0)) hx0).2 (by nlinarith))
    have hlog : DepthIntegral.exploration c =O[∞] (fun n : ℕ => Real.log (n : ℝ)) :=
      ho.congr' Filter.EventuallyEq.rfl (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa [MCTSCharacterization.integralPotential] using integral_one_div_of_pos
          (by norm_num : (0 : ℝ) < 1)
          (show (0 : ℝ) < n by exact_mod_cast Nat.zero_lt_of_lt hn))
    have hh := nonnegative_add_theta_right (f := DepthIntegral.exploration c)
      (g := fun n : ℕ => Real.log (n : ℝ)) (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        exact intervalIntegral.integral_nonneg (by exact_mod_cast hn)
          (fun x hx => (hip x hx.1).le)) (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        exact Real.log_nonneg (by exact_mod_cast hn)) hlog
    simpa only [DepthIntegral.saturated, add_comm] using hh
  have regular_variation_positive {c L : ℝ → ℝ} {α : ℝ}
      (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = x ^ α * L x) :
      ∀ x ≥ 1, 0 < c x := by
    intro x hx
    rw [hform x hx]
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (hL.positive x hx)
  have regular_variation_doubling_limit_measurable {c L : ℝ → ℝ} {α : ℝ}
      (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = x ^ α * L x) :
      Tendsto (fun x : ℝ => c (2 * x) / c x) atTop (𝓝 ((2 : ℝ) ^ α)) := by
    have regular_variation_ratio_limit {c L : ℝ → ℝ} {α : ℝ}
        (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = x ^ α * L x)
        (a : ℝ) (ha : 0 < a) :
        Tendsto (fun x : ℝ => c (a * x) / c x) atTop (𝓝 (a ^ α)) := by
      have hlim := regularlyVarying_ratio_limit (ρ := α) hL.ratio ha
      apply hlim.congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ),
        (tendsto_id.const_mul_atTop ha).eventually (eventually_ge_atTop (1 : ℝ))]
        with x hx hax
      rw [hform x hx, hform (a * x) hax]
    exact regular_variation_ratio_limit hL hform 2 (by norm_num)
  let generalSchedule_of_regularVariation {c L : ℝ → ℝ} {α : ℝ}
      (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = x ^ α * L x)
      (hα : -(1 / 2 : ℝ) < α)
      (hiBound : LocallyBounded (fun x => 1 / c x)) :
      Assumption.GeneralExplorationSchedule c := by
    have regularlyVarying_fraction_comparable {L : ℝ → ℝ} {ρ : ℝ}
        (hm : AEMeasurable L volume) (hp : ∀ x ≥ 1, 0 < L x)
        (hr : ∀ a : ℝ, 0 < a →
          Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1))
        (hρ : 0 < ρ) {η : ℝ} (hη : 0 < η) (_hη' : η < 1) :
        ∃ R > (0 : ℝ), ∃ m, ∀ x ≥ m, ∀ y, η * x ≤ y → y ≤ x →
          x ^ ρ * L x ≤ R * (y ^ ρ * L y) := by
      obtain ⟨M, hM, hmono⟩ := regularlyVarying_almost_monotone hm hp hr hρ
      have hηr : 0 < η ^ ρ := Real.rpow_pos_of_pos hη _
      have hlim := regularlyVarying_ratio_limit (ρ := ρ) hr hη
      obtain ⟨D, hD⟩ := eventually_atTop.mp
        (hlim.eventually_const_le (show η ^ ρ / 2 < η ^ ρ by linarith))
      refine ⟨6 / η ^ ρ, div_pos (by norm_num) hηr, max 1 (max D (M / η)), ?_⟩
      intro x hx y hxy _hyx
      have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
      have hxD : D ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
      have hxM : M / η ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
      have hηxM : M ≤ η * x := by
        have := (div_le_iff₀ hη).1 hxM
        simpa [mul_comm] using this
      have hxp : 0 < x := by linarith
      have hFx : 0 < x ^ ρ * L x := mul_pos (Real.rpow_pos_of_pos hxp _) (hp _ hx1)
      have hhalf := (le_div_iff₀ hFx).1 (hD x hxD)
      have hmy := hmono (η * x) hηxM y hxy
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hηr).2
      nlinarith [hhalf.trans hmy]
    have regular_variation_measurable {c L : ℝ → ℝ} {α : ℝ}
        (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = x ^ α * L x) :
        AEMeasurable c (volume.restrict (Set.Ici (1 : ℝ))) := by
      have hm : AEMeasurable (fun x => x ^ α * L x)
          (volume.restrict (Set.Ici (1 : ℝ))) :=
        (measurable_id.pow_const α).aemeasurable.mul hL.measurable
      apply hm.congr
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      exact (hform x hx).symm
    have slowlyVarying_tailExtend_ratio {L : ℝ → ℝ} (hL : SlowlyVarying L)
        (a : ℝ) (ha : 0 < a) :
        Tendsto (fun x : ℝ => tailExtend L (a * x) / tailExtend L x) atTop (𝓝 1) := by
      apply (hL.ratio a ha).congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ),
        (tendsto_id.const_mul_atTop ha).eventually (eventually_ge_atTop (1 : ℝ))]
        with x hx hax
      change 1 ≤ a * x at hax
      rw [tailExtend_eq hx, tailExtend_eq hax]
    let ρ := α + 1 / 2
    have hρ : 0 < ρ := by dsimp [ρ]; linarith
    have hm := aemeasurable_tailExtend hL.measurable
    have hp : ∀ x ≥ 1, 0 < tailExtend L x := fun x hx => by
      simpa [tailExtend_eq hx] using hL.positive x hx
    have hr := slowlyVarying_tailExtend_ratio hL
    have hmass : ∀ x ≥ 1, ExplorationSchedule.mass c x = x ^ ρ * tailExtend L x := by
      intro x hx
      rw [tailExtend_eq hx]
      exact rpow_form_mul_sqrt hform x hx
    let hmon := regularlyVarying_almost_monotone hm hp hr hρ
    let T := hmon.choose
    have hT : 1 ≤ T := hmon.choose_spec.1
    have hmono := hmon.choose_spec.2
    let m := (exists_nat_ge T).choose
    have hmT : T ≤ (m : ℝ) := (exists_nat_ge T).choose_spec
    have hm1 : 1 ≤ m := by exact_mod_cast hT.trans hmT
    refine {
      threshold := m
      threshold_pos := hm1
      positive := regular_variation_positive hL hform
      integrable := exploration_integrable (regular_variation_measurable hL hform) hiBound
      A := 3
      A_one := by norm_num
      monotone := ?_
      scaling := ?_
    }
    · intro x y hx hxy
      have hx1 : 1 ≤ x := (hT.trans hmT).trans hx
      rw [hmass x hx1, hmass y (hx1.trans hxy)]
      exact hmono x (hmT.trans hx) y hxy
    · intro η hη hη'
      obtain ⟨R, hR, D, hD⟩ := regularlyVarying_fraction_comparable hm hp hr hρ hη hη'
      obtain ⟨k, hk⟩ := exists_nat_ge (max D (1 / η))
      refine ⟨R, hR, k, ?_⟩
      intro x y hx hxy hyx
      have hxD : D ≤ x := (le_max_left _ _).trans (hk.trans hx)
      have hxη : 1 / η ≤ x := (le_max_right _ _).trans (hk.trans hx)
      have hηx1 : 1 ≤ η * x := by
        have := (div_le_iff₀ hη).1 hxη
        simpa [mul_comm] using this
      have hy1 : 1 ≤ y := hηx1.trans hxy
      rw [hmass x (hy1.trans hyx), hmass y hy1]
      exact hD x hxD y hxy hyx
  have coefficient_div_sqrt_form {c L : ℝ → ℝ} {α : ℝ}
      (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x) :
      ∀ x ≥ 1, c x / Real.sqrt x = Real.rpow x (α - 1 / 2) * L x := by
    intro x hx
    rw [hform x hx]
    change x ^ α * L x / Real.sqrt x = x ^ (α - 1 / 2) * L x
    rw [Real.rpow_sub (by linarith : 0 < x), ← Real.sqrt_eq_rpow]
    ring
  have regular_variation_positive_lower {c L : ℝ → ℝ} {α : ℝ}
      (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = x ^ α * L x) (hα : 0 < α) :
      ∃ δ > 0, ∀ᶠ x : ℝ in atTop, δ ≤ c x := by
    have hr : ∀ a : ℝ, 0 < a →
        Tendsto (fun x => tailExtend L (a * x) /
          tailExtend L x) atTop (𝓝 1) := by
      intro a ha
      apply (hL.ratio a ha).congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ),
        (tendsto_id.const_mul_atTop ha).eventually (eventually_ge_atTop (1 : ℝ))]
        with x hx hax
      change 1 ≤ a * x at hax
      rw [tailExtend_eq hx, tailExtend_eq hax]
    obtain ⟨M, hM, hmono⟩ := regularlyVarying_almost_monotone
      (aemeasurable_tailExtend hL.measurable)
      (fun x hx => by
        simpa only [tailExtend_eq hx] using hL.positive x hx) hr hα
    have hp : 0 < M ^ α * L M :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (hL.positive M hM)
    refine ⟨M ^ α * L M / 3, div_pos hp (by norm_num), ?_⟩
    filter_upwards [eventually_ge_atTop M] with x hx
    have hh := hmono M le_rfl x hx
    rw [tailExtend_eq hM,
      tailExtend_eq (hM.trans hx), ← hform x (hM.trans hx)] at hh
    linarith
  have measurable_regular_variation_subcritical {c L : ℝ → ℝ} {α : ℝ}
      (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x)
      (_hb : LocallyBounded c) (hα : α < 1 / 2) : c =O[∞] Real.sqrt := by
    have hiL : SlowlyVarying (fun x => 1 / L x) := by
      refine ⟨aemeasurable_const.div hL.measurable,
        fun x hx => one_div_pos.mpr (hL.positive x hx), ?_⟩
      intro a ha
      simpa only [one_div, inv_div_inv, inv_one, inv_div] using
        (hL.ratio a ha).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hiform : ∀ x ≥ 1, Real.sqrt x / c x = x ^ (1 / 2 - α) * (1 / L x) := by
      intro x hx
      rw [hform x hx]
      change Real.sqrt x / (x ^ α * L x) = _
      rw [Real.rpow_sub (by linarith : 0 < x), ← Real.sqrt_eq_rpow]
      ring
    obtain ⟨δ, hδ, hbound⟩ := regular_variation_positive_lower hiL hiform (by linarith)
    apply Asymptotics.IsBigO.of_bound (1 / δ)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hc := regular_variation_positive hL hform x hx1
    have hh := (le_div_iff₀ hc).1 hx
    simp only [Real.norm_eq_abs, abs_of_pos hc, abs_of_nonneg (Real.sqrt_nonneg x)]
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hh)
  have measurable_exploration_subcritical {c L : ℝ → ℝ} {α : ℝ}
      (hc : Assumption.GeneralExplorationSchedule c)
      (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x)
      (hb : c =O[∞] Real.sqrt) (hα : α < 1 / 2) :
      DepthIntegral.exploration c =Θ[∞] (fun n : ℕ => Real.sqrt (n : ℝ) / c n) := by
    have reciprocal_integral_rate {f : ℝ → ℝ} {M q A κ : ℝ}
        (hi : IntegrableFromOne (fun x => 1 / f x)) (hp : ∀ x ≥ 1, 0 < f x)
        (hM : 1 ≤ M) (hq : 0 < q) (hq2 : q < 2) (hA : 0 < A) (hκ : 0 < κ)
        (hmono : ∀ x ≥ M, ∀ y ≥ x, f x ≤ A * f y)
        (hdouble : ∀ x ≥ M, f (2 * x) ≤ q * f x)
        (hroot : ∀ᶠ n : ℕ in atTop, κ * f n ≤ n) :
        (fun n : ℕ => integralPotential (fun x => 1 / f x) n) =Θ[∞]
          (fun n => (n : ℝ) / f n) := by
      have reciprocal_integral_halving {f : ℝ → ℝ} {M q A n : ℝ}
          (hi : IntegrableFromOne (fun x => 1 / f x))
          (hp : ∀ x ≥ 1, 0 < f x)
          (hM : 1 ≤ M) (hq : 0 < q) (hA : 0 < A) (hn : 2 * M ≤ n)
          (hmono : ∀ x ≥ M, ∀ y ≥ x, f x ≤ A * f y)
          (hdouble : ∀ x ≥ M, f (2 * x) ≤ q * f x) :
          (2 - q) * integralPotential (fun x => 1 / f x) n ≤
            2 * integralPotential (fun x => 1 / f x) M + A * q * (n / f n) := by
        let g := fun x => 1 / f x
        have hgp : ∀ x ≥ 1, 0 ≤ g x := fun x hx => (one_div_pos.mpr (hp x hx)).le
        have hn1 : 1 ≤ n := by linarith
        have hhalf : M ≤ n / 2 := by linarith
        have hhalf1 : 1 ≤ n / 2 := hM.trans hhalf
        have htwoM : 1 ≤ 2 * M := by linarith
        have hscaled : IntervalIntegrable (fun x => g (x / 2)) volume (2 * M) n := by
          convert (hi M (n / 2) hM hhalf).comp_mul_right (c := (1 / 2 : ℝ)) using 1 <;>
            simp [g, div_eq_mul_inv, mul_comm]
        have hcomp := intervalIntegral.integral_mono_on (μ := volume) hn hscaled
          ((hi (2 * M) n htwoM hn).const_mul q)
          (fun x hx => by
            have hxm : M ≤ x / 2 := by linarith [hx.1]
            have hd : f x ≤ q * f (x / 2) := by
              simpa only [show 2 * (x / 2) = x by ring] using hdouble (x / 2) hxm
            have hfx := hp x (htwoM.trans hx.1)
            have hfh := hp (x / 2) (hM.trans hxm)
            dsimp [g]
            rw [← mul_div_assoc, mul_one]
            apply (div_le_div_iff₀ hfh hfx).2
            simpa [mul_comm] using hd)
        have hscale : (∫ x in 2 * M..n, g (x / 2)) = 2 * (∫ x in M..n / 2, g x) := by
          simp [intervalIntegral.integral_comp_div, smul_eq_mul]
        rw [hscale, intervalIntegral.integral_const_mul] at hcomp
        have hseg := intervalIntegral.integral_interval_sub_left (μ := volume)
          (hi 1 n le_rfl hn1) (hi 1 (2 * M) le_rfl htwoM)
        change integralPotential g n - integralPotential g (2 * M) = _ at hseg
        have htwo_nonneg : 0 ≤ integralPotential g (2 * M) :=
          intervalIntegral.integral_nonneg htwoM (fun x hx => hgp x hx.1)
        have hmain : 2 * (∫ x in M..n / 2, g x) ≤ q * integralPotential g n := by
          have hle : (∫ x in 2 * M..n, g x) ≤ integralPotential g n := by linarith
          exact hcomp.trans (mul_le_mul_of_nonneg_left hle hq.le)
        have hrect := reciprocal_integral_rectangles_of_integrable hi hp hhalf1
          (by linarith : n / 2 ≤ n) hA
          (fun x hx y _ hxy => hmono x (hhalf.trans hx.1) y hxy)
        have hd : f n ≤ q * f (n / 2) := by
          simpa only [show 2 * (n / 2) = n by ring] using hdouble (n / 2) hhalf
        have htail : (∫ x in n / 2..n, g x) ≤ A * q / 2 * (n / f n) := by
          apply hrect.2.trans
          have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ A * n by positivity)
          rw [← mul_div_assoc]
          apply (div_le_div_iff₀ (hp _ hhalf1) (hp _ hn1)).2
          nlinarith
        have hsplit₁ := intervalIntegral.integral_interval_sub_left (μ := volume)
          (hi 1 (n / 2) le_rfl hhalf1) (hi 1 M le_rfl hM)
        change integralPotential g (n / 2) - integralPotential g M = _ at hsplit₁
        have hsplit₂ := intervalIntegral.integral_interval_sub_left (μ := volume)
          (hi 1 n le_rfl hn1) (hi 1 (n / 2) le_rfl hhalf1)
        change integralPotential g n - integralPotential g (n / 2) = _ at hsplit₂
        change (2 - q) * integralPotential g n ≤
          2 * integralPotential g M + A * q * (n / f n)
        nlinarith
      let g := fun x => 1 / f x
      let K := integralPotential g M
      have hK : 0 ≤ K :=
        intervalIntegral.integral_nonneg hM (fun x hx => (one_div_pos.mpr (hp x hx.1)).le)
      have hlarge : ∀ᶠ n : ℕ in atTop, 2 * M ≤ (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
      apply theta_of_eventual_sandwich
      · filter_upwards [hlarge] with n hn
        exact intervalIntegral.integral_nonneg (by linarith : (1 : ℝ) ≤ n)
          (fun x hx => (one_div_pos.mpr (hp x hx.1)).le)
      · filter_upwards [hlarge] with n hn
        exact div_nonneg (by positivity) (hp n (by linarith)).le
      · refine ⟨(2 * K / κ + A * q) / (2 - q),
          div_pos (add_pos_of_nonneg_of_pos (div_nonneg (by positivity) hκ.le)
            (mul_pos hA hq)) (by linarith), ?_⟩
        filter_upwards [hlarge, hroot] with n hn hr
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
        have hG : κ ≤ (n : ℝ) / f n := (le_div_iff₀ (hp n hn1)).2 hr
        have hKG : 2 * K ≤ (2 * K / κ) * ((n : ℝ) / f n) := by
          have hh := mul_le_mul_of_nonneg_left hG (div_nonneg (by positivity : 0 ≤ 2 * K) hκ.le)
          simpa [div_mul_cancel₀ _ hκ.ne'] using hh
        have hself := reciprocal_integral_halving hi hp hM hq hA hn hmono hdouble
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (show 0 < 2 - q by linarith)).2
        dsimp [K, g] at hKG ⊢
        nlinarith
      · refine ⟨1 / (2 * A), by positivity, ?_⟩
        filter_upwards [hlarge] with n hn
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
        have hh : (1 : ℝ) ≤ (n : ℝ) / 2 := by linarith
        have hrect := reciprocal_integral_rectangles_of_integrable hi hp hh
          (by linarith : (n : ℝ) / 2 ≤ n) hA
          (fun x hx y _ hxy => hmono x (by linarith [hx.1]) y hxy)
        have hsplit := intervalIntegral.integral_interval_sub_left (μ := volume)
          (hi 1 n le_rfl hn1) (hi 1 ((n : ℝ) / 2) le_rfl hh)
        change integralPotential g n - integralPotential g ((n : ℝ) / 2) = _ at hsplit
        have hnonneg : 0 ≤ integralPotential g ((n : ℝ) / 2) :=
          intervalIntegral.integral_nonneg hh (fun x hx => (one_div_pos.mpr (hp x hx.1)).le)
        have heq : (1 / (2 * A)) * ((n : ℝ) / f n) =
            ((n : ℝ) - (n : ℝ) / 2) / (A * f n) := by ring
        rw [heq]
        dsimp [g] at hsplit hnonneg
        linarith [hrect.1]
    let f := ExplorationSchedule.mass c
    let r := Real.rpow 2 (α + 1 / 2)
    let q := (r + 2) / 2
    have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
    have hr2 : r < 2 := by
      simpa [r] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (show α + 1 / 2 < 1 by linarith)
    have hq : 0 < q := by dsimp [q]; linarith
    have hq2 : q < 2 := by dsimp [q]; linarith
    have hrq : r < q := by dsimp [q]; linarith
    have hfp : ∀ x ≥ 1, 0 < f x := fun x hx =>
      mul_pos (hc.positive x hx) (Real.sqrt_pos.2 (by linarith))
    have hlim : Tendsto (fun x : ℝ => f (2 * x) / f x) atTop (𝓝 r) :=
      regular_variation_doubling_limit_measurable hL (rpow_form_mul_sqrt hform)
    obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1
      (hlim.eventually (gt_mem_nhds hrq))
    let T : ℝ := max (hc.threshold : ℝ) (max 1 M₀)
    have hT1 : 1 ≤ T := (le_max_left 1 M₀).trans (le_max_right _ _)
    have hmono : ∀ x ≥ T, ∀ y ≥ x, f x ≤ hc.A * f y := by
      intro x hx y hxy
      exact hc.monotone x y ((le_max_left _ _).trans hx) hxy
    have hdouble : ∀ x ≥ T, f (2 * x) ≤ q * f x := by
      intro x hx
      exact ((div_lt_iff₀ (hfp x (hT1.trans hx))).1
        (hM₀ x (((le_max_right 1 M₀).trans (le_max_right _ _)).trans hx))).le
    obtain ⟨C, hC, hbound⟩ := hb.exists_pos
    have hroot : ∀ᶠ n : ℕ in atTop, (1 / C) * f n ≤ (n : ℝ) := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually hbound.bound,
        eventually_ge_atTop 1] with n hn hn1
      have hp := hc.positive n (by exact_mod_cast hn1)
      simp only [Real.norm_eq_abs, abs_of_pos hp, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
      have hh := mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg (n : ℝ))
      rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)] at hh
      dsimp [f, ExplorationSchedule.mass]
      rw [one_div_mul_eq_div]
      exact (div_le_iff₀ hC).2 (by nlinarith)
    have hi := reciprocal_integral_rate hc.integrable hfp
      hT1 hq hq2 (lt_of_lt_of_le zero_lt_one hc.A_one) (one_div_pos.mpr hC)
      hmono hdouble hroot
    have heq : (fun n : ℕ => (n : ℝ) / f n) =ᶠ[atTop]
        (fun n => Real.sqrt (n : ℝ) / c n) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
      have hsq := Real.sq_sqrt hnpos.le
      dsimp [f, ExplorationSchedule.mass]
      field_simp
      rw [hsq]
    exact hi.trans heq.isTheta
  have measurable_regular_variation_supercritical {c L : ℝ → ℝ} {α : ℝ}
      (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x)
      (_hb : LocallyBounded (fun x => 1 / c x))
      (hα : 1 / 2 < α) : Real.sqrt =O[∞] c := by
    obtain ⟨δ, hδ, hbound⟩ := regular_variation_positive_lower hL
      (coefficient_div_sqrt_form hform) (by linarith)
    apply Asymptotics.IsBigO.of_bound (1 / δ)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hc := regular_variation_positive hL hform x hx1
    have hh := (le_div_iff₀ (Real.sqrt_pos.2 (by linarith : 0 < x))).1 hx
    simp only [Real.norm_eq_abs, abs_of_pos hc, abs_of_nonneg (Real.sqrt_nonneg x)]
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hh)
  let hc := generalSchedule_of_regularVariation hL hform hα hInvBound
  -- Convert the schedule bounds into a depth estimate.
  have hdepth : (fun n => (H n : ℝ)) =Θ[∞] DepthIntegral.saturated c := by
    let capped_general_exploration_schedule {c : ℝ → ℝ}
        (hc : Assumption.GeneralExplorationSchedule c) :
        Assumption.GeneralExplorationSchedule (capped c) := by
      have hA : 0 < hc.A := lt_of_lt_of_le zero_lt_one hc.A_one
      refine {
        threshold := hc.threshold
        threshold_pos := hc.threshold_pos
        positive := fun x hx => lt_min (hc.positive x hx) (Real.sqrt_pos.2 (by linarith))
        integrable := ?_
        A := hc.A
        A_one := hc.A_one
        monotone := ?_
        scaling := ?_ }
      · intro x y hx hxy
        have hx0 : 0 ≤ x := (Nat.cast_nonneg hc.threshold).trans hx
        rw [capped_mass c hx0, capped_mass c (hx0.trans hxy),
          mul_min_of_nonneg _ _ hA.le]
        apply min_le_min (hc.monotone x y hx hxy)
        exact hxy.trans (le_mul_of_one_le_left (hx0.trans hxy) hc.A_one)
      · intro a b ha hab
        have hf := hc.integrable a b ha hab
        have hg : IntervalIntegrable (fun x : ℝ => 1 / x) MeasureTheory.volume a b :=
          (continuousOn_const.div continuousOn_id
            (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one (ha.trans hx.1))) :
            ContinuousOn (fun x : ℝ => 1 / x) (Set.Icc a b)).intervalIntegrable_of_Icc hab
        have hh : IntervalIntegrable
            (fun x => max (1 / ExplorationSchedule.mass c x) (1 / x)) MeasureTheory.volume a b :=
          ⟨hf.1.sup hg.1, hf.2.sup hg.2⟩
        apply hh.congr
        intro x hx
        rw [Set.uIoc_of_le hab] at hx
        have hx1 : 1 ≤ x := ha.trans hx.1.le
        change max (1 / ExplorationSchedule.mass c x) (1 / x) =
          1 / ExplorationSchedule.mass (capped c) x
        rw [capped_mass c (by linarith)]
        have hfpos : 0 < ExplorationSchedule.mass c x :=
          mul_pos (hc.positive x hx1) (Real.sqrt_pos.2 (by linarith))
        by_cases hh : ExplorationSchedule.mass c x ≤ x
        · rw [min_eq_left hh, max_eq_left (one_div_le_one_div_of_le hfpos hh)]
        · rw [min_eq_right (le_of_not_ge hh),
            max_eq_right (one_div_le_one_div_of_le (by linarith) (le_of_not_ge hh))]
      · intro η hη hη1
        obtain ⟨R, hR, m, hs⟩ := hc.scaling η hη hη1
        obtain ⟨mη, hmη⟩ := exists_nat_ge (1 / η)
        refine ⟨max R (1 / η), lt_of_lt_of_le hR (le_max_left _ _), max m mη, ?_⟩
        intro x y hx hxy hyx
        have hx0 : 0 ≤ x := (Nat.cast_nonneg (max m mη)).trans hx
        have hmx : (m : ℝ) ≤ x :=
          (show (m : ℝ) ≤ (max m mη : ℕ) by exact_mod_cast le_max_left m mη).trans hx
        have hmηx : 1 / η ≤ x := hmη.trans
          ((show (mη : ℝ) ≤ (max m mη : ℕ) by exact_mod_cast le_max_right m mη).trans hx)
        have hy1 : 1 ≤ y := by
          have hh := (div_le_iff₀ hη).1 hmηx
          nlinarith
        have hy0 : 0 ≤ y := (mul_nonneg hη.le hx0).trans hxy
        rw [capped_mass c hx0, capped_mass c hy0,
          mul_min_of_nonneg _ _ (show 0 ≤ max R (1 / η) by positivity)]
        apply min_le_min
        · apply (hs x y hmx hxy hyx).trans
          apply mul_le_mul_of_nonneg_right (le_max_left _ _)
          exact mul_nonneg (hc.positive y hy1).le (Real.sqrt_nonneg y)
        · have hh : x ≤ (1 / η) * y := by
            rw [one_div_mul_eq_div]
            exact (le_div_iff₀ hη).2 (by nlinarith)
          exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hy0)
    have general_capped_integral_equiv {c : ℝ → ℝ}
        (hc : Assumption.GeneralExplorationSchedule c) :
        DepthIntegral.exploration (capped c) =Θ[∞]
          DepthIntegral.saturated c := by
      let g := fun x => 1 / ExplorationSchedule.mass c x
      let e := fun x => 1 / ExplorationSchedule.mass (capped c) x
      have hg : IntegrableFromOne g := hc.integrable
      have he : IntegrableFromOne e :=
        (capped_general_exploration_schedule hc).integrable
      have hi : IntegrableFromOne (fun x : ℝ => 1 / x) := by
        intro a b ha hab
        exact (continuousOn_const.div continuousOn_id
          (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one (ha.trans hx.1))) :
          ContinuousOn (fun x : ℝ => 1 / x) (Set.Icc a b)).intervalIntegrable_of_Icc hab
      have hb : ∀ᶠ n : ℕ in atTop, 0 ≤ DepthIntegral.saturated c n ∧
          (1 / 2 : ℝ) * DepthIntegral.saturated c n ≤
            DepthIntegral.exploration (capped c) n ∧
          DepthIntegral.exploration (capped c) n ≤
            DepthIntegral.saturated c n := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hlog : (∫ x in (1 : ℝ)..(n : ℝ), 1 / x) = Real.log (n : ℝ) := by
          simpa using integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1)
            (show (0 : ℝ) < n by linarith)
        have hsum : (∫ x in (1 : ℝ)..(n : ℝ), g x + 1 / x) = DepthIntegral.saturated c n := by
          rw [intervalIntegral.integral_add
            (hg 1 _ le_rfl hn1)
            (hi 1 _ le_rfl hn1), hlog]
          simp only [DepthIntegral.saturated, DepthIntegral.exploration, g,
            ExplorationSchedule.mass, add_comm]
        have hlow := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hn1
          (((hg 1 _ le_rfl hn1).add (hi 1 _ le_rfl hn1)).div_const 2)
          (he 1 _ le_rfl hn1) (fun x hx => by
            dsimp [e, g]
            rw [capped_mass c (by linarith [hx.1])]
            exact (general_reciprocal_min
              (mul_pos (hc.positive x hx.1) (Real.sqrt_pos.2 (by linarith [hx.1])))
              (by linarith [hx.1])).1)
        have hupp := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hn1
          (he 1 _ le_rfl hn1)
          ((hg 1 _ le_rfl hn1).add (hi 1 _ le_rfl hn1)) (fun x hx => by
            dsimp [e, g]
            rw [capped_mass c (by linarith [hx.1])]
            exact (general_reciprocal_min
              (mul_pos (hc.positive x hx.1) (Real.sqrt_pos.2 (by linarith [hx.1])))
              (by linarith [hx.1])).2)
        rw [intervalIntegral.integral_div, hsum] at hlow
        rw [hsum] at hupp
        have hnonneg : 0 ≤ DepthIntegral.saturated c n := by
          rw [← hsum]
          apply intervalIntegral.integral_nonneg hn1
          intro x hx
          have hp := hc.positive x hx.1
          have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
          dsimp [g, ExplorationSchedule.mass]
          positivity
        refine ⟨hnonneg, ?_, hupp⟩
        simpa [e, DepthIntegral.exploration, ExplorationSchedule.mass, div_eq_mul_inv,
          mul_comm] using hlow
      apply theta_of_eventual_sandwich
      · exact hb.mono (fun _ hn => (mul_nonneg (by norm_num) hn.1).trans hn.2.1)
      · exact hb.mono (fun _ hn => hn.1)
      · exact ⟨1, by norm_num, hb.mono (fun _ hn => by simpa using hn.2.2)⟩
      · exact ⟨1 / 2, by norm_num, hb.mono (fun _ hn => hn.2.1)⟩
    have general_integral_shift {c : ℝ → ℝ}
        (hc : Assumption.GeneralExplorationSchedule c) :
        (fun n => DepthIntegral.exploration c (n + 1)) =Θ[∞] DepthIntegral.exploration c := by
      let f := ExplorationSchedule.mass c
      let g := fun x => 1 / f x
      have hfp : ∀ x ≥ 1, 0 < f x := fun x hx =>
        mul_pos (hc.positive x hx) (Real.sqrt_pos.2 (by linarith))
      have hgc : IntegrableFromOne g := hc.integrable
      have hA : 0 < hc.A := lt_of_lt_of_le zero_lt_one hc.A_one
      let δF := f hc.threshold / hc.A
      have hδF : 0 < δF := div_pos (hfp hc.threshold (by exact_mod_cast hc.threshold_pos)) hA
      obtain ⟨δ, hδ, hIall⟩ := positive_integral_lower hgc
        (fun x hx => one_div_pos.mpr (hfp x hx))
      have hI : ∀ᶠ n : ℕ in atTop, δ ≤ DepthIntegral.exploration c n := by
        filter_upwards [eventually_ge_atTop 2] with n hn
        exact hIall n (by exact_mod_cast hn)
      have hstep : ∀ᶠ n : ℕ in atTop,
          DepthIntegral.exploration c n ≤ DepthIntegral.exploration c (n + 1) ∧
          DepthIntegral.exploration c (n + 1) - DepthIntegral.exploration c n ≤ hc.A / δF := by
        filter_upwards [eventually_ge_atTop hc.threshold] with n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hc.threshold_pos.trans hn
        have hnn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
        have hmono : ∀ x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ),
            ∀ y ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ), x ≤ y → f x ≤ hc.A * f y := by
          intro x hx y hy hxy
          exact hc.monotone _ _ ((show (hc.threshold : ℝ) ≤ n by exact_mod_cast hn).trans hx.1) hxy
        have hrect := reciprocal_integral_rectangles_of_integrable hgc hfp hn1 hnn hA hmono
        have hδn : δF ≤ f n := by
          apply (div_le_iff₀ hA).2
          simpa only [mul_comm] using hc.monotone _ _ (le_refl _) (by exact_mod_cast hn)
        refine ⟨integralPotential_mono_of_integrable hgc
          (fun x hx => (one_div_pos.mpr (hfp x hx)).le) hn1 hnn, ?_⟩
        change integralPotential g ((n + 1 : ℕ) : ℝ) - integralPotential g n ≤ hc.A / δF
        simp only [integralPotential]
        rw [intervalIntegral.integral_interval_sub_left
          (hgc 1 _ le_rfl (hn1.trans hnn))
          (hgc 1 _ le_rfl hn1)]
        calc
          _ ≤ hc.A * (((n + 1 : ℕ) : ℝ) - (n : ℝ)) / f n := hrect.2
          _ = hc.A / f n := by push_cast; ring
          _ ≤ hc.A / δF := div_le_div_of_nonneg_left hA.le hδF hδn
      apply theta_of_eventual_sandwich
      · exact ((tendsto_add_atTop_nat 1).eventually hI).mono (fun _ hn => hδ.le.trans hn)
      · exact hI.mono (fun _ hn => hδ.le.trans hn)
      · refine ⟨1 + (hc.A / δF) / δ, by positivity, ?_⟩
        filter_upwards [hI, hstep] with n hn hs
        have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ (hc.A / δF) / δ by positivity)
        rw [div_mul_cancel₀ _ hδ.ne'] at hm
        nlinarith
      · exact ⟨1, by norm_num, hstep.mono (fun _ hn => by simpa only [one_mul] using hn.1)⟩
    let general_exploration_integral_path {N : ℕ → ℕ → ℕ} {H : ℕ → ℕ} {c : ℝ → ℝ}
        (h : Assumption.GeneralIntegralCountPath N H c) :
        IntegralPath H (DepthIntegral.exploration c) := by
      let general_integralPath_of_countPath
          (N : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (g : ℕ → ℝ → ℝ) (m : ℕ)
          (hm : 2 ≤ m) {κ C R δ : ℝ}
          (hκ : 0 < κ) (hC : 0 < C) (hR : 0 ≤ R) (hδ : 0 < δ)
          (hpaths : ∀ᶠ n : ℕ in atTop, CountPath (N n) (H n) n)
          (hcont : ∀ n, IntegrableFromOne (g n))
          (hpos : ∀ n x, 1 ≤ x → 0 ≤ g n x)
          (hend : ∀ᶠ n : ℕ in atTop, integralPotential (g n) m ≤ R)
          (hroot : ∀ᶠ n : ℕ in atTop, δ ≤ integralPotential (g n) n)
          (hsteps : ∀ᶠ n : ℕ in atTop, ∀ x < H n, m ≤ N n x →
            κ ≤ ∫ y in (N n (x + 1) : ℝ)..(N n x : ℝ), g n y ∧
              (∫ y in (N n (x + 1) : ℝ)..(N n x : ℝ), g n y) ≤ C) :
          IntegralPath H (fun n => integralPotential (g n) n) := by
        have hlocal_height_pos {N : ℕ → ℕ} {H n : ℕ}
            (h : CountPath N H n) (hn : 2 ≤ n) : 1 ≤ H := by
          by_contra hH
          have hzero : H = 0 := by omega
          have := h.leaf
          rw [hzero, h.root] at this
          omega
        classical
        let J : ℕ → ℕ := fun n => if hp : CountPath (N n) (H n) n then
          (hp.cutoff m hm).choose else 0
        refine { potential := fun n x => integralPotential (g n) (N n x)
                 length := J, κ := κ, C := C, endpoint := R, tail := m, δ := δ
                 κ_pos := hκ, C_pos := hC, endpoint_nonneg := hR
                 tail_nonneg := by positivity
                 δ_pos := hδ, paths := ?_ }
        filter_upwards [hpaths, hend, hroot, hsteps, eventually_ge_atTop 2] with n hp he hr hs hn
        have hcut : J n ≤ H n ∧ N n (J n) < m ∧ H n ≤ J n + m ∧
            ∀ x < J n, m ≤ N n x := by
          simpa [J, hp] using (hp.cutoff m hm).choose_spec
        have hleaf : (1 : ℝ) ≤ (N n (J n) : ℝ) := by exact_mod_cast hp.positive hcut.1
        refine ⟨hlocal_height_pos hp hn, hr, ?_, (show 0 ≤ integralPotential _ _ from
          intervalIntegral.integral_nonneg hleaf (fun x hx => (hpos n) x hx.1)),
          ?_, hcut.1, ?_, ?_⟩
        · rw [hp.root]
        · exact (integralPotential_mono_of_integrable (hcont n) (hpos n) hleaf
            (by exact_mod_cast hcut.2.1.le)).trans he
        · exact_mod_cast hcut.2.2.1
        · intro x hx
          have hxH : x < H n := hx.trans_le hcut.1
          simp only [integralPotential]
          rw [intervalIntegral.integral_interval_sub_left
            (hcont n 1 _ le_rfl (by exact_mod_cast hp.positive hxH.le))
            (hcont n 1 _ le_rfl (by exact_mod_cast hp.positive (Nat.succ_le_of_lt hxH)))]
          exact hs x hxH (hcut.2.2.2 x hx)
      have hlocal_diverges {N : ℕ → ℕ → ℕ} {H : ℕ → ℕ} {c : ℝ → ℝ}
          (h : Assumption.GeneralIntegralCountPath N H c) :
          Tendsto (DepthIntegral.exploration c) atTop atTop := by
        classical
        let J := fun n => if hp : CountPath (N n) (H n) n then
          (hp.cutoff h.threshold h.threshold_ge).choose else 0
        have hcut : ∀ᶠ n : ℕ in atTop,
            J n ≤ H n ∧ N n (J n) < h.threshold ∧ ∀ x < J n, h.threshold ≤ N n x := by
          filter_upwards [h.paths] with n hn
          have hspec := (hn.cutoff h.threshold h.threshold_ge).choose_spec
          simpa [J, hn] using And.intro hspec.1 (And.intro hspec.2.1 hspec.2.2.2)
        have hret : ∀ᶠ n : ℕ in atTop,
            h.θ ^ (J n) * (n : ℝ) ≤ (N n (J n) : ℝ) := by
          filter_upwards [h.paths, h.retention, hcut] with n hp hs hj
          have hprefix : ∀ k ≤ J n, h.θ ^ k * (n : ℝ) ≤ (N n k : ℝ) := by
            intro k
            induction k with
            | zero => intro _; simp [hp.root]
            | succ k ih =>
              intro hk
              have hkJ : k < J n := by omega
              have hprev := ih hkJ.le
              have hstep := hs k (hkJ.trans_le hj.1) (hj.2.2 k hkJ)
              have hmul := mul_le_mul_of_nonneg_left hprev h.θ_pos.le
              rw [pow_succ]
              nlinarith
          exact hprefix (J n) (le_refl _)
        have hpowers : Antitone (fun k : ℕ => h.θ ^ k) := by
          apply antitone_nat_of_succ_le
          intro k
          rw [pow_succ]
          exact mul_le_of_le_one_right (pow_nonneg h.θ_pos.le _) h.θ_lt_one.le
        have hJ : Tendsto J atTop atTop := by
          apply tendsto_atTop.2
          intro k
          have hθk : 0 < h.θ ^ k := pow_pos h.θ_pos _
          have hlarge : ∀ᶠ n : ℕ in atTop, (h.threshold : ℝ) / h.θ ^ k < (n : ℝ) :=
            tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
          filter_upwards [hcut, hret, hlarge] with n hj hr hn
          by_contra hsmall
          have hjk : J n ≤ k := by omega
          have hpower := mul_le_mul_of_nonneg_right (hpowers hjk)
            (show (0 : ℝ) ≤ (n : ℝ) by positivity)
          have hend : (N n (J n) : ℝ) < (h.threshold : ℝ) := by exact_mod_cast hj.2.1
          have hbig := (div_lt_iff₀ hθk).1 hn
          nlinarith
        let g := fun x => 1 / (c x * Real.sqrt x)
        have hgc : IntegrableFromOne g := h.integrable
        have hgp : ∀ x ≥ 1, 0 ≤ g x := by
          intro x hx
          dsimp [g]
          exact one_div_nonneg.mpr (mul_nonneg (h.positive x hx).le (Real.sqrt_nonneg _))
        have hsum : ∀ᶠ n : ℕ in atTop, h.κ * (J n : ℝ) ≤ DepthIntegral.exploration c n := by
          filter_upwards [h.paths, hcut, h.steps] with n hp hj hs
          have hstep : ∀ x < J n,
              h.κ ≤ integralPotential g (N n x) - integralPotential g (N n (x + 1)) ∧
              integralPotential g (N n x) - integralPotential g (N n (x + 1)) ≤ h.C := by
            intro x hx
            have hxH : x < H n := hx.trans_le hj.1
            simp only [integralPotential]
            rw [intervalIntegral.integral_interval_sub_left
              (hgc 1 _ le_rfl (by exact_mod_cast hp.positive hxH.le))
              (hgc 1 _ le_rfl (by exact_mod_cast hp.positive (Nat.succ_le_of_lt hxH)))]
            exact hs x hxH (hj.2.2 x hx)
          have hbound := Finset.sum_le_sum (s := Finset.range (J n))
            (fun x hx => (hstep x (Finset.mem_range.mp hx)).1)
          simp only [Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
            nsmul_eq_mul] at hbound
          have hnonneg := (show 0 ≤ integralPotential _ _ from
            intervalIntegral.integral_nonneg
              (show (1 : ℝ) ≤ (N n (J n) : ℝ) by exact_mod_cast hp.positive hj.1)
              (fun x hx => hgp x hx.1))
          rw [hp.root] at hbound
          change h.κ * (J n : ℝ) ≤ integralPotential g n
          linarith
        have hscale : Tendsto (fun n => h.κ * (J n : ℝ)) atTop atTop :=
          Filter.Tendsto.const_mul_atTop h.κ_pos (tendsto_natCast_atTop_atTop.comp hJ)
        exact tendsto_atTop_mono' atTop hsum hscale
      let g := fun y => 1 / (c y * Real.sqrt y)
      have hg : IntegrableFromOne g := h.integrable
      have hgp : ∀ y ≥ 1, 0 ≤ g y := by
        intro y hy
        exact one_div_nonneg.mpr (mul_nonneg (h.positive y hy).le (Real.sqrt_nonneg _))
      let R := integralPotential g h.threshold
      have hR : 0 ≤ R := (show 0 ≤ integralPotential _ _ from
        intervalIntegral.integral_nonneg
          (by exact_mod_cast Nat.le_trans (by decide : 1 ≤ 2) h.threshold_ge)
          (fun x hx => hgp x hx.1))
      exact general_integralPath_of_countPath N H (fun _ => g) h.threshold h.threshold_ge
        h.κ_pos h.C_pos hR zero_lt_one h.paths
        (fun _ => hg) (fun _ => hgp) (Filter.Eventually.of_forall (fun _ => le_rfl))
        ((hlocal_diverges h).eventually (eventually_ge_atTop 1))
        (h.steps)
    have hcomplete_path (V : ℕ → ℕ) (H n : ℕ)
        (hroot : V 0 = n) (hleaf : 1 ≤ V H)
        (hdec : ∀ x < H, V (x + 1) < V x) :
        CountPath (completeCountPath V H) (H + (V H - 1)) n := by
      refine ⟨by simpa [completeCountPath] using hroot, ?_, ?_⟩
      · by_cases h : V H = 1
        · simp [completeCountPath, h]
        · have hx : ¬ H + (V H - 1) ≤ H := by omega
          simp only [completeCountPath, if_neg hx]
          omega
      · intro x hx
        by_cases h : x < H
        · simpa only [completeCountPath, if_pos h.le, if_pos (Nat.succ_le_of_lt h)] using hdec x h
        · by_cases heq : x = H
          · subst x
            simp only [completeCountPath, if_pos (le_refl H), if_neg (by omega : ¬ H + 1 ≤ H)]
            omega
          · have hgt : ¬ x ≤ H := by omega
            have hgt' : ¬ x + 1 ≤ H := by omega
            simp only [completeCountPath, if_neg hgt, if_neg hgt']
            omega
    have hhigh_step {V : ℕ → ℕ} {H B m x : ℕ}
        (hend : V H ≤ B) (hmB : B < m) (hm : m ≤ completeCountPath V H x) : x < H := by
      by_contra h
      by_cases hx : x = H
      · subst x
        simp only [completeCountPath, if_pos (le_refl H)] at hm
        omega
      · have hgt : ¬ x ≤ H := by omega
        simp only [completeCountPath, if_neg hgt] at hm
        omega
    have harrival_lower :
      ∃ κ : ℝ, 0 < κ ∧ ∃ m₀ : ℕ, ∀ s t,
          ¬ M.isTerminal s → m₀ ≤ M.parentVisit s t →
          κ * min (ExplorationSchedule.mass c (M.parentVisit s t)) (M.parentVisit s t : ℝ) ≤
            (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t := by
      obtain ⟨θ, hθ, hθ1, mr, hshare⟩ :=
        scheduled_optimal_share_of_prior hseq hc.positive hreg hu hopt
      let η := θ / 2
      have hη : 0 < η := by dsimp [η]; positivity
      have hη1 : η < 1 := by dsimp [η]; linarith
      obtain ⟨R, hR, mR, hratio⟩ := hc.scaling η hη hη1
      obtain ⟨κ, hκ, ml, hlower⟩ :=
        scheduled_selected_optimal_gap_lower hseq hc.positive hreg hu hopt
      let S := R + 1 / η
      have hS : 0 < S := by dsimp [S]; positivity
      let K := max hc.threshold ml
      have hlarge : ∀ᶠ m : ℕ in atTop,
          mr ≤ m ∧ mR ≤ m ∧ 2 / θ ≤ (m : ℝ) ∧ (K : ℝ) / η ≤ (m : ℝ) := by
        filter_upwards [eventually_ge_atTop mr, eventually_ge_atTop mR,
          tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 / θ)),
          tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((K : ℝ) / η))]
          with m hmr hmR htwo hK
        exact ⟨hmr, hmR, htwo, hK⟩
      obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hlarge
      refine ⟨κ / S, by positivity, m₀, ?_⟩
      intro s t hnt ht
      obtain ⟨hmr, hmR, htwo, hK⟩ := hm₀ (M.parentVisit s t) ht
      have hr := hshare s t hnt hmr
      have ht2 := (div_le_iff₀ hθ).1 htwo
      have hstar : 0 < M.childVisit s (M.isBest s) t := by
        have : (0 : ℝ) < M.childVisit s (M.isBest s) t := by nlinarith
        exact_mod_cast this
      let u := hseq.toCountUpdates.lastSelection s (M.isBest s) t
      obtain ⟨hut, hsel, hcount⟩ := hseq.toCountUpdates.lastSelection_spec s (M.isBest s) t hstar
      change u < t at hut
      change M.selectedAt s (M.isBest s) u at hsel
      change M.childVisit s (M.isBest s) t = M.childVisit s (M.isBest s) u + 1 at hcount
      have huCount : η * (M.parentVisit s t : ℝ) ≤ M.parentVisit s u := by
        have hle := hseq.child_le_parent s (M.isBest s) u
        have hcnt : (M.childVisit s (M.isBest s) t : ℝ) ≤ (M.parentVisit s u : ℝ) + 1 := by
          exact_mod_cast (show M.childVisit s (M.isBest s) t ≤ M.parentVisit s u + 1 by omega)
        dsimp [η]
        nlinarith
      have hKu : K ≤ M.parentVisit s u := by
        have hmul := (div_le_iff₀ hη).1 hK
        have : (K : ℝ) ≤ M.parentVisit s u := by nlinarith
        exact_mod_cast this
      have hmu : hc.threshold ≤ M.parentVisit s u := (le_max_left _ _).trans hKu
      have hmlu : ml ≤ M.parentVisit s u := (le_max_right _ _).trans hKu
      have huPos : 0 < (M.parentVisit s u : ℝ) := by
        have hnat := hc.threshold_pos.trans hmu
        exact_mod_cast Nat.zero_lt_of_lt hnat
      have hFu : 0 < ExplorationSchedule.mass c (M.parentVisit s u) := by
        have hm1 := hc.threshold_pos.trans hmu
        exact mul_pos (hc.positive _ (by exact_mod_cast hm1))
          (Real.sqrt_pos.2 (by exact_mod_cast (Nat.zero_lt_of_lt hm1)))
      have hlocal := hlower s u hnt hmlu hsel
      have hRF : ExplorationSchedule.mass c (M.parentVisit s t) ≤
          R * ExplorationSchedule.mass c (M.parentVisit s u) :=
        hratio _ _ (by exact_mod_cast hmR) huCount
          (by exact_mod_cast hseq.toCountUpdates.parent_monotone s hut.le)
      have hmin : min (ExplorationSchedule.mass c (M.parentVisit s t)) (M.parentVisit s t : ℝ) ≤
          S * min (ExplorationSchedule.mass c (M.parentVisit s u)) (M.parentVisit s u : ℝ) := by
        rw [mul_min_of_nonneg _ _ hS.le]
        apply le_min
        · apply (min_le_left _ _).trans
          exact hRF.trans (mul_le_mul_of_nonneg_right
            (show R ≤ S by
              dsimp [S]
              have := one_div_pos.mpr hη
              linarith) hFu.le)
        · apply (min_le_right _ _).trans
          have hh : (M.parentVisit s t : ℝ) ≤ (1 / η) * M.parentVisit s u := by
            rw [one_div_mul_eq_div]
            exact (le_div_iff₀ hη).2 (by nlinarith)
          exact hh.trans (mul_le_mul_of_nonneg_right
            (show 1 / η ≤ S by dsimp [S]; linarith) huPos.le)
      have hsub : κ / S *
          min (ExplorationSchedule.mass c (M.parentVisit s t)) (M.parentVisit s t : ℝ) ≤
          (M.arrivalCount s u : ℝ) - M.childVisit s (M.isBest s) u := by
        have hh := mul_le_mul_of_nonneg_left hmin (show 0 ≤ κ / S by positivity)
        have heq : κ / S *
            (S * min (ExplorationSchedule.mass c (M.parentVisit s u)) (M.parentVisit s u : ℝ)) =
            κ * min (ExplorationSchedule.mass c (M.parentVisit s u))
              (M.parentVisit s u : ℝ) := by field_simp
        rw [heq] at hh
        exact hh.trans hlocal
      have hstep := hseq.parent_selected s (M.isBest s) u hsel
      have hmono := hseq.toCountUpdates.parent_monotone s (show u + 1 ≤ t by omega)
      have hnat : M.parentVisit s u + 1 ≤ M.parentVisit s t := by omega
      have hnatR : (M.parentVisit s u : ℝ) + 1 ≤ M.parentVisit s t := by exact_mod_cast hnat
      have hcountR : (M.childVisit s (M.isBest s) t : ℝ) =
          M.childVisit s (M.isBest s) u + 1 := by exact_mod_cast hcount
      simp only [MCTSModel.arrivalCount, Nat.cast_add, Nat.cast_one] at *
      linarith
    have hvisit_bounds :
      ∃ κ C θ : ℝ, 0 < κ ∧ 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∃ m₀ : ℕ, ∀ s t,
          ¬ M.isTerminal s → m₀ ≤ M.parentVisit s t →
          κ * ExplorationSchedule.mass (capped c) (M.parentVisit s t) ≤
            (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ∧
          (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ≤
            C * ExplorationSchedule.mass (capped c) (M.parentVisit s t) ∧
          θ * (M.parentVisit s t : ℝ) ≤ M.childVisit s (M.isBest s) t := by
      obtain ⟨κ, hκ, ml, hl⟩ := harrival_lower
      obtain ⟨C, hC, hupp⟩ :=
        general_uniform_arrival_upper hseq hc.toCountExplorationSchedule hreg hu
      obtain ⟨θ, hθ, hθ1, mr, hr⟩ := scheduled_optimal_share_of_prior hseq hc.positive hreg hu hopt
      refine ⟨κ, max C 2, θ, hκ, lt_of_lt_of_le hC (le_max_left _ _), hθ, hθ1,
        max hc.threshold (max ml mr), ?_⟩
      intro s t hnt hm
      have hmT := (le_max_left _ _).trans hm
      have hm1 := hc.threshold_pos.trans hmT
      have hmr := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
      have hml := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
      rw [capped_mass c (Nat.cast_nonneg _)]
      refine ⟨hl s t hnt hml, ?_, hr s t hnt hmr⟩
      rw [mul_min_of_nonneg _ _ (show 0 ≤ max C 2 by positivity)]
      apply le_min
      · exact (hupp s t hmT).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (mul_nonneg (hc.positive _ (by exact_mod_cast hm1)).le (Real.sqrt_nonneg _)))
      · have hn : (1 : ℝ) ≤ M.parentVisit s t := by exact_mod_cast hm1
        have hh := mul_le_mul_of_nonneg_right (le_max_right C 2)
          (show (0 : ℝ) ≤ M.parentVisit s t by positivity)
        simp only [MCTSModel.arrivalCount, Nat.cast_add, Nat.cast_one]
        linarith [Nat.cast_nonneg (M.childVisit s (M.isBest s) t) (α := ℝ)]
    have hstep_bounds :
      ∃ κ C η : ℝ, 0 < κ ∧ 0 < C ∧ 0 < η ∧ η < 1 ∧ ∃ m₀ : ℕ, ∀ s t,
          ¬ M.isTerminal s → m₀ ≤ M.arrivalCount s t →
          κ * ExplorationSchedule.mass (capped c) (M.arrivalCount s t) ≤
            (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ∧
          (M.arrivalCount s t : ℝ) - M.childVisit s (M.isBest s) t ≤
            C * ExplorationSchedule.mass (capped c) (M.arrivalCount s t) ∧
          η * (M.arrivalCount s t : ℝ) ≤ M.childVisit s (M.isBest s) t := by
      let he := capped_general_exploration_schedule hc
      obtain ⟨κ, C, θ, hκ, hC, hθ, hθ1, m₀, hb⟩ :=
        hvisit_bounds
      obtain ⟨R, hR, mR, hscale⟩ := he.scaling (1 / 2) (by norm_num) (by norm_num)
      have hApos : 0 < he.A := lt_of_lt_of_le zero_lt_one he.A_one
      refine ⟨κ / R, C * he.A, θ / 2, by positivity, by positivity, by positivity, by linarith,
        max (max (m₀ + 1) (2 * he.threshold)) (max 2 mR), ?_⟩
      intro s t hnt hm
      have hv0 : m₀ + 1 ≤ M.arrivalCount s t :=
        (le_max_left _ _).trans ((le_max_left _ _).trans hm)
      have hvT : 2 * he.threshold ≤ M.arrivalCount s t :=
        (le_max_right _ _).trans ((le_max_left _ _).trans hm)
      have hv2 : 2 ≤ M.arrivalCount s t := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
      have hvR : mR ≤ M.arrivalCount s t := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
      have hm0 : m₀ ≤ M.parentVisit s t := by simp only [MCTSModel.arrivalCount] at hv0; omega
      have hm1 : 1 ≤ M.parentVisit s t := by simp only [MCTSModel.arrivalCount] at hv2; omega
      have hmT : he.threshold ≤ M.parentVisit s t := by
        simp only [MCTSModel.arrivalCount] at hvT
        have := he.threshold_pos
        omega
      obtain ⟨hl, hh, hr⟩ := hb s t hnt hm0
      have hvhalf : (he.threshold : ℝ) ≤ (1 / 2 : ℝ) * M.arrivalCount s t := by
        have : (2 : ℝ) * he.threshold ≤ M.arrivalCount s t := by exact_mod_cast hvT
        linarith
      have hhalf : (1 / 2 : ℝ) * M.arrivalCount s t ≤ M.parentVisit s t := by
        simp only [MCTSModel.arrivalCount, Nat.cast_add, Nat.cast_one]
        have : (1 : ℝ) ≤ M.parentVisit s t := by exact_mod_cast hm1
        linarith
      have hmass : ExplorationSchedule.mass (capped c) (M.arrivalCount s t) ≤
          R * ExplorationSchedule.mass (capped c) (M.parentVisit s t) :=
        hscale _ _ (by exact_mod_cast hvR) hhalf
          (by exact_mod_cast Nat.le_succ (M.parentVisit s t))
      have hlo : κ / R *
          ExplorationSchedule.mass (capped c) (M.arrivalCount s t) ≤
          κ * ExplorationSchedule.mass (capped c) (M.parentVisit s t) := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hR).2
        nlinarith [mul_le_mul_of_nonneg_left hmass hκ.le]
      have hmono' := he.monotone _ _
        (show (he.threshold : ℝ) ≤ M.parentVisit s t by exact_mod_cast hmT)
        (show (M.parentVisit s t : ℝ) ≤ M.arrivalCount s t by
          exact_mod_cast Nat.le_succ (M.parentVisit s t))
      refine ⟨hlo.trans hl, ?_, ?_⟩
      · simpa only [mul_assoc] using hh.trans (mul_le_mul_of_nonneg_left hmono' hC.le)
      · have hsmall := mul_le_mul_of_nonneg_left hhalf hθ.le
        nlinarith
    have hdepth_from_arrivals
        (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
        (hpath : ∀ᶠ n : ℕ in atTop,
          M.OptimalPathCounts (V n) (H n) (n) (state n) (time n)) :
        (fun n => (H n : ℝ)) =Θ[∞] DepthIntegral.exploration (capped c) := by
      let he := capped_general_exploration_schedule hc
      obtain ⟨κ, C, η, hκ, hC, hη, hη1, m₀, hstep⟩ :=
        hstep_bounds
      obtain ⟨θ, hθ, -, mθ, hshare⟩ :=
        scheduled_optimal_share_of_prior hseq hc.positive hreg hu hopt
      obtain ⟨B, hfront⟩ := frontier_bound_of_optimal_share hθ hshare
      obtain ⟨R, hR, mR, hratio⟩ := he.scaling η hη hη1
      obtain ⟨mη, hmη⟩ := exists_nat_ge ((he.threshold : ℝ) / η)
      let m := max (max 2 (B + 1)) (max (max m₀ mR) mη)
      have hm2 : 2 ≤ m := (le_max_left _ _).trans (le_max_left _ _)
      have hmB : B < m := lt_of_lt_of_le (Nat.lt_succ_self B)
        ((le_max_right _ _).trans (le_max_left _ _))
      have hm0 : m₀ ≤ m := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
      have hmR : mR ≤ m := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
      have hmη' : (he.threshold : ℝ) ≤ η * m := by
        have hle : (mη : ℝ) ≤ m := by
          exact_mod_cast (le_max_right (max m₀ mR) mη).trans (le_max_right _ _)
        have hbound := (div_le_iff₀ hη).1 (hmη.trans hle)
        nlinarith
      let W := fun n => completeCountPath (V n) (H n)
      let J := fun n => H n + (V n (H n) - 1)
      have hdata : ∀ᶠ n : ℕ in atTop, V n 0 = n ∧ 1 ≤ V n (H n) ∧ V n (H n) ≤ B ∧
          ∀ x < H n, V n (x + 1) < V n x := by
        filter_upwards [hpath] with n hn
        refine ⟨hn.1, ?_, ?_, ?_⟩
        · rw [hn.2.1]
          exact Nat.succ_pos _
        · rw [hn.2.1]
          exact hfront _ _ hn.2.2.1 hn.2.2.2.1
        · intro x hx
          obtain ⟨_, hp, hc⟩ := hn.2.2.2.2 x hx
          rw [hp, hc]
          exact Nat.lt_succ_of_le (hseq.child_le_parent _ _ _)
      have hApos : 0 < he.A := lt_of_lt_of_le zero_lt_one he.A_one
      have hp : Assumption.GeneralIntegralCountPath W J (capped c) := {
        threshold := m
        threshold_ge := hm2
        κ := κ / he.A
        C := C * R * he.A
        θ := η
        κ_pos := by positivity
        C_pos := by positivity
        θ_pos := hη
        θ_lt_one := hη1
        integrable := he.integrable
        positive := he.positive
        paths := by
          filter_upwards [hdata] with n hn
          exact hcomplete_path (V n) (H n) n hn.1 hn.2.1 hn.2.2.2
        retention := by
          filter_upwards [hpath, hdata] with n hn hd
          intro x _ hx
          have hxH := hhigh_step hd.2.2.1 hmB hx
          obtain ⟨hnt, hparent, hchild⟩ := hn.2.2.2.2 x hxH
          have hW : W n x = V n x := by simp [W, completeCountPath, hxH.le]
          have hW' : W n (x + 1) = V n (x + 1) := by
            simp [W, completeCountPath, Nat.succ_le_of_lt hxH]
          have hlarge : m₀ ≤ M.arrivalCount (state n x) (time n x) := by
            rw [hW, hparent] at hx
            exact hm0.trans hx
          simpa only [hW, hW', hparent, hchild] using
            (hstep (state n x) (time n x) hnt hlarge).2.2
        steps := by
          filter_upwards [hpath, hdata] with n hn hd
          intro x _ hx
          have hxH := hhigh_step hd.2.2.1 hmB hx
          obtain ⟨hnt, hparent, hchild⟩ := hn.2.2.2.2 x hxH
          have hW : W n x = V n x := by simp [W, completeCountPath, hxH.le]
          have hW' : W n (x + 1) = V n (x + 1) := by
            simp [W, completeCountPath, Nat.succ_le_of_lt hxH]
          rw [hW, hW']
          rw [hW] at hx
          have hlarge : m₀ ≤ M.arrivalCount (state n x) (time n x) := by
            rw [hparent] at hx
            exact hm0.trans hx
          obtain ⟨hlo, hhi, hshare⟩ := hstep (state n x) (time n x) hnt hlarge
          rw [← hparent, ← hchild] at hlo hhi hshare
          have hupper : (V n (x + 1) : ℝ) ≤ V n x := by exact_mod_cast (hd.2.2.2 x hxH).le
          have hpar : (m : ℝ) ≤ V n x := by exact_mod_cast hx
          have hθpar : (he.threshold : ℝ) ≤ η * V n x :=
            hmη'.trans (mul_le_mul_of_nonneg_left hpar hη.le)
          have hchild1 : (1 : ℝ) ≤ V n (x + 1) :=
            (show (1 : ℝ) ≤ he.threshold by exact_mod_cast he.threshold_pos).trans
              (hθpar.trans hshare)
          let f := ExplorationSchedule.mass (capped c)
          have hfp : ∀ y ≥ 1, 0 < f y := fun y hy =>
            mul_pos (he.positive y hy) (Real.sqrt_pos.2 (by linarith))
          have hmono : ∀ u ∈ Set.Icc (V n (x + 1) : ℝ) (V n x : ℝ),
              ∀ v ∈ Set.Icc (V n (x + 1) : ℝ) (V n x : ℝ), u ≤ v → f u ≤ he.A * f v := by
            intro u hu v hv huv
            exact he.monotone u v (hθpar.trans (hshare.trans hu.1)) huv
          have hrect := reciprocal_integral_rectangles_of_integrable
            he.integrable hfp hchild1 hupper hApos hmono
          have hrat : f (V n x) ≤ R * f (V n (x + 1)) :=
            hratio _ _ ((show (mR : ℝ) ≤ m by exact_mod_cast hmR).trans hpar) hshare hupper
          have hfpb := hfp _ (hchild1.trans hupper)
          have hfpa := hfp _ hchild1
          constructor
          · apply le_trans _ hrect.1
            apply (le_div_iff₀ (mul_pos hApos hfpb)).2
            have heq : κ / he.A * (he.A * f (V n x)) = κ * f (V n x) := by
              field_simp
            simpa only [heq] using hlo
          · apply hrect.2.trans
            apply (div_le_iff₀ hfpa).2
            have hh := mul_le_mul_of_nonneg_left hrat hC.le
            have hh' := mul_le_mul_of_nonneg_left (hhi.trans hh) hApos.le
            nlinarith }
      have hJ := depth_theta_of_integral_path (general_exploration_integral_path hp)
      have hHpos : ∀ᶠ n : ℕ in atTop, 1 ≤ H n := by
        filter_upwards [hdata, eventually_gt_atTop B] with n hn hbig
        by_contra h
        have hzero : H n = 0 := by omega
        rw [hzero, hn.1] at hn
        omega
      have hHJ : (fun n => (H n : ℝ)) =Θ[∞] (fun n => (J n : ℝ)) := by
        constructor
        · apply Asymptotics.IsBigO.of_bound 1
          filter_upwards [] with n
          have hle : H n ≤ J n := by dsimp [J]; omega
          simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (H n) (α := ℝ)),
            abs_of_nonneg (Nat.cast_nonneg (J n) (α := ℝ)), one_mul] using
            (show (H n : ℝ) ≤ J n by exact_mod_cast hle)
        · apply Asymptotics.IsBigO.of_bound ((B : ℝ) + 1)
          filter_upwards [hdata, hHpos] with n hn hpos
          have hJle : J n ≤ H n + B := by dsimp [J]; omega
          have hh : (1 : ℝ) ≤ H n := by exact_mod_cast hpos
          have hj : (J n : ℝ) ≤ (H n : ℝ) + B := by exact_mod_cast hJle
          have hmul := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ B by positivity)
          simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (H n) (α := ℝ)),
            abs_of_nonneg (Nat.cast_nonneg (J n) (α := ℝ))]
          nlinarith
      exact hHJ.trans hJ
    have hmodel_depth : (fun n => (H n : ℝ)) =Θ[∞]
        DepthIntegral.exploration (capped c) := by
      have hd := hdepth_from_arrivals
        (fun k x => V (k - 1) x) (fun k => H (k - 1))
        (fun k x => state (k - 1) x) (fun k x => time (k - 1) x) (by
          filter_upwards [(tendsto_sub_atTop_nat 1).eventually hpath, eventually_ge_atTop 1]
            with k hk hk1
          simpa only [Nat.sub_add_cancel hk1] using hk)
      have hshift := And.intro (hd.1.comp_tendsto (tendsto_add_atTop_nat 1))
        (hd.2.comp_tendsto (tendsto_add_atTop_nat 1))
      have hroot : (fun n => (H n : ℝ)) =Θ[∞]
          (fun n => DepthIntegral.exploration (capped c) (n + 1)) := by
        simpa [Function.comp_def] using hshift
      exact hroot.trans (general_integral_shift (capped_general_exploration_schedule hc))
    exact hmodel_depth.trans (general_capped_integral_equiv hc)
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    have hb := measurable_regular_variation_subcritical hL hform hcBound ha
    exact (hdepth.trans (saturated_depth_weak
      hc.integrable hc.positive hb)).trans
      (measurable_exploration_subcritical hc hL hform hb ha)
  · intro ha
    have heq := exploration_eq_critical_of_sqrt_form (c := c) (L := L) (fun x hx => by
      rw [hform x hx, ha]
      exact congrArg (fun y => y * L x) (Real.sqrt_eq_rpow x).symm)
    exact hdepth.trans (Filter.EventuallyEq.isTheta (heq.mono
      (fun n hn => by simp only [DepthIntegral.saturated, hn])))
  · intro ha
    exact hdepth.trans (saturated_depth_strong
      hc.integrable hc.positive
      (measurable_regular_variation_supercritical hL hform hInvBound ha))

/-- Corollary 2.3, capped: eventual terminal depth and all three capped rates. -/
theorem corollary23_capped {M : MCTSModel} {c L : ℝ → ℝ} {α : ℝ}
    (hseq : M.Scheduled c) (hreg : Assumption.Regularity M) (hu : M.UniformValueConsistency)
    (hopt : ∃ p : ℝ, 0 < p ∧ ∀ s, ¬ M.isTerminal s → p ≤ M.prior s (M.isBest s))
    (hL : SlowlyVarying L) (hform : ∀ x ≥ 1, c x = Real.rpow x α * L x)
    (_hα : -(1 / 2 : ℝ) < α)
    (hcBound : LocallyBounded c)
    (_hInvBound : LocallyBounded (fun x => 1 / c x))
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (D : ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      M.CappedOptimalPathCounts (V n) (H n) (n + 1) D (state n) (time n)) :
    (α < 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
      (fun n => min (D : ℝ) (Real.sqrt (n : ℝ) / c n))) ∧
    (α = 1 / 2 → (fun n => (H n : ℝ)) =Θ[∞]
      (fun n => min (D : ℝ) (Real.log (n : ℝ) + DepthIntegral.critical L n))) ∧
    (1 / 2 < α → (fun n => (H n : ℝ)) =Θ[∞]
      (fun n : ℕ => min (D : ℝ) (Real.log (n : ℝ)))) := by
  have hp : ∀ x ≥ 1, 0 < c x := by
    intro x hx
    rw [hform x hx]
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (hL.positive x hx)
  have heq := scheduled_depth_capped_of_optimal_share
    (scheduled_optimal_share_of_prior hseq hp hreg hu hopt) V H D state time hpath
  have hterminal : ∀ᶠ n : ℕ in atTop, H n ≤ D ∧ (D = 0 ∨ 1 ≤ H n) := by
    filter_upwards [heq] with n hn
    rw [hn]
    exact ⟨le_rfl, by omega⟩
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    let d : ℝ → ℝ := fun x => Real.sqrt x / c x
    let ρ : ℝ := 1 / 2 - α
    have hρ : 0 < ρ := by dsimp [ρ]; linarith
    have hdpos : ∀ x ≥ 1, 0 < d x := fun x hx =>
      div_pos (Real.sqrt_pos.2 (by linarith)) (hp x hx)
    have hdform : ∀ x ≥ 1, d x = x ^ ρ / L x := by
      intro x hx
      dsimp [d, ρ]
      rw [hform x hx]
      change Real.sqrt x / (x ^ α * L x) = x ^ (1 / 2 - α) / L x
      rw [Real.rpow_sub (by linarith : 0 < x), ← Real.sqrt_eq_rpow]
      ring
    have hlim : Tendsto (fun x : ℝ => d (2 * x) / d x) atTop (𝓝 ((2 : ℝ) ^ ρ)) := by
      have hh := ((hL.ratio 2 (by norm_num)).inv₀ (by norm_num : (1 : ℝ) ≠ 0)).const_mul
        ((2 : ℝ) ^ ρ)
      simp only [inv_one, mul_one] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hxpos : 0 < x := by linarith
      rw [hdform x hx, hdform (2 * x) (by linarith),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxpos.le]
      simp only [inv_div]
      field_simp [(Real.rpow_pos_of_pos hxpos ρ).ne']
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
      (hlim.eventually_const_le (Real.one_lt_rpow (by norm_num) hρ))
    let T : ℝ := max 1 T₀
    have hT : 1 ≤ T := le_max_left _ _
    have hdouble : ∀ x ≥ T, d x ≤ d (2 * x) := by
      intro x hx
      have hh := (le_div_iff₀ (hdpos x (hT.trans hx))).1
        (hT₀ x ((le_max_right _ _).trans hx))
      simpa only [one_mul] using hh
    obtain ⟨C₀, hC₀⟩ := (hcBound (2 * T) (by linarith)).exists_norm_le
    let C : ℝ := max 1 C₀
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hbase : ∀ x ∈ Set.Icc T (2 * T), 1 / C ≤ d x := by
      intro x hx
      have hx1 := hT.trans hx.1
      have hc : c x ≤ C := by
        have hh := hC₀ _ (Set.mem_image_of_mem _ ⟨hx1, hx.2⟩)
        rw [Real.norm_eq_abs, abs_of_pos (hp x hx1)] at hh
        exact hh.trans (le_max_right _ _)
      have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx1
      apply (le_div_iff₀ (hp x hx1)).2
      have hh := mul_le_mul_of_nonneg_left hc (one_div_pos.mpr hC).le
      rw [one_div_mul_cancel hC.ne'] at hh
      exact hh.trans hs
    have hlower : ∀ x ≥ T, 1 / C ≤ d x := by
      intro x hx
      have hTp : 0 < T := by linarith
      obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near
        ((le_div_iff₀ hTp).2 (by simpa using hx)) (by norm_num : (1 : ℝ) < 2)
      let z : ℝ := x / (2 : ℝ) ^ k
      have hz : T ≤ z := by
        dsimp [z]
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).2
        have hh := (le_div_iff₀ hTp).1 hk
        simpa [mul_comm] using hh
      have hz2 : z ≤ 2 * T := by
        dsimp [z]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).2
        have hh := (div_lt_iff₀ hTp).1 hk'
        nlinarith [pow_succ (2 : ℝ) k]
      have hiter : Monotone (fun j : ℕ => d ((2 : ℝ) ^ j * z)) := by
        apply monotone_nat_of_le_succ
        intro j
        have hzpos : 0 ≤ z := (by linarith : 0 ≤ T).trans hz
        have hj : T ≤ (2 : ℝ) ^ j * z :=
          hz.trans (le_mul_of_one_le_left hzpos (one_le_pow₀ (by norm_num)))
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          hdouble ((2 : ℝ) ^ j * z) hj
      have hh := hiter (Nat.zero_le k)
      have he : (2 : ℝ) ^ k * z = x := by dsimp [z]; field_simp
      simp only [pow_zero, one_mul, he] at hh
      exact (hbase z ⟨hz, hz2⟩).trans hh
    have hratio : ∀ᶠ n : ℕ in atTop, 1 / C ≤ Real.sqrt (n : ℝ) / c n := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop T)] with n hn
      exact hlower n hn
    exact finite_depth_capped_rate H D _ (one_div_pos.mpr hC) hratio hterminal
  · intro _
    apply finite_depth_capped_rate H D _ (δ := 1) (by norm_num) _ hterminal
    filter_upwards [hlog, eventually_ge_atTop 1] with n hn hn1
    have hi : 0 ≤ DepthIntegral.critical L n := by
      apply intervalIntegral.integral_nonneg (by exact_mod_cast hn1)
      intro x hx
      exact one_div_nonneg.mpr (mul_nonneg (by linarith [hx.1]) (hL.positive x hx.1).le)
    linarith
  · intro _
    exact finite_depth_capped_rate H D _ (δ := 1) (by norm_num) hlog hterminal

/-! ## Parallelism -/

namespace DepthIntegral

/-- `T n` is constant within each integral. -/
noncomputable def parallel (T : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∫ m in (1 : ℝ)..(n : ℝ), 1 / (Real.sqrt m + (T n : ℝ))

private noncomputable def parallelRate (T : ℕ → ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) / (Real.sqrt (n : ℝ) + (T n : ℝ))

end DepthIntegral

private theorem lemma4_of_visit_bounds (N : ℕ → ℕ → ℝ) (H T : ℕ → ℕ)
    {B C E R ρ K M₀ : ℝ}
    (hB : 0 < B) (hC : 0 < C) (hE : 0 ≤ E) (_hR : 0 ≤ R)
    (hρ : 0 < ρ) (_hK : 0 ≤ K)
    (hcounts : ∀ n x, x < H n → M₀ ≤ N n x →
      N n x - N n (x + 1) ≤ C * (Real.sqrt (N n x) + (T n : ℝ)) ∧
      B * Real.sqrt (N n x) - E * (T n : ℝ) - R ≤ N n x - N n (x + 1) ∧
      ρ * (T n : ℝ) - K ≤ N n x - N n (x + 1)) :
    (∃ κ₁ κ₂ : ℝ, 0 < κ₁ ∧ κ₁ ≤ κ₂ ∧ ∃ M : ℝ,
      ∀ n x, x < H n → M ≤ N n x →
        κ₁ * (Real.sqrt (N n x) + (T n : ℝ)) ≤ N n x - N n (x + 1) ∧
        N n x - N n (x + 1) ≤ κ₂ * (Real.sqrt (N n x) + (T n : ℝ))) := by
  let S := ρ + E + B
  have hS : 0 < S := by dsimp [S]; positivity
  let κ := min C (ρ * B / (2 * S))
  have hκ : 0 < κ := lt_min hC (by positivity)
  have hcoef : S * κ ≤ ρ * B / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * S)).mp (min_le_right C (ρ * B / (2 * S)))
    dsimp [κ]
    nlinarith
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_sqrt_atTop.eventually
      (eventually_ge_atTop (2 * (ρ * R + (E + B) * K) / (ρ * B))))
  refine ⟨κ, C, hκ, min_le_left _ _, max M₀ M₁, ?_⟩
  intro n x hx hNx
  obtain ⟨hupper, hlower, hwindow⟩ := hcounts n x hx ((le_max_left _ _).trans hNx)
  have hthreshold := (div_le_iff₀ (mul_pos hρ hB)).mp
    (hM₁ (N n x) ((le_max_right _ _).trans hNx))
  have hcombined := add_le_add
    (mul_le_mul_of_nonneg_left hlower hρ.le)
    (mul_le_mul_of_nonneg_left hwindow (by positivity : 0 ≤ E + B))
  have hscale := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ Real.sqrt (N n x) + (T n : ℝ) by positivity)
  refine ⟨(mul_le_mul_iff_right₀ hS).mp ?_, hupper⟩
  dsimp [S] at *
  nlinarith [mul_nonneg (mul_pos hρ hB).le (show (0 : ℝ) ≤ T n by positivity)]

private theorem parallel_interval_bounds {a b T : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hT : 0 < T) :
    (b - a) / (Real.sqrt b + T) ≤ (∫ y in a..b, 1 / (Real.sqrt y + T)) ∧
      (∫ y in a..b, 1 / (Real.sqrt y + T)) ≤ 2 * (b - a) / (Real.sqrt b + T) := by
  have hden : 0 < Real.sqrt b + T := by positivity
  have hsqrt : ∀ y ∈ Set.uIcc a b, 0 < Real.sqrt y := by
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    exact Real.sqrt_pos.mpr (by linarith [hy.1])
  have hc : Continuous (fun y : ℝ => 1 / (Real.sqrt y + T)) :=
    continuous_const.div (Real.continuous_sqrt.add continuous_const)
      (fun y => (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg y) hT).ne')
  have hg : ContinuousOn (fun y => Real.sqrt b / (Real.sqrt y * (Real.sqrt b + T)))
      (Set.uIcc a b) :=
    continuousOn_const.div (Real.continuous_sqrt.continuousOn.mul continuousOn_const)
      (fun y hy => (mul_pos (hsqrt y hy) hden).ne')
  have hint : (∫ y in a..b, Real.sqrt b / (Real.sqrt y * (Real.sqrt b + T))) =
      2 * Real.sqrt b * Real.sqrt b / (Real.sqrt b + T) -
        2 * Real.sqrt b * Real.sqrt a / (Real.sqrt b + T) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y => 2 * Real.sqrt b * Real.sqrt y / (Real.sqrt b + T)) _ hg.intervalIntegrable
    intro y hy
    convert ((Real.hasDerivAt_sqrt (by
      have := hsqrt y hy
      exact (Real.sqrt_pos.mp this).ne')).const_mul (2 * Real.sqrt b)).div_const
      (Real.sqrt b + T) using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨(reciprocal_integral_rectangles
    (Real.continuous_sqrt.add continuous_const).continuousOn
    (fun y _ => add_pos_of_nonneg_of_pos (Real.sqrt_nonneg y) hT) ha hab
    (fun _ _ _ _ hxy => by dsimp; linarith [Real.sqrt_le_sqrt hxy])).1, ?_⟩
  have hupper := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (hc.intervalIntegrable a b) hg.intervalIntegrable (fun y hy => by
      have hypos := hsqrt y (by rwa [Set.uIcc_of_le hab])
      apply (div_le_div_iff₀ (by positivity : 0 < Real.sqrt y + T)
        (mul_pos hypos hden)).2
      nlinarith [mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hy.2) hT.le])
  rw [hint] at hupper
  apply hupper.trans
  rw [← sub_div, div_le_div_iff_of_pos_right hden]
  nlinarith [Real.sq_sqrt (show 0 ≤ a by linarith),
    Real.sq_sqrt (show 0 ≤ b by linarith),
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg a)]


private theorem parallel_integral_bounds {n T : ℝ} (hn : 2 ≤ n) (hT : 0 < T) :
    n / (2 * (Real.sqrt n + T)) ≤ (∫ m in (1 : ℝ)..n, 1 / (Real.sqrt m + T)) ∧
      (∫ m in (1 : ℝ)..n, 1 / (Real.sqrt m + T)) ≤ 4 * (n / (Real.sqrt n + T)) := by
  have hb := parallel_interval_bounds le_rfl (by linarith : (1 : ℝ) ≤ n) hT
  have hden : 0 < Real.sqrt n + T := by positivity
  constructor
  · apply le_trans _ hb.1
    calc
      n / (2 * (Real.sqrt n + T)) = (n / 2) / (Real.sqrt n + T) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (n - 1) / (Real.sqrt n + T) := div_le_div_of_nonneg_right (by linarith) hden.le
  · apply hb.2.trans
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hden.le

private theorem parallel_integral_theta_rate (T : ℕ → ℕ)
    (hT : ∀ᶠ n : ℕ in atTop, 1 ≤ T n) :
    DepthIntegral.parallel T =Θ[∞] DepthIntegral.parallelRate T := by
  have hbounds : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * DepthIntegral.parallelRate T n ≤ DepthIntegral.parallel T n ∧
        DepthIntegral.parallel T n ≤ 4 * DepthIntegral.parallelRate T n := by
    filter_upwards [hT, eventually_ge_atTop 2] with n hn hn2
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hT' : (0 : ℝ) < (T n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have h := parallel_integral_bounds hn' hT'
    constructor
    · dsimp [DepthIntegral.parallelRate, DepthIntegral.parallel]
      convert h.1 using 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · exact h.2
  apply theta_of_eventual_sandwich
  · filter_upwards [hbounds] with n hn
    have hrate : 0 ≤ DepthIntegral.parallelRate T n := by
      dsimp [DepthIntegral.parallelRate]; positivity
    linarith [hn.1]
  · exact Filter.Eventually.of_forall (fun n => by dsimp [DepthIntegral.parallelRate]; positivity)
  · exact ⟨4, by norm_num, hbounds.mono (fun _ hn => hn.2)⟩
  · exact ⟨1 / 2, by norm_num, hbounds.mono (fun _ hn => hn.1)⟩

private theorem parallel_rate_small (T : ℕ → ℕ)
    (hsmall : (fun n => (T n : ℝ)) =O[∞] DepthProfile.sqrtSimulationCount) :
    DepthIntegral.parallelRate T =Θ[∞] DepthProfile.sqrtSimulationCount := by
  obtain ⟨C, hC, hbound⟩ := hsmall.exists_pos
  have hpoint : ∀ᶠ n : ℕ in atTop,
      1 / (1 + C) * Real.sqrt (n : ℝ) ≤ DepthIntegral.parallelRate T n ∧
      DepthIntegral.parallelRate T n ≤ Real.sqrt (n : ℝ) := by
    filter_upwards [hbound.bound, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hn1
    have hspos := Real.sqrt_pos.2 hnpos
    have hT : (T n : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
      simpa [DepthProfile.sqrtSimulationCount, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))] using hn
    have hden : 0 < Real.sqrt (n : ℝ) + (T n : ℝ) := by positivity
    have hsq := Real.sq_sqrt hnpos.le
    dsimp [DepthIntegral.parallelRate]
    constructor
    · rw [one_div_mul_eq_div]
      apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 + C) hden).2
      nlinarith
    · apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (show (0 : ℝ) ≤ (T n : ℝ) by positivity)]
  apply theta_of_eventual_sandwich
  · exact Filter.Eventually.of_forall (fun n => by dsimp [DepthIntegral.parallelRate]; positivity)
  · exact Filter.Eventually.of_forall (fun n => Real.sqrt_nonneg _)
  · exact ⟨1, by norm_num, hpoint.mono (fun _ hn => by simpa using hn.2)⟩
  · exact ⟨1 / (1 + C), by positivity, hpoint.mono (fun _ hn => hn.1)⟩

/-! ## Parallel visit estimates -/

private structure Assumption.ParallelEstimates (N : ℕ → ℕ → ℕ) (H T : ℕ → ℕ) where
  threshold : ℕ
  B : ℝ
  C : ℝ
  E : ℝ
  R : ℝ
  B_pos : 0 < B
  C_pos : 0 < C
  E_nonneg : 0 ≤ E
  R_nonneg : 0 ≤ R
  steps : ∀ n x, x < H n → threshold ≤ N n x →
    (N n x : ℝ) - N n (x + 1) ≤ C * (Real.sqrt (N n x : ℝ) + T n) ∧
    B * Real.sqrt (N n x : ℝ) - E * T n - R ≤ (N n x : ℝ) - N n (x + 1)

/-! ## Parallel execution

Selections are issued, decisions use visible snapshots, and reported counts are completed.
-/

structure MCTSModel.ParallelExecution (M : MCTSModel) (c : ℝ) where
  updates : M.CountUpdates
  threads : M.State → ℕ
  threads_pos : ∀ s, 1 ≤ threads s
  visibleParent : M.State → ℕ → ℕ
  visibleChild : ∀ s, M.Action s → ℕ → ℕ
  completedChild : ∀ s, M.Action s → ℕ → ℕ
  visible_parent_le : ∀ s t, visibleParent s t ≤ M.parentVisit s t
  parent_snapshot_lag : ∀ s t, M.parentVisit s t ≤ visibleParent s t + threads s
  visible_child_le : ∀ s a t, visibleChild s a t ≤ M.childVisit s a t
  child_snapshot_lag : ∀ s a t, M.childVisit s a t ≤ visibleChild s a t + threads s
  completed_le_issued : ∀ s a t, completedChild s a t ≤ M.childVisit s a t
  child_outstanding : ∀ s a t, M.childVisit s a t ≤ completedChild s a t + threads s
  parent_outstanding : ∀ s t,
    M.parentVisit s t ≤ (∑' a, completedChild s a t) + threads s
  completed_monotone : ∀ s a, Monotone (completedChild s a)
  argmax : ∀ s a t, M.selectedAt s a t → ∀ b,
    M.searchValue s b t + c * M.prior s b * Real.sqrt (visibleParent s t : ℝ) /
      (1 + (visibleChild s b t : ℝ)) ≤
    M.searchValue s a t + c * M.prior s a * Real.sqrt (visibleParent s t : ℝ) /
      (1 + (visibleChild s a t : ℝ))
  uniform_values : ∀ ε : ℝ, 0 < ε → ∃ m₀ : ℕ, ∀ s a t,
    m₀ ≤ visibleParent s t → |M.searchValue s a t - M.value s a| ≤ ε

namespace MCTSModel.ParallelExecution

variable {M : MCTSModel} {c : ℝ}

noncomputable def completedParent (h : M.ParallelExecution c) (s : M.State) (t : ℕ) : ℕ :=
  ∑' a, h.completedChild s a t

noncomputable def arrivalCount (h : M.ParallelExecution c) (s : M.State) (t : ℕ) : ℕ :=
  h.completedParent s t + 1

/-- Optimal-path count identities with `T` threads at each reached node. -/
def PathEdges (h : M.ParallelExecution c) (V : ℕ → ℕ) (H T : ℕ)
    (state : ℕ → M.State) (time : ℕ → ℕ) : Prop :=
  ∀ x < H, ¬ M.isTerminal (state x) ∧ V x = h.arrivalCount (state x) (time x) ∧
    V (x + 1) = h.completedChild (state x) (M.isBest (state x)) (time x) ∧
    h.threads (state x) = T

/-- Root count and nonterminal frontier with an unvisited optimal child. -/
def Frontier (h : M.ParallelExecution c) (V : ℕ → ℕ) (H root T : ℕ)
    (state : ℕ → M.State) (time : ℕ → ℕ) : Prop :=
  V 0 = root ∧ V H = h.arrivalCount (state H) (time H) ∧ ¬ M.isTerminal (state H) ∧
    h.completedChild (state H) (M.isBest (state H)) (time H) = 0 ∧ h.threads (state H) = T

/-- A path capped at `L`, with completed counts and `T` threads. -/
def CappedPathCounts (h : M.ParallelExecution c) (V : ℕ → ℕ) (H root L T : ℕ)
    (state : ℕ → M.State) (time : ℕ → ℕ) : Prop :=
  V 0 = root ∧ H ≤ L ∧
    (H < L → V H = h.arrivalCount (state H) (time H) ∧
      h.completedChild (state H) (M.isBest (state H)) (time H) = 0 ∧
      h.threads (state H) = T) ∧
    h.PathEdges V H T state time

private theorem completedParent_le_issued (h : M.ParallelExecution c)
    (s : M.State) [Finite (M.Action s)] (t : ℕ) :
    h.completedParent s t ≤ M.parentVisit s t := by
  classical
  letI := Fintype.ofFinite (M.Action s)
  rw [h.updates.count_identity s t]
  simpa [completedParent, tsum_fintype] using
    (Finset.sum_le_sum (fun a _ => h.completed_le_issued s a t))

private theorem completed_child_le_parent (h : M.ParallelExecution c)
    (s : M.State) [Finite (M.Action s)] (a : M.Action s) (t : ℕ) :
    h.completedChild s a t ≤ h.completedParent s t := by
  classical
  letI := Fintype.ofFinite (M.Action s)
  simpa [completedParent, tsum_fintype] using
    (Finset.single_le_sum (fun b _ => Nat.zero_le (h.completedChild s b t)) (Finset.mem_univ a))

end MCTSModel.ParallelExecution

private theorem parallel_issued_gap_upper {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s t,
      (M.parentVisit s t : ℝ) - M.childVisit s (M.isBest s) t ≤
        C * (Real.sqrt (M.parentVisit s t : ℝ) + h.threads s) := by
  have hprefix_upper {M : MCTSModel} {c : ℝ}
      (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M) :
      ∃ K A : ℝ, 0 ≤ K ∧ 0 < A ∧ ∀ s a t (lag : ℕ),
        (∀ u, u < t → M.parentVisit s u ≤ h.visibleParent s u + lag ∧
          ∀ b, M.childVisit s b u ≤ h.visibleChild s b u + lag) →
        M.Suboptimal s a →
        (M.childVisit s a t : ℝ) ≤ K + A * Real.sqrt (M.parentVisit s t : ℝ) + lag := by
    obtain ⟨Δ, hΔ, hg⟩ := hreg.gap_lower
    obtain ⟨m₀, hv⟩ := h.uniform_values (Δ / 4) (by positivity)
    refine ⟨m₀, 2 * c / Δ, by positivity, by positivity, ?_⟩
    intro s a t lag hlag_prefix ha
    by_cases hz : M.childVisit s a t = 0
    · rw [hz, Nat.cast_zero]
      positivity
    let u := h.updates.lastSelection s a t
    obtain ⟨hut, hsel, hcount⟩ := h.updates.lastSelection_spec s a t (Nat.pos_of_ne_zero hz)
    change u < t at hut
    change M.selectedAt s a u at hsel
    change M.childVisit s a t = M.childVisit s a u + 1 at hcount
    by_cases hm : m₀ ≤ h.visibleParent s u
    · have hs := h.argmax s a u hsel (M.isBest s)
      have hbonus : 0 ≤ c * M.prior s (M.isBest s) * Real.sqrt (h.visibleParent s u : ℝ) /
          (1 + (h.visibleChild s (M.isBest s) u : ℝ)) := by
        have := M.prior_nonneg s (M.isBest s)
        positivity
      have hcompare : M.searchValue s (M.isBest s) u ≤ M.searchValue s a u +
          c * M.prior s a * Real.sqrt (h.visibleParent s u : ℝ) /
            (1 + (h.visibleChild s a u : ℝ)) := by linarith
      have hgap : 0 < M.Gap s a - 2 * (Δ / 4) := by have := hg s a ha; linarith
      have hb := theorem1_part1_upper_case (c := c) (P := M.prior s a)
        (by positivity : 0 < 1 + (h.visibleChild s a u : ℝ)) hgap hcompare
        (hv s a u hm) (hv s (M.isBest s) u hm)
      letI : Finite (M.Action s) := (hreg.finite_branching.choose_spec.2 s).1
      letI := Fintype.ofFinite (M.Action s)
      have hP : M.prior s a ≤ 1 :=
        (Summable.of_finite.le_tsum a (fun b _ => M.prior_nonneg s b)).trans_eq
          (M.prior_sum s)
      have hcoef : c * M.prior s a / (M.Gap s a - 2 * (Δ / 4)) ≤ 2 * c / Δ := by
        apply (div_le_div_iff₀ hgap hΔ).2
        have hPg := mul_le_mul_of_nonneg_left hP (mul_pos hc hΔ).le
        have hG := mul_le_mul_of_nonneg_left (hg s a ha) (show 0 ≤ 2 * c by positivity)
        nlinarith
      have hmono : Real.sqrt (h.visibleParent s u : ℝ) ≤ Real.sqrt (M.parentVisit s t : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast
          (h.visible_parent_le s u).trans (h.updates.parent_monotone s hut.le))
      have hmul := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (h.visibleParent s u : ℝ))
      have hmul' := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 2 * c / Δ by positivity)
      have hlag : (M.childVisit s a t : ℝ) ≤
          (h.visibleChild s a u : ℝ) + lag + 1 := by
        exact_mod_cast (show M.childVisit s a t ≤ h.visibleChild s a u + lag + 1 by
          have := (hlag_prefix u hut).2 a
          omega)
      rw [← div_mul_eq_mul_div] at hb
      dsimp [MCTSModel.Gap] at *
      linarith [Nat.cast_nonneg m₀ (α := ℝ)]
    · have hi := h.updates.child_le_parent s a u
      have hp := (hlag_prefix u hut).1
      have hn : M.childVisit s a t ≤ m₀ + lag := by omega
      have hn' : (M.childVisit s a t : ℝ) ≤ (m₀ : ℝ) + lag := by exact_mod_cast hn
      have hnonneg : 0 ≤ (2 * c / Δ) * Real.sqrt (M.parentVisit s t : ℝ) := by positivity
      linarith
  have hissued_upper {M : MCTSModel} {c : ℝ}
      (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M) :
      ∃ K A : ℝ, 0 ≤ K ∧ 0 < A ∧ ∀ s a t, M.Suboptimal s a →
        (M.childVisit s a t : ℝ) ≤ K + A * Real.sqrt (M.parentVisit s t : ℝ) + h.threads s := by
    obtain ⟨K, A, hK, hA, hu⟩ := hprefix_upper hc h hreg
    exact ⟨K, A, hK, hA, fun s a t => hu s a t (h.threads s)
      (fun u _ => ⟨h.parent_snapshot_lag s u, fun b => h.child_snapshot_lag s b u⟩)⟩
  obtain ⟨K, A, hK, hA, hu⟩ := hissued_upper hc h hreg
  obtain ⟨b, hb, hf⟩ := hreg.finite_branching
  refine ⟨(b : ℝ) * K + (b : ℝ) * A + b, by positivity, ?_⟩
  intro s t
  letI : Finite (M.Action s) := (hf s).1
  have hg := count_gap_sum_le h.updates s t b (hf s).2
    (show 0 ≤ K + A * Real.sqrt (M.parentVisit s t : ℝ) + h.threads s by positivity)
    (fun a ha => hu s a t ha)
  have hT : (1 : ℝ) ≤ h.threads s := by exact_mod_cast h.threads_pos s
  have hKT := mul_le_mul_of_nonneg_left hT (mul_nonneg (Nat.cast_nonneg b) hK)
  have hr : 0 ≤ Real.sqrt (M.parentVisit s t : ℝ) := Real.sqrt_nonneg _
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hK0 : 0 ≤ (b : ℝ) * K := by positivity
  have hA0 : 0 ≤ (b : ℝ) * A := by positivity
  nlinarith [mul_nonneg hK0 hr, mul_nonneg hb0 hr,
    mul_nonneg hA0 (show (0 : ℝ) ≤ h.threads s by positivity)]

private theorem parallel_completed_gap_upper {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s t,
      (h.arrivalCount s t : ℝ) - h.completedChild s (M.isBest s) t ≤
        C * (Real.sqrt (h.arrivalCount s t : ℝ) + h.threads s) := by
  obtain ⟨C, hC, hb⟩ := parallel_issued_gap_upper hc h hreg
  refine ⟨2 * C + 2, by positivity, ?_⟩
  intro s t
  letI : Finite (M.Action s) := (hreg.finite_branching.choose_spec.2 s).1
  have hg := hb s t
  have hp : (h.completedParent s t : ℝ) ≤ M.parentVisit s t := by
    exact_mod_cast h.completedParent_le_issued s t
  have hlag : (M.parentVisit s t : ℝ) ≤ (h.completedParent s t : ℝ) + h.threads s := by
    exact_mod_cast h.parent_outstanding s t
  have hs : (M.childVisit s (M.isBest s) t : ℝ) ≤
      (h.completedChild s (M.isBest s) t : ℝ) + h.threads s := by
    exact_mod_cast h.child_outstanding s (M.isBest s) t
  have hT : (1 : ℝ) ≤ h.threads s := by exact_mod_cast h.threads_pos s
  have hroot : Real.sqrt (M.parentVisit s t : ℝ) ≤
      Real.sqrt (h.arrivalCount s t : ℝ) + h.threads s := by
    have hi := Real.sq_sqrt (show (0 : ℝ) ≤ (M.parentVisit s t : ℝ) by positivity)
    have hv := Real.sq_sqrt (show (0 : ℝ) ≤ (h.arrivalCount s t : ℝ) by positivity)
    have hsr := Real.sqrt_nonneg (M.parentVisit s t : ℝ)
    have hsv := Real.sqrt_nonneg (h.arrivalCount s t : ℝ)
    have hsqT : (h.threads s : ℝ) ≤ (h.threads s : ℝ)^2 := by nlinarith
    have harrival : (h.arrivalCount s t : ℝ) = (h.completedParent s t : ℝ) + 1 := by
      simp [MCTSModel.ParallelExecution.arrivalCount]
    nlinarith [mul_nonneg hsv (show (0 : ℝ) ≤ h.threads s by positivity)]
  have hscale := mul_le_mul_of_nonneg_left hroot hC.le
  have hV : 1 ≤ Real.sqrt (h.arrivalCount s t : ℝ) :=
    Real.one_le_sqrt.mpr (by simp [MCTSModel.ParallelExecution.arrivalCount])
  simp only [MCTSModel.ParallelExecution.arrivalCount, Nat.cast_add, Nat.cast_one] at *
  nlinarith [mul_nonneg hC.le (show (0 : ℝ) ≤ h.threads s by positivity),
    mul_nonneg hC.le (Real.sqrt_nonneg ((h.completedParent s t : ℝ) + 1))]

private theorem parallel_visit_bounds {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M) :
    ∃ B C E R : ℝ, 0 < B ∧ 0 < C ∧ 0 ≤ E ∧ 0 ≤ R ∧ ∃ m₀ : ℕ, ∀ s t,
      ¬ M.isTerminal s → m₀ ≤ h.arrivalCount s t →
      (h.arrivalCount s t : ℝ) - h.completedChild s (M.isBest s) t ≤
        C * (Real.sqrt (h.arrivalCount s t : ℝ) + h.threads s) ∧
      B * Real.sqrt (h.arrivalCount s t : ℝ) - E * h.threads s - R ≤
        (h.arrivalCount s t : ℝ) - h.completedChild s (M.isBest s) t := by
  have hcompleted_gap {M : MCTSModel} {c : ℝ} (h : M.ParallelExecution c)
      (s : M.State) [Finite (M.Action s)] (a : M.Action s)
      (ha : M.Suboptimal s a) (t : ℕ) :
      h.completedChild s a t + h.completedChild s (M.isBest s) t ≤ h.completedParent s t := by
    classical
    letI := Fintype.ofFinite (M.Action s)
    have he := Finset.sum_erase_add (Finset.univ : Finset (M.Action s))
      (fun b => h.completedChild s b t) (Finset.mem_univ (M.isBest s))
    have hl := Finset.single_le_sum (fun b _ => Nat.zero_le (h.completedChild s b t))
      (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩)
    have hs : h.completedParent s t = ∑ a, h.completedChild s a t := by
      simp [MCTSModel.ParallelExecution.completedParent, tsum_fintype]
    rw [← he] at hs
    dsimp only at hs
    omega
  have hlast_snapshot {M : MCTSModel} {c C : ℝ}
      (h : M.ParallelExecution c) (hC : 0 < C)
      (hb : ∀ s t, (M.parentVisit s t : ℝ) - M.childVisit s (M.isBest s) t ≤
        C * (Real.sqrt (M.parentVisit s t : ℝ) + h.threads s))
      (s : M.State) (t : ℕ)
      (hT : (h.threads s : ℝ) ≤ Real.sqrt (M.parentVisit s t : ℝ))
      (hlarge : 8 * C + 8 ≤ Real.sqrt (M.parentVisit s t : ℝ)) :
      ∃ u < t, M.selectedAt s (M.isBest s) u ∧
        (M.parentVisit s t : ℝ) / 4 ≤ h.visibleParent s u ∧
        (M.parentVisit s t : ℝ) / 4 ≤ h.visibleChild s (M.isBest s) u ∧
        h.visibleParent s u ≤ M.parentVisit s t := by
    have hr := Real.sqrt_nonneg (M.parentVisit s t : ℝ)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (M.parentVisit s t : ℝ) by positivity)
    have hprod := mul_nonneg (sub_nonneg.mpr hlarge) hr
    have hgap := hb s t
    have hscale := mul_le_mul_of_nonneg_left hT hC.le
    have hstar : 0 < M.childVisit s (M.isBest s) t := by
      by_contra hh
      have hz : M.childVisit s (M.isBest s) t = 0 := by omega
      rw [hz, Nat.cast_zero, sub_zero] at hgap
      nlinarith
    let u := h.updates.lastSelection s (M.isBest s) t
    obtain ⟨hut, hsel, hcount⟩ := h.updates.lastSelection_spec s (M.isBest s) t hstar
    change u < t at hut
    change M.selectedAt s (M.isBest s) u at hsel
    change M.childVisit s (M.isBest s) t = M.childVisit s (M.isBest s) u + 1 at hcount
    have hlast : (M.childVisit s (M.isBest s) t : ℝ) ≤ (M.parentVisit s u : ℝ) + 1 := by
      have hi := h.updates.child_le_parent s (M.isBest s) u
      exact_mod_cast (show M.childVisit s (M.isBest s) t ≤ M.parentVisit s u + 1 by omega)
    have hparent : (M.parentVisit s t : ℝ) / 2 ≤ M.parentVisit s u := by nlinarith
    have hmono := h.updates.parent_monotone s hut.le
    have hsqrt : Real.sqrt (M.parentVisit s u : ℝ) ≤ Real.sqrt (M.parentVisit s t : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hmono)
    have hgap_u := hb s u
    have hmul := mul_le_mul_of_nonneg_left hsqrt hC.le
    have hvp : (M.parentVisit s u : ℝ) ≤ (h.visibleParent s u : ℝ) + h.threads s := by
      exact_mod_cast h.parent_snapshot_lag s u
    have hvs : (M.childVisit s (M.isBest s) u : ℝ) ≤
        (h.visibleChild s (M.isBest s) u : ℝ) + h.threads s := by
      exact_mod_cast h.child_snapshot_lag s (M.isBest s) u
    refine ⟨u, hut, hsel, ?_, ?_, (h.visible_parent_le s u).trans hmono⟩ <;> nlinarith
  have hsmall_lower {M : MCTSModel} {c : ℝ}
      (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M) :
      ∃ B : ℝ, 0 < B ∧ ∃ m₀ : ℕ, ∀ s t, ¬ M.isTerminal s →
        m₀ ≤ M.parentVisit s t → (h.threads s : ℝ) ≤ Real.sqrt (M.parentVisit s t : ℝ) →
        B * Real.sqrt (M.parentVisit s t : ℝ) - h.threads s ≤
          (h.arrivalCount s t : ℝ) - h.completedChild s (M.isBest s) t := by
    obtain ⟨C, hC, hupp⟩ := parallel_issued_gap_upper hc h hreg
    obtain ⟨mv, hv⟩ := h.uniform_values 1 zero_lt_one
    obtain ⟨p₀, hp₀, hp⟩ := hreg.suboptimal_prior
    obtain ⟨Δmax, hΔmax, hgap⟩ := hreg.gap_upper
    let A := c * p₀ / (Δmax + 3)
    have hA : 0 < A := by dsimp [A]; positivity
    have hlarge : ∀ᶠ m : ℕ in atTop,
        4 * mv ≤ m ∧ max (8 * C + 8) (4 * c) ≤ Real.sqrt (m : ℝ) := by
      filter_upwards [eventually_ge_atTop (4 * mv),
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (max (8 * C + 8) (4 * c)))] with m hm hs
      exact ⟨hm, hs⟩
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hlarge
    refine ⟨A / 2, by positivity, m₀, ?_⟩
    intro s t hnt hm hT
    obtain ⟨hmv, hsize⟩ := hm₀ (M.parentVisit s t) hm
    obtain ⟨u, hut, hsel, hparent, hstar, hle⟩ := hlast_snapshot h hC hupp s t hT
      ((le_max_left _ _).trans hsize)
    have hmvu : mv ≤ h.visibleParent s u := by
      have hh : (4 : ℝ) * mv ≤ M.parentVisit s t := by exact_mod_cast hmv
      have : (mv : ℝ) ≤ h.visibleParent s u := by linarith
      exact_mod_cast this
    letI : Finite (M.Action s) := (hreg.finite_branching.choose_spec.2 s).1
    letI := Fintype.ofFinite (M.Action s)
    have hPstar : M.prior s (M.isBest s) ≤ 1 :=
      (Summable.of_finite.le_tsum (M.isBest s) (fun b _ => M.prior_nonneg s b)).trans_eq
        (M.prior_sum s)
    have hsqrt := Real.sqrt_le_sqrt (show (h.visibleParent s u : ℝ) ≤ M.parentVisit s t by
      exact_mod_cast hle)
    have hbonus : c * M.prior s (M.isBest s) * Real.sqrt (h.visibleParent s u : ℝ) /
        (1 + (h.visibleChild s (M.isBest s) u : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 1 + (h.visibleChild s (M.isBest s) u : ℝ))).2
      have hcoef := mul_le_mul_of_nonneg_left hPstar hc.le
      have hmul := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (h.visibleParent s u : ℝ))
      have hmul' := mul_le_mul_of_nonneg_left hsqrt hc.le
      have hsize' := (le_max_right _ _).trans hsize
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M.parentVisit s t : ℝ) by positivity)
      have hprod := mul_nonneg (sub_nonneg.mpr hsize') (Real.sqrt_nonneg (M.parentVisit s t : ℝ))
      nlinarith
    obtain ⟨a, ha, hpa⟩ := hp s hnt
    have hΔ : 0 < M.Gap s a := hreg.gap_lower.choose_spec.1.trans_le
      (hreg.gap_lower.choose_spec.2 s a ha)
    have hden : 0 < M.Gap s a + 3 * (1 : ℝ) := by linarith
    have hl := theorem1_part1_lower_case (c := c) (P := M.prior s a)
      (by positivity : 0 < 1 + (h.visibleChild s a u : ℝ)) hden
      (h.argmax s (M.isBest s) u hsel a) (hv s a u hmvu) (hv s (M.isBest s) u hmvu) hbonus
    have hcoef : A ≤ c * M.prior s a / (M.Gap s a + 3) := by
      dsimp [A]
      apply (div_le_div_iff₀ (by positivity : 0 < Δmax + 3) (by linarith)).2
      have hP := mul_le_mul_of_nonneg_left hpa hc.le
      have hD := mul_le_mul_of_nonneg_left (hgap s a ha) (mul_pos hc hp₀).le
      have hP' := mul_le_mul_of_nonneg_right hP (show 0 ≤ Δmax + 3 by positivity)
      nlinarith
    have hsqrtlower : Real.sqrt (M.parentVisit s t : ℝ) / 2 ≤
        Real.sqrt (h.visibleParent s u : ℝ) := by
      have hm := Real.sq_sqrt (show (0 : ℝ) ≤ (M.parentVisit s t : ℝ) by positivity)
      have hu := Real.sq_sqrt (show (0 : ℝ) ≤ (h.visibleParent s u : ℝ) by positivity)
      nlinarith [Real.sqrt_nonneg (M.parentVisit s t : ℝ),
        Real.sqrt_nonneg (h.visibleParent s u : ℝ)]
    have hc1 := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (h.visibleParent s u : ℝ))
    have hc2 := mul_le_mul_of_nonneg_left hsqrtlower hA.le
    have hissued : h.visibleChild s a u ≤ M.childVisit s a t :=
      (h.visible_child_le s a u).trans (h.updates.child_monotone s a hut.le)
    have hlag : (h.visibleChild s a u : ℝ) ≤ (h.completedChild s a t : ℝ) + h.threads s := by
      exact_mod_cast hissued.trans (h.child_outstanding s a t)
    have hsum : (h.completedChild s a t : ℝ) + h.completedChild s (M.isBest s) t ≤
        h.completedParent s t := by exact_mod_cast hcompleted_gap h s a ha t
    rw [← div_mul_eq_mul_div] at hl
    dsimp [MCTSModel.Gap] at *
    simp only [MCTSModel.ParallelExecution.arrivalCount, Nat.cast_add, Nat.cast_one]
    nlinarith
  obtain ⟨C, hC, hu⟩ := parallel_completed_gap_upper hc h hreg
  obtain ⟨B, hB, m₀, hl⟩ := hsmall_lower hc h hreg
  refine ⟨B, C, max 1 B, B, hB, hC, by positivity, hB.le, m₀ + 1, ?_⟩
  intro s t hnt hm
  refine ⟨hu s t, ?_⟩
  letI : Finite (M.Action s) := (hreg.finite_branching.choose_spec.2 s).1
  have hcount := h.completedParent_le_issued s t
  have hm' : m₀ ≤ M.parentVisit s t := by
    simp only [MCTSModel.ParallelExecution.arrivalCount] at hm
    omega
  have hsqrt : Real.sqrt (h.arrivalCount s t : ℝ) ≤ Real.sqrt (M.parentVisit s t : ℝ) + 1 := by
    have hc' : (h.completedParent s t : ℝ) ≤ M.parentVisit s t := by exact_mod_cast hcount
    have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ (h.arrivalCount s t : ℝ) by positivity)
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ (M.parentVisit s t : ℝ) by positivity)
    have harrival : (h.arrivalCount s t : ℝ) = (h.completedParent s t : ℝ) + 1 := by
      simp [MCTSModel.ParallelExecution.arrivalCount]
    nlinarith [Real.sqrt_nonneg (h.arrivalCount s t : ℝ), Real.sqrt_nonneg (M.parentVisit s t : ℝ)]
  have hmul := mul_le_mul_of_nonneg_left hsqrt hB.le
  have hE1 := mul_le_mul_of_nonneg_right (le_max_left 1 B)
    (show (0 : ℝ) ≤ h.threads s by positivity)
  by_cases hT : (h.threads s : ℝ) ≤ Real.sqrt (M.parentVisit s t : ℝ)
  · have hlow := hl s t hnt hm' hT
    nlinarith
  · have hEB := mul_le_mul_of_nonneg_right (le_max_right 1 B)
      (show (0 : ℝ) ≤ h.threads s by positivity)
    have hlarge := mul_le_mul_of_nonneg_left (le_of_not_ge hT) hB.le
    have hnonneg : 0 ≤ (h.arrivalCount s t : ℝ) - h.completedChild s (M.isBest s) t := by
      have hb : (h.completedChild s (M.isBest s) t : ℝ) ≤ h.completedParent s t := by
        exact_mod_cast h.completed_child_le_parent s (M.isBest s) t
      simp only [MCTSModel.ParallelExecution.arrivalCount, Nat.cast_add, Nat.cast_one]
      linarith
    nlinarith

/-- A completed selection cohort with at most `K` optimal selections. -/
structure Assumption.CompletedContention {M : MCTSModel} {c : ℝ}
    (h : M.ParallelExecution c) where
  /-- Require contention at these observations. -/
  observed : M.State → ℕ → Prop
  threshold : ℕ
  ρ : ℝ
  K : ℝ
  ρ_pos : 0 < ρ
  K_nonneg : 0 ≤ K
  windows : ∀ s t, observed s t → ¬ M.isTerminal s → threshold ≤ h.arrivalCount s t →
    ∃ u v : ℕ, u ≤ v ∧ v ≤ t ∧
      ρ * (h.threads s : ℝ) ≤ (M.parentVisit s v : ℝ) - M.parentVisit s u ∧
      (M.childVisit s (M.isBest s) v : ℝ) - M.childVisit s (M.isBest s) u ≤ K ∧
      ∀ a, (M.childVisit s a v : ℝ) - M.childVisit s a u ≤ h.completedChild s a t

private noncomputable def parallelEstimates_of_execution {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M)
    (V : ℕ → ℕ → ℕ) (H T : ℕ → ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ n, h.PathEdges (V n) (H n) (T n) (state n) (time n)) :
    Assumption.ParallelEstimates V H T := by
  classical
  choose B C E R hB hC hE hR m₀ hb using parallel_visit_bounds hc h hreg
  refine {
    threshold := m₀
    B := B
    C := C
    E := E
    R := R
    B_pos := hB
    C_pos := hC
    E_nonneg := hE
    R_nonneg := hR
    steps := ?_ }
  intro n x hx hm
  obtain ⟨hnt, hp, ha, hT⟩ := hpath n x hx
  have hlarge : m₀ ≤ h.arrivalCount (state n x) (time n x) := by simpa [hp] using hm
  simpa only [hp, ha, hT] using hb (state n x) (time n x) hnt hlarge

/-- Lemma 4: parallel one-step bounds, with a contention-dependent lower bound. -/
theorem lemma4 {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M)
    (V : ℕ → ℕ → ℕ) (H T : ℕ → ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ n, h.PathEdges (V n) (H n) (T n) (state n) (time n)) :
    (∃ C : ℝ, 0 < C ∧ ∀ s t,
      (h.arrivalCount s t : ℝ) - h.completedChild s (M.isBest s) t ≤
        C * (Real.sqrt (h.arrivalCount s t : ℝ) + h.threads s)) ∧
    (∃ c₀ η : ℝ, 0 < c₀ ∧ 0 < η ∧ ∃ m₀ : ℕ, ∀ s t,
      ¬ M.isTerminal s → m₀ ≤ h.arrivalCount s t →
      (h.threads s : ℝ) ≤ η * Real.sqrt (h.arrivalCount s t : ℝ) →
      c₀ * Real.sqrt (h.arrivalCount s t : ℝ) ≤
        (h.arrivalCount s t : ℝ) - h.completedChild s (M.isBest s) t) ∧
    (∀ (hw : Assumption.CompletedContention h) s t,
      hw.observed s t → ¬ M.isTerminal s → hw.threshold ≤ h.arrivalCount s t →
      2 * hw.K / hw.ρ ≤ (h.threads s : ℝ) →
      hw.ρ / 2 * (h.threads s : ℝ) ≤
        (h.arrivalCount s t : ℝ) - h.completedChild s (M.isBest s) t) ∧
    (∀ hw : Assumption.CompletedContention h,
      (∀ n x, x < H n → hw.observed (state n x) (time n x)) →
      ∃ κ₁ κ₂ : ℝ, 0 < κ₁ ∧ κ₁ ≤ κ₂ ∧ ∃ m : ℝ, ∀ n x,
        x < H n → m ≤ (V n x : ℝ) →
        κ₁ * (Real.sqrt (V n x : ℝ) + T n) ≤ (V n x : ℝ) - V n (x + 1) ∧
        (V n x : ℝ) - V n (x + 1) ≤ κ₂ * (Real.sqrt (V n x : ℝ) + T n)) := by
  have hcontention {M : MCTSModel} {c : ℝ}
      (h : M.ParallelExecution c) (hw : Assumption.CompletedContention h)
      (s : M.State) [Finite (M.Action s)] (t : ℕ)
      (hobs : hw.observed s t) (hnt : ¬ M.isTerminal s)
      (hm : hw.threshold ≤ h.arrivalCount s t) :
      hw.ρ * (h.threads s : ℝ) - hw.K ≤
        (h.arrivalCount s t : ℝ) - h.completedChild s (M.isBest s) t := by
    classical
    letI := Fintype.ofFinite (M.Action s)
    obtain ⟨u, v, _, _, hsize, hopt, hdone⟩ := hw.windows s t hobs hnt hm
    let δ := fun a => (M.childVisit s a v : ℝ) - M.childVisit s a u
    have hv : (M.parentVisit s v : ℝ) = ∑ a, (M.childVisit s a v : ℝ) := by
      exact_mod_cast h.updates.count_identity s v
    have hu : (M.parentVisit s u : ℝ) = ∑ a, (M.childVisit s a u : ℝ) := by
      exact_mod_cast h.updates.count_identity s u
    have hδ : (M.parentVisit s v : ℝ) - M.parentVisit s u = ∑ a, δ a := by
      rw [hv, hu, ← Finset.sum_sub_distrib]
    have hcompleted : (h.completedParent s t : ℝ) = ∑ a, (h.completedChild s a t : ℝ) := by
      simp [MCTSModel.ParallelExecution.completedParent, tsum_fintype]
    have hi := Finset.sum_erase_add (Finset.univ : Finset (M.Action s)) δ
      (Finset.mem_univ (M.isBest s))
    have hd := Finset.sum_erase_add (Finset.univ : Finset (M.Action s))
      (fun a => (h.completedChild s a t : ℝ)) (Finset.mem_univ (M.isBest s))
    have hsum : ∑ a ∈ (Finset.univ : Finset (M.Action s)).erase (M.isBest s), δ a ≤
        ∑ a ∈ (Finset.univ : Finset (M.Action s)).erase (M.isBest s),
          (h.completedChild s a t : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      exact hdone a
    change δ (M.isBest s) ≤ hw.K at hopt
    simp only [MCTSModel.ParallelExecution.arrivalCount, Nat.cast_add, Nat.cast_one]
    linarith
  refine ⟨parallel_completed_gap_upper hc h hreg, ?_, ?_, ?_⟩
  · obtain ⟨B, C, E, R, hB, _, hE, _, m₀, hb⟩ := parallel_visit_bounds hc h hreg
    let η := B / (4 * (E + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    have hEη : E * η ≤ B / 4 := by
      dsimp [η]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (E + 1))).2
      nlinarith
    obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.1
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (4 * R / B)))
    refine ⟨B / 2, η, by positivity, hη, max m₀ m₁, ?_⟩
    intro s t hnt hm hT
    have hl := (hb s t hnt ((le_max_left _ _).trans hm)).2
    have hRbound := (div_le_iff₀ hB).1 (hm₁ _ ((le_max_right _ _).trans hm))
    change 4 * R ≤ Real.sqrt (h.arrivalCount s t : ℝ) * B at hRbound
    have hmul := mul_le_mul_of_nonneg_left hT hE
    have hmul' := mul_le_mul_of_nonneg_right hEη (Real.sqrt_nonneg (h.arrivalCount s t : ℝ))
    nlinarith
  · intro hw s t hobs hnt hm hT
    letI : Finite (M.Action s) := (hreg.finite_branching.choose_spec.2 s).1
    have hb := hcontention h hw s t hobs hnt hm
    have ht := (div_le_iff₀ hw.ρ_pos).1 hT
    nlinarith
  · intro hw hobserved
    let he := parallelEstimates_of_execution hc h hreg V H T state time hpath
    apply lemma4_of_visit_bounds (fun n x => (V n x : ℝ)) H T
      he.B_pos he.C_pos he.E_nonneg he.R_nonneg hw.ρ_pos hw.K_nonneg
      (M₀ := ((max he.threshold hw.threshold : ℕ) : ℝ))
    intro n x hx hm
    have hm' : max he.threshold hw.threshold ≤ V n x := by exact_mod_cast hm
    obtain ⟨hu, hl⟩ := he.steps n x hx ((le_max_left _ _).trans hm')
    obtain ⟨hnt, hp, ha, hT⟩ := hpath n x hx
    letI : Finite (M.Action (state n x)) := (hreg.finite_branching.choose_spec.2 (state n x)).1
    have hw' : hw.threshold ≤ h.arrivalCount (state n x) (time n x) := by
      rw [← hp]
      exact (le_max_right _ _).trans hm'
    refine ⟨hu, hl, ?_⟩
    simpa only [hp, ha, hT] using hcontention h hw (state n x) (time n x)
      (hobserved n x hx) hnt hw'

/-! ## Parallel frontier bounds -/

/-- An unvisited optimal child gives a frontier count of O(T). -/
private theorem parallel_frontier_bound {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M) :
    ∃ A : ℝ, 0 < A ∧ ∀ s t, h.completedChild s (M.isBest s) t = 0 →
      (h.arrivalCount s t : ℝ) ≤ A * h.threads s := by
  obtain ⟨C, hC, hb⟩ := parallel_completed_gap_upper hc h hreg
  refine ⟨4 * C ^ 2 + 2 * C, by nlinarith [sq_nonneg C], ?_⟩
  intro s t hz
  have hg := hb s t
  rw [hz, Nat.cast_zero, sub_zero] at hg
  have hT : (1 : ℝ) ≤ h.threads s := by exact_mod_cast h.threads_pos s
  have hv : (1 : ℝ) ≤ h.arrivalCount s t := by
    simp [MCTSModel.ParallelExecution.arrivalCount]
  have hspos : 0 < Real.sqrt (h.arrivalCount s t : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (h.arrivalCount s t : ℝ) by positivity)
  by_cases hsmall : (h.arrivalCount s t : ℝ) ≤ 2 * C * Real.sqrt (h.arrivalCount s t : ℝ)
  · have hs : Real.sqrt (h.arrivalCount s t : ℝ) ≤ 2 * C :=
      (mul_le_mul_iff_left₀ hspos).1 (by nlinarith)
    have hmul := mul_le_mul_of_nonneg_left hT (show 0 ≤ 4 * C ^ 2 by positivity)
    nlinarith
  · have hbig : 2 * C * Real.sqrt (h.arrivalCount s t : ℝ) < h.arrivalCount s t :=
      lt_of_not_ge hsmall
    nlinarith [mul_nonneg (sq_nonneg C) (show (0 : ℝ) ≤ h.threads s by positivity)]

private theorem depth_theta_succ (H : ℕ → ℕ) (hpos : ∀ᶠ n : ℕ in atTop, 1 ≤ H n) :
    (fun n => (H n : ℝ)) =Θ[∞] (fun n => ((H n + 1 : ℕ) : ℝ)) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with n
    simp only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (Nat.cast_nonneg (H n) (α := ℝ)),
      abs_of_nonneg (show (0 : ℝ) ≤ (H n : ℝ) + 1 by positivity)]
    linarith
  · apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [hpos] with n hn
    have hp : (1 : ℝ) ≤ H n := by exact_mod_cast hn
    simp only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (H n : ℝ) + 1 by positivity),
      abs_of_nonneg (Nat.cast_nonneg (H n) (α := ℝ))]
    linarith

private theorem parallel_frontier_path_data {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M)
    (V : ℕ → ℕ → ℕ) (H T : ℕ → ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hfrontier : ∀ᶠ n : ℕ in atTop,
      h.Frontier (V n) (H n) n (T n) (state n) (time n))
    (hpath : ∀ n, h.PathEdges (V n) (H n) (T n) (state n) (time n)) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, V n 0 = n ∧
      (∀ x ≤ H n, 1 ≤ V n x) ∧ (∀ x < H n, V n (x + 1) < V n x) ∧
      (V n (H n) : ℝ) ≤ A * T n := by
  obtain ⟨A, hA, hb⟩ := parallel_frontier_bound hc h hreg
  refine ⟨A, hA, ?_⟩
  filter_upwards [hfrontier] with n hn
  refine ⟨hn.1, ?_, ?_, ?_⟩
  · intro x hx
    by_cases heq : x = H n
    · rw [heq, hn.2.1]
      exact Nat.succ_pos _
    · have hxH : x < H n := by omega
      rw [(hpath n x hxH).2.1]
      exact Nat.succ_pos _
  · intro x hx
    obtain ⟨_, hp, ha, _⟩ := hpath n x hx
    letI : Finite (M.Action (state n x)) := (hreg.finite_branching.choose_spec.2 (state n x)).1
    rw [hp, ha]
    exact Nat.lt_succ_of_le
      (h.completed_child_le_parent (state n x) (M.isBest (state n x)) (time n x))
  · rw [hn.2.1]
    simpa only [hn.2.2.2.2] using hb (state n (H n)) (time n (H n)) hn.2.2.2.1

private theorem sublinear_threads_pred {T : ℕ → ℕ}
    (hsub : (fun n => (T n : ℝ)) =o[∞] (fun n : ℕ => (n : ℝ))) :
    (fun k => (T (k - 1) : ℝ)) =o[∞] (fun k : ℕ => (k : ℝ)) := by
  refine (hsub.comp_tendsto (tendsto_sub_atTop_nat 1)).trans_isBigO ?_
  apply Asymptotics.IsBigO.of_bound 1
  apply Filter.Eventually.of_forall
  intro k
  simpa only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (k - 1) (α := ℝ)),
    abs_of_nonneg (Nat.cast_nonneg k (α := ℝ)), one_mul] using
    (show ((k - 1 : ℕ) : ℝ) ≤ k by exact_mod_cast Nat.sub_le k 1)

private theorem parallel_eventually_terminal {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (L : ℕ) (T : ℕ → ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hsub : (fun n => (T n : ℝ)) =o[∞] (fun n : ℕ => (n : ℝ)))
    (hpath : ∀ᶠ n : ℕ in atTop,
      h.CappedPathCounts (V n) (H n) (n + 1) L (T n) (state n) (time n)) :
    ∀ᶠ n : ℕ in atTop, H n = L := by
  have hterminal_from_loss
      (N : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (L : ℕ) (T : ℕ → ℕ)
      {C A : ℝ} (hC : 0 < C) (hA : 0 < A)
      (hsub : (fun n => (T n : ℝ)) =o[∞] (fun n : ℕ => (n : ℝ)))
      (hpaths : ∀ᶠ n : ℕ in atTop, N n 0 = n ∧ H n ≤ L ∧
        (H n = L ∨ (N n (H n) : ℝ) ≤ A * T n) ∧
        ∀ x < H n, N n (x + 1) ≤ N n x ∧
          (N n x : ℝ) - N n (x + 1) ≤ C * (Real.sqrt (N n x : ℝ) + T n)) :
      ∀ᶠ n : ℕ in atTop, H n = L := by
    obtain ⟨D, hD, hDeq⟩ : ∃ D : ℝ, 0 < D ∧ D = A + L * C := ⟨_, by positivity, rfl⟩
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hpaths, hsub.bound (show 0 < 1 / (4 * D) by positivity),
      hsqrt.eventually (eventually_ge_atTop (4 * ((L : ℝ) * C))), eventually_ge_atTop 1]
      with n hn ht hs hn1
    by_contra hnot
    obtain ⟨hroot, hL, hfront, hstep⟩ := hn
    have hend : (N n (H n) : ℝ) ≤ A * T n := by
      rcases hfront with h | h
      · exact absurd h hnot
      · exact h
    have hT : (0 : ℝ) ≤ T n := by positivity
    have hpref : ∀ k ≤ H n, (N n k : ℝ) ≤ n ∧
        (n : ℝ) - k * (C * (Real.sqrt (n : ℝ) + T n)) ≤ N n k := by
      intro k
      induction k with
      | zero => intro _; simp [hroot]
      | succ k ih =>
        intro hk
        have hkH : k < H n := by omega
        obtain ⟨hup, hlo⟩ := ih hkH.le
        obtain ⟨hmono, hloss⟩ := hstep k hkH
        have hmono' : (N n (k + 1) : ℝ) ≤ N n k := by exact_mod_cast hmono
        have hsq : C * Real.sqrt (N n k : ℝ) ≤ C * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hup) hC.le
        refine ⟨hmono'.trans hup, ?_⟩
        push_cast
        linarith
    obtain ⟨_, hlast⟩ := hpref (H n) le_rfl
    have hHL : (H n : ℝ) ≤ L := by exact_mod_cast hL
    have hnn : 0 ≤ C * (Real.sqrt (n : ℝ) + T n) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hHL hnn
    simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _ (α := ℝ))] at ht
    have h2 := mul_le_mul_of_nonneg_left ht hD.le
    have hcancel : D * (1 / (4 * D) * (n : ℝ)) = (n : ℝ) / 4 := by field_simp
    rw [hcancel, hDeq] at h2
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)
    have hs' : (L : ℝ) * C * Real.sqrt (n : ℝ) ≤ (n : ℝ) / 4 := by
      nlinarith [mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (n : ℝ))]
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  obtain ⟨C, hC, hgap⟩ := parallel_completed_gap_upper hc h hreg
  obtain ⟨A, hA, hB⟩ := parallel_frontier_bound hc h hreg
  have hd := hterminal_from_loss (fun k x => V (k - 1) x) (fun k => H (k - 1))
    L (fun k => T (k - 1)) hC hA (sublinear_threads_pred hsub) (by
      filter_upwards [(tendsto_sub_atTop_nat 1).eventually hpath, eventually_ge_atTop 1]
        with k hk hk1
      obtain ⟨hroot, hL, hfront, hstep⟩ := hk
      show V (k - 1) 0 = k ∧ H (k - 1) ≤ L ∧
        (H (k - 1) = L ∨ (V (k - 1) (H (k - 1)) : ℝ) ≤ A * T (k - 1)) ∧
        ∀ x < H (k - 1), V (k - 1) (x + 1) ≤ V (k - 1) x ∧
          (V (k - 1) x : ℝ) - V (k - 1) (x + 1) ≤
            C * (Real.sqrt (V (k - 1) x : ℝ) + T (k - 1))
      refine ⟨by omega, hL, ?_, ?_⟩
      · by_cases hHL : H (k - 1) = L
        · exact Or.inl hHL
        · obtain ⟨hv, hz, hT⟩ := hfront (lt_of_le_of_ne hL hHL)
          right
          rw [hv, ← hT]
          exact hB _ _ hz
      · intro x hx
        obtain ⟨_, hv, hv', hT⟩ := hstep x hx
        letI : Finite (M.Action (state (k - 1) x)) :=
          (hreg.finite_branching.choose_spec.2 (state (k - 1) x)).1
        refine ⟨?_, ?_⟩
        · rw [hv, hv']
          exact Nat.le_succ_of_le (h.completed_child_le_parent _ _ _)
        · rw [hv, hv', ← hT]
          exact hgap _ _)
  simpa using (tendsto_add_atTop_nat 1).eventually hd

private theorem parallel_frontier_depth_from_steps
    (V : ℕ → ℕ → ℕ) (H T : ℕ → ℕ) (m : ℕ) (hm : 2 ≤ m)
    {κ C A : ℝ} (hκ : 0 < κ) (hC : 0 < C) (hA : 0 < A)
    (hdata : ∀ᶠ n : ℕ in atTop, V n 0 = n ∧
      (∀ x ≤ H n, 1 ≤ V n x) ∧ (∀ x < H n, V n (x + 1) < V n x) ∧
      (V n (H n) : ℝ) ≤ A * T n)
    (hthreads : ∀ᶠ n : ℕ in atTop, 1 ≤ T n ∧ T n ≤ n)
    (hsteps : ∀ᶠ n : ℕ in atTop, ∀ x < H n, m ≤ V n x →
      κ * (Real.sqrt (V n x : ℝ) + T n) ≤ (V n x : ℝ) - V n (x + 1) ∧
      (V n x : ℝ) - V n (x + 1) ≤ C * (Real.sqrt (V n x : ℝ) + T n)) :
    (fun n => ((H n + 1 : ℕ) : ℝ)) =Θ[∞] DepthIntegral.parallel T := by
  have parallel_potential_upper {a T : ℝ} (ha : 1 ≤ a) (hT : 0 < T) :
      integralPotential (fun y => 1 / (Real.sqrt y + T)) a ≤ a / T := by
    have hrect := reciprocal_integral_rectangles (f := fun y => Real.sqrt y + T)
      (Real.continuous_sqrt.add continuous_const).continuousOn
      (fun y _ => add_pos_of_nonneg_of_pos (Real.sqrt_nonneg y) hT) le_rfl ha
      (fun _ _ _ _ hxy => by simpa [add_comm] using add_le_add_right (Real.sqrt_le_sqrt hxy) T)
    apply hrect.2.trans
    simp only [Real.sqrt_one]
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + T) hT).2
    nlinarith
  -- Telescope the edge integrals and bound the frontier contribution.
  let parallel_frontier_integral_path
      (V : ℕ → ℕ → ℕ) (H T : ℕ → ℕ) (m : ℕ) (hm : 2 ≤ m)
      {κ C A : ℝ} (hκ : 0 < κ) (hC : 0 < C) (hA : 0 ≤ A)
      (hpaths : ∀ᶠ n : ℕ in atTop, V n 0 = n ∧
        (∀ x ≤ H n, 1 ≤ V n x) ∧ (∀ x < H n, V n (x + 1) < V n x))
      (hthreads : ∀ᶠ n : ℕ in atTop, 1 ≤ T n ∧ T n ≤ n)
      (hfrontier : ∀ᶠ n : ℕ in atTop,
        integralPotential (fun y => 1 / (Real.sqrt y + (T n : ℝ))) (V n (H n)) ≤ A)
      (hsteps : ∀ᶠ n : ℕ in atTop, ∀ x < H n, m ≤ V n x →
        κ * (Real.sqrt (V n x : ℝ) + T n) ≤ (V n x : ℝ) - V n (x + 1) ∧
        (V n x : ℝ) - V n (x + 1) ≤ C * (Real.sqrt (V n x : ℝ) + T n)) :
      IntegralPath (fun n => H n + 1) (DepthIntegral.parallel T) := by
    have hstep_integral {a b T κ C : ℝ}
        (ha : 1 ≤ a) (hab : a ≤ b) (hT : 1 ≤ T) (_hC : 0 < C)
        (hlo : κ * (Real.sqrt b + T) ≤ b - a)
        (hhi : b - a ≤ C * (Real.sqrt b + T)) :
        κ ≤ (∫ y in a..b, 1 / (Real.sqrt y + T)) ∧
          (∫ y in a..b, 1 / (Real.sqrt y + T)) ≤ 16 * C ^ 2 + 2 * C := by
      have hden : 0 < Real.sqrt b + T := by positivity
      have hb := parallel_interval_bounds ha hab (by linarith : 0 < T)
      refine ⟨((le_div_iff₀ hden).2 hlo).trans hb.1, hb.2.trans ?_⟩
      have hh := (div_le_iff₀ hden).2 hhi
      rw [mul_div_assoc]
      nlinarith [sq_nonneg C]
    have hintegral_positive (T : ℕ → ℕ)
        (hT : ∀ᶠ n : ℕ in atTop, 1 ≤ T n ∧ T n ≤ n) :
        ∀ᶠ n : ℕ in atTop, (1 / 4 : ℝ) ≤ DepthIntegral.parallel T n := by
      filter_upwards [hT, eventually_ge_atTop 2] with n ht hn
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < T n := by exact_mod_cast (by omega : 0 < T n)
      have hle : (T n : ℝ) ≤ n := by exact_mod_cast ht.2
      have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
        have := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)
        nlinarith [Real.sqrt_nonneg (n : ℝ)]
      apply le_trans _ (parallel_integral_bounds hn' hpos).1
      apply (le_div_iff₀ (by positivity : 0 < 2 * (Real.sqrt (n : ℝ) + (T n : ℝ)))).2
      nlinarith
    classical
    let g := fun n y => 1 / (Real.sqrt y + (T n : ℝ))
    have hgc : ∀ n, ContinuousOn (g n) (Set.Ici 1) := by
      intro n
      apply continuousOn_const.div (Real.continuous_sqrt.add continuous_const).continuousOn
      intro y hy
      change 1 ≤ y at hy
      exact ne_of_gt (add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 (by linarith)) (by positivity))
    have hgp : ∀ n y, 1 ≤ y → 0 ≤ g n y := by intro n y _; dsimp [g]; positivity
    let J := fun n => if hd : ∀ x < H n, V n (x + 1) < V n x then
      (finite_chain_cutoff (V n) (H n) m hd).choose else 0
    refine {
      potential := fun n x => integralPotential (g n) (V n x)
      length := J
      κ := κ
      C := 16 * C ^ 2 + 2 * C
      endpoint := A + m
      tail := (m : ℝ) + 1
      δ := 1 / 4
      κ_pos := hκ
      C_pos := by nlinarith [sq_nonneg C]
      endpoint_nonneg := by positivity
      tail_nonneg := by positivity
      δ_pos := by norm_num
      paths := ?_ }
    filter_upwards [hpaths, hthreads, hfrontier, hsteps,
      hintegral_positive T hthreads] with n hp ht hf hs hI
    have hcut : J n ≤ H n ∧ (J n = H n ∨ V n (J n) < m) ∧
        H n ≤ J n + m ∧ ∀ x < J n, m ≤ V n x := by
      dsimp [J]
      rw [dif_pos hp.2.2]
      exact (finite_chain_cutoff (V n) (H n) m hp.2.2).choose_spec
    have hJpos : (1 : ℝ) ≤ V n (J n) := by exact_mod_cast hp.2.1 _ hcut.1
    refine ⟨by omega, hI, ?_, (show 0 ≤ integralPotential _ _ from
      intervalIntegral.integral_nonneg hJpos (fun x hx => (hgp n) x hx.1)), ?_,
      hcut.1.trans (Nat.le_succ _), ?_, ?_⟩
    · rw [hp.1]
      rfl
    · rcases hcut.2.1 with heq | hsmall
      · rw [heq]
        exact hf.trans (by have := Nat.cast_nonneg m (α := ℝ); linarith)
      · have hTpos : (0 : ℝ) < T n := by exact_mod_cast (by omega : 0 < T n)
        have hbound := parallel_potential_upper hJpos hTpos
        have hT1 : (1 : ℝ) ≤ T n := by exact_mod_cast ht.1
        have hm' : (V n (J n) : ℝ) ≤ m := by exact_mod_cast hsmall.le
        have hdiv : (V n (J n) : ℝ) / T n ≤ (m : ℝ) := by
          apply (div_le_iff₀ hTpos).2
          have hmul := mul_le_mul_of_nonneg_left hT1 (Nat.cast_nonneg m (α := ℝ))
          linarith
        exact (hbound.trans hdiv).trans (by linarith)
    · have hn : (H n : ℝ) ≤ (J n : ℝ) + m := by exact_mod_cast hcut.2.2.1
      push_cast
      linarith
    · intro x hx
      have hxH : x < H n := hx.trans_le hcut.1
      have ha : (1 : ℝ) ≤ V n (x + 1) := by exact_mod_cast hp.2.1 _ (Nat.succ_le_of_lt hxH)
      have hb : (V n (x + 1) : ℝ) ≤ V n x := by exact_mod_cast (hp.2.2 x hxH).le
      simp only [integralPotential]
      rw [intervalIntegral.integral_interval_sub_left
        (((hgc n).mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc (ha.trans hb))
        (((hgc n).mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc ha)]
      exact hstep_integral ha hb (by exact_mod_cast ht.1) hC
        (hs x hxH (hcut.2.2.2 x hx)).1 (hs x hxH (hcut.2.2.2 x hx)).2
  have hf : ∀ᶠ n : ℕ in atTop,
      integralPotential (fun y => 1 / (Real.sqrt y + (T n : ℝ))) (V n (H n)) ≤ A := by
    filter_upwards [hdata, hthreads] with n hn ht
    have hT : (0 : ℝ) < T n := by exact_mod_cast (by omega : 0 < T n)
    apply (parallel_potential_upper (show (1 : ℝ) ≤ V n (H n) by
      exact_mod_cast hn.2.1 _ (le_refl _)) hT).trans
    exact (div_le_iff₀ hT).2 hn.2.2.2
  exact depth_theta_of_integral_path
    (parallel_frontier_integral_path V H T m hm hκ hC hA.le
      (hdata.mono (fun _ hn => ⟨hn.1, hn.2.1, hn.2.2.1⟩)) hthreads hf hsteps)

/-- Theorem 3: fixed parallelism preserves optimal-path depth Θ(√n). -/
theorem theorem3 {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ → ℕ) (T : ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hfrontier : ∀ᶠ n : ℕ in atTop,
      h.Frontier (V n) (H n T) (n + 1) T (state n) (time n))
    (hpath : ∀ n, h.PathEdges (V n) (H n T) T (state n) (time n)) :
    (fun n => (H n T : ℝ)) =Θ[∞] DepthProfile.sqrtSimulationCount := by
  have harrival_depth
      (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ → ℕ)
      (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
      (hfrontier : ∀ᶠ n : ℕ in atTop,
        h.Frontier (V n) (H n T) n T (state n) (time n))
      (hpath : ∀ n, h.PathEdges (V n) (H n T) T (state n) (time n)) :
      (fun n => (H n T : ℝ)) =Θ[∞] DepthProfile.sqrtSimulationCount := by
    have hstep_data : ∃ κ C : ℝ, 0 < κ ∧ κ ≤ C ∧ ∃ m : ℝ, ∀ n x,
        x < H n T → m ≤ (V n x : ℝ) →
        κ * (Real.sqrt (V n x : ℝ) + T) ≤ (V n x : ℝ) - V n (x + 1) ∧
        (V n x : ℝ) - V n (x + 1) ≤ C * (Real.sqrt (V n x : ℝ) + T) := by
      let he := parallelEstimates_of_execution hc h hreg V (fun n => H n T) (fun _ => T)
        state time hpath
      apply lemma4_of_visit_bounds (fun n x => (V n x : ℝ)) (fun n => H n T) (fun _ => T)
        he.B_pos he.C_pos he.E_nonneg he.R_nonneg (by norm_num : (0 : ℝ) < 1)
        (show (0 : ℝ) ≤ T by positivity) (M₀ := (he.threshold : ℝ))
      intro n x hx hm
      obtain ⟨hu, hl⟩ := he.steps n x hx (by exact_mod_cast hm)
      obtain ⟨_, hp, ha, _⟩ := hpath n x hx
      letI : Finite (M.Action (state n x)) := (hreg.finite_branching.choose_spec.2 (state n x)).1
      have hle := h.completed_child_le_parent (state n x) (M.isBest (state n x)) (time n x)
      have hle' : h.completedChild (state n x) (M.isBest (state n x)) (time n x) ≤
          h.arrivalCount (state n x) (time n x) := hle.trans (Nat.le_succ _)
      refine ⟨hu, hl, ?_⟩
      simp only [one_mul, sub_self]
      exact sub_nonneg.mpr (by rw [hp, ha]; exact_mod_cast hle')
    obtain ⟨κ, C, hκ, hκC, m, hstep⟩ := hstep_data
    obtain ⟨A, hA, hdata⟩ :=
      parallel_frontier_path_data hc h hreg V (fun n => H n T) (fun _ => T)
        state time hfrontier hpath
    have hT : 1 ≤ T := by
      obtain ⟨n, hn⟩ := hfrontier.exists
      exact (h.threads_pos (state n (H n T))).trans_eq hn.2.2.2.2
    have hthreads : ∀ᶠ n : ℕ in atTop, 1 ≤ (fun _ => T) n ∧ (fun _ => T) n ≤ n :=
      (eventually_ge_atTop T).mono (fun _ hn => ⟨hT, hn⟩)
    obtain ⟨m₁, hm₁⟩ := exists_nat_ge m
    have hlevels : (fun n => ((H n T + 1 : ℕ) : ℝ)) =Θ[∞] DepthIntegral.parallel (fun _ => T) := by
      apply parallel_frontier_depth_from_steps V (fun n => H n T) (fun _ => T) (max 2 m₁)
        (le_max_left _ _) hκ (hκ.trans_le hκC) hA hdata hthreads
      apply Filter.Eventually.of_forall
      intro n x hx hm
      exact hstep n x hx (hm₁.trans (by exact_mod_cast (le_max_right 2 m₁).trans hm))
    have hprogress : ∀ᶠ n : ℕ in atTop, 1 ≤ H n T := by
      filter_upwards [hdata,
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (A * (T : ℝ)))] with n hn hlarge
      by_contra hz
      have heq : H n T = 0 := by omega
      have hbound := hn.2.2.2
      rw [heq, hn.1] at hbound
      linarith
    have hsmall : (fun _ : ℕ => (T : ℝ)) =O[∞] DepthProfile.sqrtSimulationCount := by
      apply Asymptotics.IsBigO.of_bound (T : ℝ)
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hs : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
      simpa only [DepthProfile.sqrtSimulationCount, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg T (α := ℝ)), abs_of_nonneg (Real.sqrt_nonneg _)] using
        le_mul_of_one_le_right (Nat.cast_nonneg T (α := ℝ)) hs
    exact ((depth_theta_succ (fun n => H n T) hprogress).trans hlevels).trans
      ((parallel_integral_theta_rate (fun _ => T) (Filter.Eventually.of_forall (fun _ => hT))).trans
        (parallel_rate_small (fun _ => T) hsmall))
  have hd := harrival_depth
    (fun k x => V (k - 1) x) (fun k t => H (k - 1) t)
    (fun k x => state (k - 1) x) (fun k x => time (k - 1) x) (by
      filter_upwards [(tendsto_sub_atTop_nat 1).eventually hfrontier, eventually_ge_atTop 1]
        with k hk hk1
      simpa only [Nat.sub_add_cancel hk1] using hk)
    (fun k => hpath (k - 1))
  have hs := And.intro (hd.1.comp_tendsto (tendsto_add_atTop_nat 1))
    (hd.2.comp_tendsto (tendsto_add_atTop_nat 1))
  have hh : (fun n => (H n T : ℝ)) =Θ[∞]
      (fun n => Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
    simpa only [Function.comp_def, Nat.add_sub_cancel, DepthProfile.sqrtSimulationCount] using hs
  exact hh.trans sqrtSimulationCount_succ_equiv

/-- Theorem 3, capped: fixed parallelism eventually reaches terminal depth L. -/
theorem theorem3_capped {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ → ℕ) (T L : ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hpath : ∀ᶠ n : ℕ in atTop,
      h.CappedPathCounts (V n) (H n T) (n + 1) L T (state n) (time n)) :
    ∀ᶠ n : ℕ in atTop, H n T = L :=
  parallel_eventually_terminal hc h hreg V (fun n => H n T) L (fun _ => T) state time
    (Asymptotics.isLittleO_const_left.2
      (Or.inr (tendsto_natCast_atTop_atTop.congr (fun n => by simp)))) hpath

/-- Theorem 4: the parallel depth integral and both thread regimes for T = o(n). -/
theorem theorem4 {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M)
    (hw : Assumption.CompletedContention h)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ → ℕ) (T : ℕ → ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hthreads : ∀ᶠ n : ℕ in atTop, 1 ≤ T n)
    (hfrontier : ∀ᶠ n : ℕ in atTop,
      h.Frontier (V n) (H n (T n)) (n + 1) (T n) (state n) (time n))
    (hpath : ∀ n, h.PathEdges (V n) (H n (T n)) (T n) (state n) (time n))
    (hobserved : ∀ n x, x < H n (T n) → hw.observed (state n x) (time n x))
    (hsub : (fun n => (T n : ℝ)) =o[∞] (fun n : ℕ => (n : ℝ))) :
    ((fun n => (H n (T n) : ℝ)) =Θ[∞] DepthIntegral.parallel T) ∧
    (((fun n => (T n : ℝ)) =o[∞] DepthProfile.sqrtSimulationCount) →
      (fun n => (H n (T n) : ℝ)) =Θ[∞] DepthProfile.sqrtSimulationCount) ∧
    ((DepthProfile.sqrtSimulationCount =o[∞] (fun n => (T n : ℝ))) →
      (fun n => (H n (T n) : ℝ)) =Θ[∞] DepthProfile.nOverThreads T) := by
  have hlarge_rate
      (hlarge : DepthProfile.sqrtSimulationCount =O[∞] (fun n => (T n : ℝ))) :
      DepthIntegral.parallelRate T =Θ[∞] DepthProfile.nOverThreads T := by
    obtain ⟨C, hC, hbound⟩ := hlarge.exists_pos
    have hpoint : ∀ᶠ n : ℕ in atTop,
        1 / (1 + C) * DepthProfile.nOverThreads T n ≤ DepthIntegral.parallelRate T n ∧
        DepthIntegral.parallelRate T n ≤ DepthProfile.nOverThreads T n := by
      filter_upwards [hbound.bound, hthreads] with n hn hnT
      have hTpos : (0 : ℝ) < (T n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hnT
      have hs : Real.sqrt (n : ℝ) ≤ C * (T n : ℝ) := by
        simpa [DepthProfile.sqrtSimulationCount, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))] using hn
      have hden : 0 < Real.sqrt (n : ℝ) + (T n : ℝ) := by positivity
      have hCT : 0 < (1 + C) * (T n : ℝ) := by positivity
      dsimp [DepthIntegral.parallelRate, DepthProfile.nOverThreads]
      constructor
      · calc
          1 / (1 + C) * ((n : ℝ) / (T n : ℝ)) = (n : ℝ) / ((1 + C) * (T n : ℝ)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
          _ ≤ (n : ℝ) / (Real.sqrt (n : ℝ) + (T n : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) hden (by nlinarith)
      · exact div_le_div_of_nonneg_left (by positivity) hTpos
          (by nlinarith [Real.sqrt_nonneg (n : ℝ)])
    apply theta_of_eventual_sandwich
    · exact Filter.Eventually.of_forall (fun n => by dsimp [DepthIntegral.parallelRate]; positivity)
    · exact Filter.Eventually.of_forall (fun n => by dsimp [DepthProfile.nOverThreads]; positivity)
    · exact ⟨1, by norm_num, hpoint.mono (fun _ hn => by simpa using hn.2)⟩
    · exact ⟨1 / (1 + C), by positivity, hpoint.mono (fun _ hn => hn.1)⟩
  have harrival_depth
      (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ → ℕ) (T : ℕ → ℕ)
      (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
      (hthreads : ∀ᶠ n : ℕ in atTop, 1 ≤ T n)
      (hfrontier : ∀ᶠ n : ℕ in atTop,
        h.Frontier (V n) (H n (T n)) n (T n) (state n) (time n))
      (hpath : ∀ n, h.PathEdges (V n) (H n (T n)) (T n) (state n) (time n))
      (hobserved : ∀ n x, x < H n (T n) → hw.observed (state n x) (time n x))
      (hsub : (fun n => (T n : ℝ)) =o[∞] (fun n : ℕ => (n : ℝ))) :
      (fun n => (H n (T n) : ℝ)) =Θ[∞] DepthIntegral.parallel T := by
    have hthread_bound : ∀ᶠ n : ℕ in atTop, T n ≤ n := by
      filter_upwards [hsub.bound one_pos] with n hn
      simpa only [Real.norm_natCast, one_mul, Nat.cast_le] using hn
    obtain ⟨A, hA, hdata⟩ :=
      parallel_frontier_path_data hc h hreg V (fun n => H n (T n)) T state time hfrontier hpath
    obtain ⟨κ, C, hκ, hκC, m, hstep⟩ :=
      (lemma4 hc h hreg V (fun n => H n (T n)) T state time hpath).2.2.2 hw hobserved
    obtain ⟨m₁, hm₁⟩ := exists_nat_ge m
    have hlevels : (fun n => ((H n (T n) + 1 : ℕ) : ℝ)) =Θ[∞] DepthIntegral.parallel T := by
      apply parallel_frontier_depth_from_steps V (fun n => H n (T n)) T (max 2 m₁)
        (le_max_left _ _) hκ (hκ.trans_le hκC) hA hdata (hthreads.and hthread_bound)
      apply Filter.Eventually.of_forall
      intro n x hx hm
      exact hstep n x hx (hm₁.trans (by exact_mod_cast (le_max_right 2 m₁).trans hm))
    have hprogress : ∀ᶠ n : ℕ in atTop, 1 ≤ H n (T n) := by
      filter_upwards [hdata, hsub.bound (show 0 < 1 / (2 * A) by positivity),
        eventually_ge_atTop 1] with n hn ht hn1
      simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _ (α := ℝ))] at ht
      have hmul := mul_le_mul_of_nonneg_left ht hA.le
      have hcancel : A * (1 / (2 * A) * (n : ℝ)) = (n : ℝ) / 2 := by field_simp
      rw [hcancel] at hmul
      by_contra hz
      have heq : H n (T n) = 0 := by omega
      have hb := hn.2.2.2
      rw [heq, hn.1] at hb
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn1
      linarith
    exact (depth_theta_succ (fun n => H n (T n)) hprogress).trans hlevels
  have hintegral_shift :
      (fun n => ∫ m in (1 : ℝ)..((n + 1 : ℕ) : ℝ), 1 / (Real.sqrt m + (T n : ℝ)))
        =Θ[∞] DepthIntegral.parallel T := by
    have hb : ∀ᶠ n : ℕ in atTop, 0 ≤ DepthIntegral.parallel T n ∧
        DepthIntegral.parallel T n ≤
          (∫ m in (1 : ℝ)..((n + 1 : ℕ) : ℝ), 1 / (Real.sqrt m + (T n : ℝ))) ∧
        (∫ m in (1 : ℝ)..((n + 1 : ℕ) : ℝ), 1 / (Real.sqrt m + (T n : ℝ))) ≤
          2 * DepthIntegral.parallel T n := by
      filter_upwards [hthreads, eventually_ge_atTop 2] with n ht hn
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have ht' : (0 : ℝ) < T n := by exact_mod_cast Nat.zero_lt_of_lt ht
      let g := fun m : ℝ => 1 / (Real.sqrt m + (T n : ℝ))
      have hg : Continuous g := continuous_const.div
        (Real.continuous_sqrt.add continuous_const)
        (fun m => ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg m) ht'))
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (μ := MeasureTheory.volume)
        (hg.intervalIntegrable 1 (n : ℝ)) (hg.intervalIntegrable (n : ℝ) ((n + 1 : ℕ) : ℝ))
      have hpos : 0 ≤ ∫ m in (n : ℝ)..((n + 1 : ℕ) : ℝ), g m :=
        intervalIntegral.integral_nonneg (by push_cast; linarith)
          (fun _ _ => by dsimp [g]; positivity)
      have hu : (∫ m in (n : ℝ)..((n + 1 : ℕ) : ℝ), g m) ≤
          1 / (Real.sqrt (n : ℝ) + (T n : ℝ)) := by
        have hh := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
          (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by push_cast; linarith)
          (hg.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _ : IntervalIntegrable
            (fun _ : ℝ => 1 / (Real.sqrt (n : ℝ) + (T n : ℝ))) MeasureTheory.volume
            (n : ℝ) ((n + 1 : ℕ) : ℝ))
          (fun m hm => one_div_le_one_div_of_le
            (by positivity : 0 < Real.sqrt (n : ℝ) + (T n : ℝ))
            (by linarith [Real.sqrt_le_sqrt hm.1]))
        simpa only [intervalIntegral.integral_const, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_left, smul_eq_mul, one_mul] using hh
      have hl := (parallel_integral_bounds hn' ht').1
      have hden : 0 < Real.sqrt (n : ℝ) + (T n : ℝ) := by positivity
      have hone : 1 / (Real.sqrt (n : ℝ) + (T n : ℝ)) ≤
          (n : ℝ) / (2 * (Real.sqrt (n : ℝ) + (T n : ℝ))) := by
        apply (div_le_div_iff₀ hden (by positivity)).2
        nlinarith
      change _ ≤ DepthIntegral.parallel T n at hl
      have hi : 0 ≤ DepthIntegral.parallel T n :=
        (by positivity : (0 : ℝ) ≤ 1 / (Real.sqrt (n : ℝ) + (T n : ℝ))).trans (hone.trans hl)
      change DepthIntegral.parallel T n + _ = _ at hsplit
      dsimp [g] at hsplit hpos hu
      exact ⟨hi, by linarith, by linarith [hone.trans hl]⟩
    apply theta_of_eventual_sandwich
    · exact hb.mono (fun _ hn => hn.1.trans hn.2.1)
    · exact hb.mono (fun _ hn => hn.1)
    · exact ⟨2, by norm_num, hb.mono (fun _ hn => hn.2.2)⟩
    · exact ⟨1, by norm_num, hb.mono (fun _ hn => by simpa using hn.2.1)⟩
  have hd := harrival_depth
    (fun k x => V (k - 1) x) (fun k t => H (k - 1) t) (fun k => T (k - 1))
    (fun k x => state (k - 1) x) (fun k x => time (k - 1) x)
    ((tendsto_sub_atTop_nat 1).eventually hthreads) (by
      filter_upwards [(tendsto_sub_atTop_nat 1).eventually hfrontier, eventually_ge_atTop 1]
        with k hk hk1
      simpa only [Nat.sub_add_cancel hk1] using hk)
    (fun k => hpath (k - 1))
    (fun k x hx => hobserved (k - 1) x hx)
    (sublinear_threads_pred hsub)
  have hs := And.intro (hd.1.comp_tendsto (tendsto_add_atTop_nat 1))
    (hd.2.comp_tendsto (tendsto_add_atTop_nat 1))
  have hh : (fun n => (H n (T n) : ℝ)) =Θ[∞]
      (fun n => ∫ m in (1 : ℝ)..((n + 1 : ℕ) : ℝ), 1 / (Real.sqrt m + (T n : ℝ))) := by
    simpa only [Function.comp_def, Nat.add_sub_cancel, DepthIntegral.parallel] using hs
  have hdepth := hh.trans hintegral_shift
  have hrate := hdepth.trans (parallel_integral_theta_rate T hthreads)
  exact ⟨hdepth, fun hsmall => hrate.trans (parallel_rate_small T hsmall.isBigO),
    fun hlarge => hrate.trans (hlarge_rate hlarge.isBigO)⟩

/-- Theorem 4, capped: sublinear parallelism eventually reaches L without contention. -/
theorem theorem4_capped {M : MCTSModel} {c : ℝ}
    (hc : 0 < c) (h : M.ParallelExecution c) (hreg : Assumption.Regularity M)
    (V : ℕ → ℕ → ℕ) (H : ℕ → ℕ → ℕ) (L : ℕ) (T : ℕ → ℕ)
    (state : ℕ → ℕ → M.State) (time : ℕ → ℕ → ℕ)
    (hsub : (fun n => (T n : ℝ)) =o[∞] (fun n : ℕ => (n : ℝ)))
    (hpath : ∀ᶠ n : ℕ in atTop,
      h.CappedPathCounts (V n) (H n (T n)) (n + 1) L (T n) (state n) (time n)) :
    ∀ᶠ n : ℕ in atTop, H n (T n) = L :=
  parallel_eventually_terminal hc h hreg V (fun n => H n (T n)) L T state time hsub hpath

end MCTSCharacterization
