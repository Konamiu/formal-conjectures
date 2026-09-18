/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesForMathlib.Data.Set.Density
import FormalConjectures.ErdosProblems.«486».Main

open Filter Topology Finset Real

namespace Erdos486Bridge

/-- The real-cutoff logarithmic sum of plby's formalisation, at a cutoff `x > 0`, agrees with the
integer-cutoff sum of `Set.HasLogDensity` at `⌈x⌉₊ - 1`. -/
theorem logSum_eq (B : Set ℕ) {x : ℝ} (hx : 0 < x) :
    open scoped Classical in
    Erdos486.logSum B x = ∑ k ≤ ⌈x⌉₊ - 1 with k ∈ B, (k : ℝ)⁻¹ := by
  classical
  unfold Erdos486.logSum
  rw [Finset.sum_filter]
  have hpos : 0 < ⌈x⌉₊ := Nat.ceil_pos.2 hx
  have hIic : Finset.Iic (⌈x⌉₊ - 1) = Finset.range ⌈x⌉₊ := by
    ext m
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  rw [hIic]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmx : (m : ℝ) < x := by
    have := Nat.ceil_lt_add_one hx.le
    have hm' : (m : ℝ) + 1 ≤ ⌈x⌉₊ := by exact_mod_cast Finset.mem_range.1 hm
    linarith
  by_cases hB : m ∈ B <;> simp [hB, hmx]

/-- `log n / log (n + 1) → 1`. -/
theorem tendsto_log_div_log_add_one :
    Tendsto (fun n : ℕ => Real.log n / Real.log (n + 1)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => (Real.log (n + 1) - Real.log n) / Real.log (n + 1)) atTop
      (𝓝 0) :=
    Real.tendsto_log_nat_add_one_sub_log.div_atTop
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have h2 : Tendsto (fun n : ℕ => 1 - (Real.log (n + 1) - Real.log n) / Real.log (n + 1)) atTop
      (𝓝 (1 - 0)) := tendsto_const_nhds.sub h1
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : 0 < Real.log (n + 1) := Real.log_pos (by norm_cast; omega)
  field_simp
  ring

/-- `x ↦ ⌈x⌉₊ - 1` tends to infinity. -/
theorem tendsto_ceil_sub_one : Tendsto (fun x : ℝ => ⌈x⌉₊ - 1) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun N => ⟨(N + 1 : ℕ), fun x hx => ?_⟩
  have h1 : ((N + 1 : ℕ) : ℝ) ≤ ⌈x⌉₊ := hx.trans (Nat.le_ceil x)
  have h2 : N + 1 ≤ ⌈x⌉₊ := by exact_mod_cast h1
  omega

/-- `log (⌈x⌉₊ - 1) / log x → 1`. -/
theorem tendsto_log_ceil_sub_one_div_log :
    Tendsto (fun x : ℝ => Real.log (⌈x⌉₊ - 1 : ℕ) / Real.log x) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_log_div_log_add_one.comp
    tendsto_ceil_sub_one) tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hn : 1 ≤ ⌈x⌉₊ - 1 := by
      have : (2 : ℕ) ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
      omega
    have hxle : x ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 := by
      have := Nat.le_ceil x
      have h' : ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 = ⌈x⌉₊ := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
      linarith
    have h0 : 0 ≤ Real.log (⌈x⌉₊ - 1 : ℕ) := Real.log_nonneg (by exact_mod_cast hn)
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    simp only [Function.comp]
    exact div_le_div_of_nonneg_left h0 hlx (Real.log_le_log (by linarith) hxle)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hn1 : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := by
      have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x)
      have h2 : (2 : ℕ) ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      linarith
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hn : (1 : ℝ) ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) := by
      have h2 : (2 : ℕ) ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
      exact_mod_cast (show 1 ≤ ⌈x⌉₊ - 1 by omega)
    exact div_le_one_of_le₀ (Real.log_le_log (by linarith) hn1.le) hlx.le

/-- Integer-cutoff logarithmic density (`Set.HasLogDensity`) implies plby's real-cutoff version. -/
theorem hasLogDensity_of (B : Set ℕ) {d : ℝ} (h : B.HasLogDensity d) :
    Erdos486.HasLogDensity B d := by
  classical
  unfold Erdos486.HasLogDensity
  unfold Set.HasLogDensity at h
  have hseq := h.comp tendsto_ceil_sub_one
  have hprod := hseq.mul tendsto_log_ceil_sub_one_div_log
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
  have h3 : (3 : ℕ) ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans (Nat.le_ceil x)
  have hn : (2 : ℝ) ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ ⌈x⌉₊ - 1 by omega)
  have hlx : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  have h0 : Real.log (⌈x⌉₊ - 1 : ℕ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  simp only [Function.comp, Erdos486.logAverage]
  rw [logSum_eq B (by linarith), ← Finset.sum_div]
  field_simp

end Erdos486Bridge

namespace Erdos486Bridge

open Erdos486 in
/-- The formal-conjectures statement of Erdős 486 is false, as a consequence of
`Erdos486.not_erdos_486`. -/
theorem erdos_486_false :
    ¬ ∀ X : (n : ℕ) → Set (ZMod n),
      ∃ d, {m : ℕ | ∀ n, 0 < n → n < m → (m : ZMod n) ∉ X n}.HasLogDensity d := by
  classical
  intro h
  apply Erdos486.erdos486_negative
  intro A X hA0
  -- Extend `X` by `∅` outside `A`.
  let X' : (n : ℕ) → Set (ZMod n) := fun n => if hn : n ∈ A then X ⟨n, hn⟩ else ∅
  obtain ⟨d, hd⟩ := h X'
  refine ⟨d, Erdos486Bridge.hasLogDensity_of _ ?_⟩
  -- The two survivor sets agree on positive integers, hence have the same logarithmic sums.
  unfold Set.HasLogDensity at hd ⊢
  refine hd.congr fun N => ?_
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have key : (∀ n, 0 < n → n < m → (m : ZMod n) ∉ X' n) ↔ m ∈ Erdos486.survivors A X := by
      simp only [Erdos486.survivors, Set.mem_ofPred_eq]
      constructor
      · intro hX
        refine ⟨hm, fun n hn => ?_⟩
        have := hX n (Nat.pos_of_ne_zero fun h0 => hA0 (h0 ▸ n.2)) hn
        simpa [X', n.2] using this
      · rintro ⟨-, hX⟩ n hn0 hnm
        by_cases hnA : n ∈ A
        · simpa [X', hnA] using hX ⟨n, hnA⟩ hnm
        · simp [X', hnA]
    simp only [Set.mem_ofPred_eq, key]

end Erdos486Bridge
