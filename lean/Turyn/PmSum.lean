import Mathlib

open Finset BigOperators

theorem sum_of_pm_ones_mod_two (k : Nat) (f : Nat → Int)
    (h : ∀ i ∈ Finset.range k, f i = 1 ∨ f i = -1) :
    (∑ i ∈ Finset.range k, f i) % 2 = (k : Int) % 2 := by
  rw [Finset.sum_int_mod]
  rw [Finset.sum_congr rfl fun i hi => by rcases h i hi with H | H <;> rw [H]; norm_num]
  norm_num

theorem sum_of_pm_ones_odd_iff (k : Nat) (f : Nat → Int)
    (h : ∀ i ∈ Finset.range k, f i = 1 ∨ f i = -1) :
    Odd (∑ i ∈ Finset.range k, f i) ↔ Odd k := by
  have h_mod := sum_of_pm_ones_mod_two k f h
  rw [Int.odd_iff, Nat.odd_iff]
  omega
