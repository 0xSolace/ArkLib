import Mathlib.Data.Nat.Choose.Basic

theorem test_choose : 2^128 < Nat.choose 512 256 := by decide
