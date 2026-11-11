import BeaverStructural.BB7.DigitsVals
/-! The BB(7) champion's step count τ and score σ: their last 200 decimal digits, residues mod 2^20 and 10^6, and the
lowest 40 base-32 digits of τ. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
theorem tauX_val : (8574 + C1 4 + (C2 12 0 + T0part 3) + (C2 65532 1 + (V 1).2.1) + (C2 Ares 2 + (V 2).2.2) +
    (C2 Ares 3 + (V 3).2.2) + (C2 Ares 4 + (V 4).2.2) + (C2 Ares 5 + (V 5).2.2) + (C2 Ares 6 + (V 6).2.2) +
    (C2 Ares 7 + (V 7).2.2) + (C2 Ares 8 + (V 8).2.2) + (C2 Ares 9 + (V 9).2.2) + (C2 Ares 10 + (V 10).2.2) +
    CH Ares 12) % M = 10442722074196456773707640344163283107608038313650144315814389328319446910761894323931867085376411580682445199494700647587803129645200041753088294078160945237875590633254874041202959286480341950034543 := by
  rw [V1_val, V2_val, V3_val, V4_val, V5_val, V6_val, V7_val, V8_val, V9_val, V10_val]
  decide +kernel

set_option maxHeartbeats 0 in
theorem sigmaX_val : (3 * Ares + 34) % M = 12897809075781567187510870723274308261486089663242393885290451904435315345520726377730964080560052153267706661570675282053969566167812736363848524885873710436586090617800479560014295845226060298846230 := by decide +kernel

/-- τ mod 10^200. -/
theorem tau_mod_ten200 : tau % 10 ^ 200 = 10442722074196456773707640344163283107608038313650144315814389328319446910761894323931867085376411580682445199494700647587803129645200041753088294078160945237875590633254874041202959286480341950034543 := by
  rw [← M_eq]; exact Eq.trans tau_mod tauX_val

/-- σ mod 10^200. -/
theorem sigma_mod_ten200 : sigma % 10 ^ 200 = 12897809075781567187510870723274308261486089663242393885290451904435315345520726377730964080560052153267706661570675282053969566167812736363848524885873710436586090617800479560014295845226060298846230 := by
  rw [← M_eq]; exact Eq.trans sigma_mod sigmaX_val

theorem tau_mod_two20 : tau % 2 ^ 20 = 815727 := by
  rw [← Nat.mod_mod_of_dvd tau (show 2 ^ 20 ∣ 10 ^ 200 by decide +kernel), tau_mod_ten200]; decide +kernel

theorem sigma_mod_two20 : sigma % 2 ^ 20 = 22 := by
  rw [← Nat.mod_mod_of_dvd sigma (show 2 ^ 20 ∣ 10 ^ 200 by decide +kernel), sigma_mod_ten200]; decide +kernel

theorem tau_mod_ten6 : tau % 10 ^ 6 = 34543 := by
  rw [← Nat.mod_mod_of_dvd tau (show 10 ^ 6 ∣ 10 ^ 200 by decide +kernel), tau_mod_ten200]; decide +kernel

theorem sigma_mod_ten6 : sigma % 10 ^ 6 = 846230 := by
  rw [← Nat.mod_mod_of_dvd sigma (show 10 ^ 6 ∣ 10 ^ 200 by decide +kernel), sigma_mod_ten200]; decide +kernel

theorem tau_mod_32_40 : tau % 32 ^ 40 = 1606938044258990275541962092341162602522202992674487193596527 := by
  rw [← Nat.mod_mod_of_dvd tau (show 32 ^ 40 ∣ 10 ^ 200 by decide +kernel), tau_mod_ten200]; decide +kernel

/-- The base-32 digit of τ at place i < 40 is that of τ mod 32^40. -/
theorem tau_digit32 (i : ℕ) (hi : i < 40) : tau / 32 ^ i % 32 = tau % 32 ^ 40 / 32 ^ i % 32 := by
  rw [show 32 ^ 40 = 32 ^ i * 32 ^ (40 - i) by rw [← pow_add]; congr 1; omega, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 32 (by omega))]

/-- The lowest 40 base-32 digits of τ, lowest first: 15, 19, 28, 24, 30, 29, 1, 0, 16, 0, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31. -/
theorem tau_digits32 : (List.range 40).map (fun i => tau / 32 ^ i % 32) = [15, 19, 28, 24, 30, 29, 1, 0, 16, 0, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31] := by
  rw [List.map_congr_left (fun i hi => tau_digit32 i (List.mem_range.1 hi)), tau_mod_32_40]
  decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.tau_mod_ten200
#print axioms BeaverStructural.BB7.sigma_mod_ten200
#print axioms BeaverStructural.BB7.tau_mod_two20
#print axioms BeaverStructural.BB7.sigma_mod_two20
#print axioms BeaverStructural.BB7.tau_mod_ten6
#print axioms BeaverStructural.BB7.sigma_mod_ten6
#print axioms BeaverStructural.BB7.tau_mod_32_40
#print axioms BeaverStructural.BB7.tau_digits32
