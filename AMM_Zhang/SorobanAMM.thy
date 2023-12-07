theory SorobanAMM
  imports HOL.Real
begin

sledgehammer_params [timeout=300]

section "Pool state"

record pool_state =
  \<comment> \<open>A liquidity pool between tokens x and y; l is the token representing pool shares\<close>
  x :: real
  y :: real
  l :: real

definition deposit_amounts where
  "deposit_amounts desired_a min_a desired_b min_b reserve_a reserve_b \<equiv>
    if (reserve_a = 0 \<and> reserve_b = 0)
    then Some (desired_a, desired_b)
    else let amount_b = (desired_a*reserve_b)/reserve_a in
      if (amount_b \<le> desired_b)
      then
        if (amount_b < min_b)
        then None
        else Some (desired_a, amount_b)
      else let amount_a = (desired_b*reserve_a)/reserve_b in
        if (amount_a > desired_a \<or> amount_a < min_a)
        then None
        else Some (amount_a, desired_b)"

lemma deposit_amounts_property:
  assumes "da \<ge> (0::real)" and "db \<ge> 0" and "ma \<ge> 0" and "mb \<ge> 0" and "ra \<ge> a" and "rb \<ge> 0"
    and "ma \<le> da" and "mb \<le> db"
    and "deposit_amounts da ma db mb ra rb = Some (a, b)"
  shows "ma \<le> a" and "mb \<le> b" and "a \<le> da" and "b \<le> db" and "(ra \<noteq> 0 \<or> rb \<noteq> 0) \<longrightarrow> a*rb = b*ra"
    and "(ra = 0 \<and> rb = 0) \<longrightarrow> a = da \<and> b = db" and "(ra \<noteq> 0 \<and> rb \<noteq> 0) \<longrightarrow> a/ra = b/rb"
proof -
  show "ma \<le> a"
    using assms unfolding deposit_amounts_def
    by (simp split:if_splits add:Let_def; force)
  show "mb \<le> b"
    using assms unfolding deposit_amounts_def
    by (simp split:if_splits add:Let_def; force)
  show "a \<le> da"
    using assms unfolding deposit_amounts_def
    by (simp split:if_splits add:Let_def; force)
  show "b \<le> db"
    using assms unfolding deposit_amounts_def
    by (simp split:if_splits add:Let_def; force)
  show "(ra \<noteq> 0 \<or> rb \<noteq> 0) \<longrightarrow> a*rb = b*ra"
    using assms unfolding deposit_amounts_def
    by (simp split:if_splits add:Let_def; force)
  show "(ra = 0 \<and> rb = 0) \<longrightarrow> a = da \<and> b = db"
    using assms unfolding deposit_amounts_def
    by (simp split:if_splits add:Let_def; force)
  show "(ra \<noteq> 0 \<and> rb \<noteq> 0) \<longrightarrow> a/ra = b/rb"
    using assms unfolding deposit_amounts_def
    by (simp split:if_splits add:Let_def; force)
qed

definition deposit_amounts_2 where
  "deposit_amounts_2 desired_a min_a desired_b min_b reserve_a reserve_b \<equiv>
    if (reserve_a = 0 \<and> reserve_b = 0)
    then Some (desired_a, desired_b)
    else let amount_b = \<lfloor>(desired_a*reserve_b)/reserve_a\<rfloor> in
      if (amount_b \<le> desired_b)
      then
        if (amount_b < min_b)
        then None
        else Some (desired_a, amount_b)
      else let amount_a = \<lfloor>(desired_b*reserve_a)/reserve_b\<rfloor> in
        if (amount_a > desired_a \<or> amount_a < min_a)
        then None
        else Some (amount_a, desired_b)"

lemma deposit_amounts_2_property:
  assumes "da \<ge> (0::real)" and "db \<ge> 0" and "ma \<ge> 0" and "mb \<ge> 0" and "ra \<ge> a" and "rb \<ge> 0"
    and "ma \<le> da" and "mb \<le> db"
    and "deposit_amounts_2 da ma db mb ra rb = Some (a, b)"
  shows "ma \<le> a" and "mb \<le> b" and "a \<le> da" and "b \<le> db"
    and "(ra = 0 \<and> rb = 0) \<longrightarrow> a = da \<and> b = db"
    and "(ra \<noteq> 0 \<and> rb \<noteq> 0) \<longrightarrow> ((b/rb \<le> a/ra \<and> a/ra \<le> b/rb + 1) \<or> (a/ra \<le> b/rb \<and> b/rb \<le> a/ra + 1))"
proof -
  show "ma \<le> a"
    using assms unfolding deposit_amounts_2_def
    by (simp split:if_splits add:Let_def; force)
  show "mb \<le> b"
    using assms unfolding deposit_amounts_2_def
    by (simp split:if_splits add:Let_def; force)
  show "a \<le> da"
    using assms unfolding deposit_amounts_2_def
    by (simp split:if_splits add:Let_def; force)
  show "b \<le> db"
    using assms unfolding deposit_amounts_2_def
    by (simp split:if_splits add:Let_def; force)
  show "(ra = 0 \<and> rb = 0) \<longrightarrow> a = da \<and> b = db"
    using assms unfolding deposit_amounts_2_def
    by (simp split:if_splits add:Let_def; force)
  show "(ra \<noteq> 0 \<and> rb \<noteq> 0) \<longrightarrow> ((b/rb \<le> a/ra \<and> a/ra \<le> b/rb + 1) \<or> (a/ra \<le> b/rb \<and> b/rb \<le> a/ra + 1))"
    using assms unfolding deposit_amounts_2_def
    apply (simp split:if_splits add:Let_def)
    apply (smt (verit, del_insts) floor_divide_real_eq_div floor_of_int nonzero_mult_div_cancel_right of_int_floor_le of_int_pos real_of_int_div3 times_divide_eq_left)
    apply (smt (verit) eq_divide_imp floor_divide_of_int_eq floor_divide_real_eq_div floor_le_zero floor_less_zero le_divide_eq_1_pos of_int_floor_le of_int_pos real_of_int_floor_add_one_ge times_divide_eq_left)
    done
qed