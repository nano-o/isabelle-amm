theory SorobanAMM
  imports Complex_Main  "HOL-Statespace.StateSpaceSyntax"
begin

sledgehammer_params [timeout=300]

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
    and "(ra+a)*rb = (rb+b)*ra"
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
  show "(ra+a)*rb = (rb+b)*ra"
    by (metis \<open>ra \<noteq> 0 \<or> rb \<noteq> 0 \<longrightarrow> a * rb = b * ra\<close> add_cancel_left_right mult.commute ring_class.ring_distribs(1))
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

definition new_total_shares where
  "new_total_shares old_a new_a old_b new_b old_shares \<equiv>
    if (old_a > 0 \<and> old_b > 0)
    then
      let shares_a = (new_a*old_shares)/old_a;
          shares_b = (new_b*old_shares)/old_b in
      min shares_a shares_b
    else sqrt (new_a*new_b)"

lemma deposit_lemma:
  assumes "da \<ge> (0::real)" and "db \<ge> 0" and "ma \<ge> 0" and "mb \<ge> 0" and "ra \<ge> a" and "rb \<ge> 0"
    and "ma \<le> da" and "mb \<le> db" and "s \<ge> 0" and "(ra = 0) \<longleftrightarrow> (rb = 0)"
    and "deposit_amounts da ma db mb ra rb = Some (a, b)"
    and "new_total_shares ra (ra+a) rb (rb+b) s = ns"
  shows "ra*ns = (ra+a)*s"
  using assms unfolding new_total_shares_def
  apply (simp split:if_splits option.splits add:Let_def split_def)
   apply (smt (verit, best) deposit_amounts_property(8) mult.commute nonzero_eq_divide_eq times_divide_eq_left)
  apply (smt (verit, best) deposit_amounts_property(1) mult_not_zero)
  done

statespace 'addr system =
  reserve_a :: real
  reserve_b :: real
  total_shares :: real
  attacker_shares :: real
  attacker_a :: real
  attacker_b :: real

definition (in system) init where
  "init s \<equiv>
      s\<cdot>reserve_a = 0
    \<and> s\<cdot>reserve_b = 0
    \<and> s\<cdot>total_shares = 0
    \<and> s\<cdot>attacker_shares = 0
    \<and> s\<cdot>attacker_a \<ge> 0
    \<and> s\<cdot>attacker_b \<ge> 0"

definition (in system) deposit where
  "deposit a b ma mb s s' \<equiv>
    a \<ge> 0 \<and> b \<ge> 0 \<and> ma \<le> a \<and> mb \<le> b
    \<and> (s\<cdot>attacker_a) \<ge> a
    \<and> (s\<cdot>attacker_b) \<ge> b
    \<and> (s'\<cdot>attacker_a) = (s\<cdot>attacker_a) - a
    \<and> (s'\<cdot>attacker_b) = (s\<cdot>attacker_b) - b
    \<and> (let amounts = deposit_amounts a ma b mb (s\<cdot>reserve_a) (s\<cdot>reserve_b) in
        (case amounts of
          None \<Rightarrow> False
        | Some (amount_a, amount_b) \<Rightarrow>
              (s'\<cdot>attacker_a) = (s\<cdot>attacker_a) - amount_a
            \<and> (s'\<cdot>attacker_b) = (s\<cdot>attacker_b) - amount_b
            \<and> (let new_a = (s\<cdot>reserve_a)+amount_a;
                   new_b = (s\<cdot>reserve_b)+amount_b;
                   new_shares = shares_to_mint (s\<cdot>reserve_a) new_a (s\<cdot>reserve_b) new_b (s\<cdot>total_shares)
               in
                  (s'\<cdot>reserve_a) = new_a
                \<and> (s'\<cdot>reserve_b) = new_b
                \<and> (s'\<cdot>total_shares) = (s\<cdot>total_shares)+new_shares
                \<and> (s'\<cdot>attacker_shares) = (s\<cdot>attacker_shares)+new_shares)))"

definition (in system) withdraw where
  "withdraw shrs min_a min_b s s' \<equiv>
      (s\<cdot>attacker_shares) \<ge> shrs
    \<and> (s'\<cdot>attacker_shares) = (s\<cdot>attacker_shares)-shrs
    \<and> (s'\<cdot>total_shares) = (s\<cdot>total_shares)-shrs \<comment> \<open>We burn the shares\<close>
    \<and> (let out_a = (shrs*(s\<cdot>reserve_a))/(s\<cdot>total_shares);
           out_b = (shrs*(s\<cdot>reserve_b))/(s\<cdot>total_shares) in
         out_a \<ge> min_a \<and> out_b \<ge> min_b
       \<and> (s'\<cdot>attacker_a) = (s\<cdot>attacker_a)+out_a
       \<and> (s'\<cdot>attacker_b) = (s\<cdot>attacker_b)+out_b
       \<and> (s'\<cdot>reserve_a) = (s\<cdot>reserve_a)-out_a
       \<and> (s'\<cdot>reserve_b) = (s\<cdot>reserve_b)-out_b)"

lemma (in system) deposit_withdraw:
  assumes "deposit a b ma mb s s'" and "withdraw (s'\<cdot>attacker_shares) min_a min_b s' s''"
    and "s\<cdot>attacker_shares = 0" and "s''\<cdot>attacker_shares = 0"
  shows "s''\<cdot>attacker_a \<ge> s\<cdot>attacker_a"
  using assms
  unfolding deposit_def withdraw_def shares_to_mint_def
  apply (simp split:if_splits option.splits add:Let_def split_def)
  apply auto

text \<open>The attacker buys shares and then sells them back in two steps. We want to check that no money is made by the attacker.\<close>
