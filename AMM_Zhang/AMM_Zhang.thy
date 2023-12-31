theory AMM_Zhang
  imports HOL.Real
begin

text \<open>This is an attempt at translating the AMM formalization of Zhang et al. 
@{url "https://github.com/runtimeverification/verified-smart-contracts/blob/uniswap/uniswap/x-y-k.pdf"} in Isabelle/HOL\<close>

text \<open>We formalize a basic constant-product liquidity pool.
We define an add-liquidity and a remove-liquidity operation on a pool whose token amounts are reals.
We also define the code versions of those operations, where amounts are rounded to obtain integers.
Rounding the wrong way can allow an attacker to drain the pool.
We would like to prove that this cannot happen.\<close>

section "Pool state"

record pool_state =
  \<comment> \<open>A liquidity pool between tokens x and y; l is the token representing pool shares\<close>
  x :: real
  y :: real
  l :: real

definition k where "k p \<equiv> (x p)*(y p)"

section "Adding liquidity"

definition add_liquidity_spec where
  "add_liquidity_spec p \<Delta>x \<equiv> let \<alpha> = \<Delta>x / x p
    in \<lparr>x = (1+\<alpha>)*(x p), y = (1+\<alpha>)*(y p), l = (1+\<alpha>)*(l p)\<rparr>"

definition add_liquidity_code_spec where
  "add_liquidity_code_spec p \<Delta>x \<equiv>
    \<lparr>x = x p + \<Delta>x,
     y = y p + \<lfloor>\<Delta>x*(y p) / x p\<rfloor> + 1, \<comment> \<open>note we need to round in favor of the pool or the pool can be drained\<close>
     l = l p + \<lfloor>\<Delta>x*(l p) / x p\<rfloor>\<rparr>"

lemma l1:"(1 + \<Delta>x / x p) * a = a + \<Delta>x * a / x p" for a
  \<comment> \<open>this simple lemma helps automated provers a lot\<close>
  by algebra

lemma add_liquidity_properties:  
  \<comment> \<open>properties of add-liquidity\<close>
  fixes p \<Delta>x
  assumes "x p > 0" and "y p > 0" and "l p > 0"
    and "\<Delta>x \<ge> 0"
  defines "p' \<equiv> add_liquidity_spec p \<Delta>x"
    and "p'' \<equiv> add_liquidity_code_spec p \<Delta>x"
  shows "x p \<le> x p'" and "x p' = x p''"
    and "y p \<le> y p'" and "y p' < y p''" and "y p'' \<le> y p' + 1"
    and "l p' - 1 < l p''" and "l p'' \<le> l p'" and "l p \<le> l p''" and "l p \<le> l p'"
    and "k p \<le> k p'" and "k p' < k p''"
    and "k p'/k p = (l p'/l p)\<^sup>2"
    and "(l p''/l p)\<^sup>2 < k p''/k p"
    and "x p / l p = x p' / l p'"
    and "y p / l p = y p' / l p'"
proof -
  show "x p \<le> x p'"
    by (smt (verit) add_liquidity_spec_def assms(1) assms(4) divide_nonneg_pos eq_divide_imp ext_inject le_divide_eq_1 p'_def surjective)
  show "x p' = x p''"
    using assms(1-4) unfolding p'_def p''_def add_liquidity_spec_def add_liquidity_code_spec_def Let_def
    by (auto; metis add_divide_distrib eq_divide_eq_1 nonzero_eq_divide_eq order_less_irrefl)
  show "y p \<le> y p'"
    by (smt (verit, del_insts) add_liquidity_spec_def assms(1) assms(2) assms(4) divide_nonneg_pos l1 p'_def select_convs(2) split_mult_pos_le)
  show "y p' < y p''"
    by (simp add: add_liquidity_code_spec_def add_liquidity_spec_def l1 p''_def p'_def)
  show "y p'' \<le> y p' + 1"
    by (simp add: add_liquidity_code_spec_def add_liquidity_spec_def l1 p''_def p'_def)
  show "l p' - 1 < l p''"
    by (simp add: add_liquidity_code_spec_def add_liquidity_spec_def l1 p''_def p'_def) 
  show "l p'' \<le> l p'"
    by (simp add: add_liquidity_code_spec_def add_liquidity_spec_def l1 p''_def p'_def)
  show "l p \<le> l p''"
    by (smt (verit) add_liquidity_code_spec_def assms(1) assms(3) assms(4) divide_nonneg_pos of_int_0_le_iff p''_def select_convs(3) split_mult_pos_le zero_le_floor)
  show "l p \<le> l p'"
    using \<open>l p \<le> l p''\<close> \<open>l p'' \<le> l p'\<close> by force
  show "k p \<le> k p'"
    by (smt (verit, ccfv_SIG) \<open>x p \<le> x p'\<close> \<open>y p \<le> y p'\<close> add_liquidity_spec_def assms(1) assms(2) k_def mult.left_commute mult_le_less_imp_less nonzero_mult_div_cancel_right p'_def select_convs(1) select_convs(2) times_divide_eq_right)
  show "k p' < k p''"
    by (metis \<open>x p \<le> x p'\<close> \<open>x p' = x p''\<close> \<open>y p' < y p''\<close> assms(1) dual_order.strict_trans1 k_def mult_less_cancel_left_pos) 
  show "k p'/k p = (l p'/l p)\<^sup>2"
    using assms(1-4) unfolding p'_def add_liquidity_spec_def Let_def k_def
    by (simp; algebra)
  show "(l p''/l p)\<^sup>2 < k p''/k p"
  proof -
    have "((l p + \<lfloor>\<Delta>x * l p / x p\<rfloor>) / l p)\<^sup>2 \<le> ((l p + \<Delta>x * l p / x p) / l p)\<^sup>2"
    proof -
      have "((l p + \<lfloor>\<Delta>x * l p / x p\<rfloor>) / l p) \<le> ((l p + \<Delta>x * l p / x p) / l p)"
        by (simp add: assms(3) pos_le_divide_eq)
      thus ?thesis
        using assms(1,3,4) by fastforce
    qed
    moreover
    have "(x p + \<Delta>x) * (y p + \<lfloor>\<Delta>x * y p / x p\<rfloor> + 1) / (x p * y p)
          > (x p + \<Delta>x) * (y p + \<Delta>x * y p / x p) / (x p * y p)"
      by (smt (verit) assms(1) assms(2) assms(4) divide_strict_right_mono less_floor_iff mult_pos_pos mult_strict_left_mono)
    ultimately
    show ?thesis
      by (smt (verit, best) \<open>k p' / k p = (l p' / l p)\<^sup>2\<close> \<open>k p' < k p''\<close> add_liquidity_code_spec_def add_liquidity_spec_def assms(1,2) divide_le_cancel k_def l1 p''_def p'_def select_convs(3) split_mult_pos_le)
  qed
  show "x p / l p = x p' / l p'"
    by (smt (verit, del_insts) \<open>x p \<le> x p'\<close> add_liquidity_spec_def assms(1) divide_pos_pos nonzero_eq_divide_eq nonzero_mult_divide_mult_cancel_left p'_def select_convs(1) select_convs(3))
  show "y p / l p = y p' / l p'"
    by (smt (verit, ccfv_threshold) \<open>y p \<le> y p'\<close> add_liquidity_spec_def assms(2) divide_eq_0_iff nonzero_eq_divide_eq nonzero_mult_divide_mult_cancel_left p'_def select_convs(2) select_convs(3))
qed

section "Removing liquidity"

definition remove_liquidity_spec where
  "remove_liquidity_spec p \<Delta>l \<equiv> let \<alpha> = \<Delta>l / l p
    in \<lparr>x = (1-\<alpha>)*(x p), y = (1-\<alpha>)*(y p), l = (1-\<alpha>)*(l p)\<rparr>"

definition remove_liquidity_code_spec where
  "remove_liquidity_code_spec p \<Delta>l \<equiv>
    \<lparr>x = x p - \<lfloor>\<Delta>l*(x p) / l p\<rfloor>,
     y = y p - \<lfloor>\<Delta>l*(y p) / l p\<rfloor>,
     l = l p - \<Delta>l\<rparr>"

lemma l2:"(1 - \<Delta>l / l p) * a = a - \<Delta>l * a / l p" for a
    \<comment> \<open>this simple lemma helps automated provers a lot\<close>
  by algebra

lemma remove_liquidity_properties:
  \<comment> \<open>properties of remove-liquidity\<close>
  fixes p \<Delta>l
  assumes "x p > 0" and "y p > 0" and "l p > 0"
    and "\<Delta>l < l p" and "0 \<le> \<Delta>l"
  defines "p' \<equiv> remove_liquidity_spec p \<Delta>l"
    and "p'' \<equiv> remove_liquidity_code_spec p \<Delta>l"
  shows "x p' \<le> x p" and "x p' \<le> x p''"
    and "y p' \<le> y p" and "y p' \<le> y p''"
    and "l p' = l p''" and "l p' \<le> l p"
    and "k p' \<le> k p''" and "k p' \<le> k p"
    and "k p'/k p = (l p'/l p)\<^sup>2"
    and "(l p''/l p)\<^sup>2 \<le> k p''/k p"
    and "x p / l p = x p' / l p'"
    and "y p / l p = y p' / l p'"
proof -
  show "x p' \<le> x p"
    by (smt (verit, del_insts) assms(1) assms(3) assms(5) divide_divide_eq_right divide_eq_0_iff divide_nonneg_pos l2 p'_def remove_liquidity_spec_def select_convs(1))
  show "x p' \<le> x p''"
    by (simp add: assms(7) l2 p'_def remove_liquidity_code_spec_def remove_liquidity_spec_def)
  show "y p' \<le> y p"
    by (smt (verit, ccfv_SIG) assms(2) assms(3) assms(5) divide_nonneg_pos l2 p'_def remove_liquidity_spec_def select_convs(2) split_mult_pos_le)
  show "y p' \<le> y p''"
    by (simp add: l2 p''_def p'_def remove_liquidity_code_spec_def remove_liquidity_spec_def)
  show "l p' = l p''"
    by (metis assms(3) l2 nonzero_mult_div_cancel_right not_less_iff_gr_or_eq p''_def p'_def pool_state.select_convs(3) remove_liquidity_code_spec_def remove_liquidity_spec_def)
  show "l p' \<le> l p"
    by (simp add: \<open>l p' = l p''\<close> assms(5) p''_def remove_liquidity_code_spec_def)
  show "k p' \<le> k p"
    by (smt (verit) \<open>x p' \<le> x p\<close> \<open>y p' \<le> y p\<close> assms(1) assms(2) assms(3) assms(4) divide_less_eq_1_pos k_def mult_less_cancel_left_pos mult_less_iff1 mult_pos_pos p'_def remove_liquidity_spec_def select_convs(2))
  show "k p' \<le> k p''"
    by (smt (verit) \<open>x p' \<le> x p''\<close> \<open>y p' \<le> y p''\<close> assms(1) assms(2) assms(3) assms(4) divide_less_eq_1_pos k_def mult.commute mult_less_cancel_left_pos mult_pos_pos p'_def pool_state.select_convs(1) pool_state.select_convs(2) remove_liquidity_spec_def)
  show "k p'/k p = (l p'/l p)\<^sup>2"
    by (smt (verit, ccfv_SIG) ab_semigroup_mult_class.mult_ac(1) assms(1) assms(2) assms(3) k_def mult.left_commute mult_pos_pos nonzero_eq_divide_eq p'_def power2_eq_square remove_liquidity_spec_def select_convs(1) select_convs(2) select_convs(3))
  show "(l p''/l p)\<^sup>2 \<le> k p''/k p"
    by (metis \<open>k p' / k p = (l p' / l p)\<^sup>2\<close> \<open>k p' \<le> k p''\<close> \<open>l p' = l p''\<close> assms(1) assms(2) divide_right_mono k_def less_le_not_le split_mult_pos_le)
  show "x p / l p = x p' / l p'"
    by (smt (verit) assms(4) divide_divide_eq_right eq_divide_eq_1 mult.commute nonzero_mult_div_cancel_left p'_def remove_liquidity_spec_def select_convs(1) select_convs(3))
  show "y p / l p = y p' / l p'"
    by (smt (verit, best) \<open>x p / l p = x p' / l p'\<close> assms(1) divide_divide_eq_left divide_eq_0_iff nonzero_mult_div_cancel_left p'_def remove_liquidity_spec_def select_convs(2) select_convs(3))
qed

section "No free money"

text \<open>Here we want to prove that, no matter what sequence of operations one applies,
withdrawing all the liquidity obtained leaves the pool with at least the same amount of tokens it started from.
We could formalize executions as lists, inductive invariants, etc.\<close>

definition inv where
  "inv p\<^sub>0 p \<equiv> l p \<ge> l p\<^sub>0 \<and> (
    let p' = remove_liquidity_spec p (l p - l p\<^sub>0)
    in x p' = x p\<^sub>0 \<and> y p' = y p\<^sub>0)"

definition pool_ne where
  \<comment> \<open>non-empty pool\<close>
  "pool_ne p \<equiv> x p > 0 \<and> y p > 0 \<and> l p > 0"

lemma l3:
  \<comment> \<open>if the ratio x to l is the same as x' to l', then removing liquidity l' minus l results in balance x\<close>
  fixes x l x' l' :: real
  assumes "x/l = x'/l'" and "l>0" and "x>0"
  shows "x'*(1-(l'-l)/l') = x"
  by (metis (no_types, opaque_lifting) add.right_neutral add_diff_cancel assms diff_diff_eq diff_divide_distrib divide_divide_eq_right divide_eq_0_iff eq_divide_eq_1 minus_diff_eq mult_1 nonzero_eq_divide_eq order_less_irrefl times_divide_eq_left)   

lemma l4:
  fixes p\<^sub>0 p
  assumes "inv p\<^sub>0 p" and "pool_ne p\<^sub>0" and "pool_ne p"
  shows "x p / l p = x p\<^sub>0 / l p\<^sub>0" and "y p / l p = y p\<^sub>0 / l p\<^sub>0"
proof -
  define \<Delta>l where "\<Delta>l \<equiv> l p - l p\<^sub>0"
  define p' where "p' \<equiv> remove_liquidity_spec p \<Delta>l"
  have 1:"l p\<^sub>0 = l p'"
  proof -
    have "(1 - (x' - x)/x')*x' = x" if "x' \<noteq> 0" for x x' :: real
      by (simp add: diff_divide_distrib that)
    thus ?thesis
      unfolding p'_def remove_liquidity_spec_def Let_def
      by (metis \<Delta>l_def assms(3) order_less_irrefl pool_ne_def select_convs(3))
  qed
  have 2:"\<Delta>l \<ge> 0"
    using AMM_Zhang.inv_def \<Delta>l_def assms(1) by auto
  have 3:"\<Delta>l < l p"
    using \<Delta>l_def assms(2) pool_ne_def by auto
  show "x p / l p = x p\<^sub>0 / l p\<^sub>0"
  proof -
    have "x p / l p = x p' / l p'"
      using "2" "3" assms(3) p'_def pool_ne_def remove_liquidity_properties(11) by blast
    thus ?thesis using 1
      by (metis AMM_Zhang.inv_def \<Delta>l_def assms(1) p'_def)
  qed
  show "y p / l p = y p\<^sub>0 / l p\<^sub>0"
  proof -
    have "y p / l p = y p' / l p'"
      using "2" "3" assms(3) p'_def pool_ne_def remove_liquidity_properties(12) by blast
    thus ?thesis using 1
      by (metis AMM_Zhang.inv_def \<Delta>l_def assms(1) p'_def) 
  qed
qed

lemma l5:
  fixes p\<^sub>0 p p' \<Delta>x
  assumes "inv p\<^sub>0 p" and "l p' \<ge> l p\<^sub>0" and "pool_ne p\<^sub>0" and "pool_ne p"
    and "x p' / l p' = x p / l p" and "y p' / l p' = y p / l p"
  shows "inv p\<^sub>0 p'"
proof -
  have "l p \<ge> l p\<^sub>0"
    using inv_def assms(1)
    by blast
  define p'' where "p'' \<equiv> remove_liquidity_spec p' (l p' - l p\<^sub>0)"
  have "x p\<^sub>0 / l p\<^sub>0 =  x p' / l p'"
    using \<open>l p\<^sub>0 \<le> l p\<close> assms(1) assms(3) assms(4) assms(5) l4(1) by fastforce
  hence "x p\<^sub>0 = x p''" using l3 unfolding p''_def remove_liquidity_spec_def Let_def
    by (metis assms(3) mult.commute pool_ne_def select_convs(1))
  have "y p\<^sub>0 / l p\<^sub>0 =  y p' / l p'"
    using \<open>l p\<^sub>0 \<le> l p\<close> assms(1) assms(3) assms(4) assms(6) l4(2) by fastforce
  hence "y p\<^sub>0 = y p''" using l3 unfolding p''_def remove_liquidity_spec_def Let_def
    by (metis assms(3) mult.commute pool_ne_def select_convs(2))
  show ?thesis
    using AMM_Zhang.inv_def \<open>x p\<^sub>0 = x p''\<close> \<open>y p\<^sub>0 = y p''\<close> assms(2) p''_def by fastforce
qed

lemma inv_add_okay:
  fixes p\<^sub>0 p p' \<Delta>x
  assumes "inv p\<^sub>0 p" and "0 \<le> \<Delta>x" and "pool_ne p\<^sub>0" and "pool_ne p"
  defines "p' \<equiv> add_liquidity_spec p \<Delta>x"
  shows "inv p\<^sub>0 p'"
proof -
  have "x p' / l p' = x p / l p" and "y p' / l p' = y p / l p"
    by (metis add_liquidity_properties(14) assms(2) assms(4) p'_def pool_ne_def
    , metis add_liquidity_properties(15) assms(2) assms(4) p'_def pool_ne_def)
  moreover
  have "l p' \<ge> l p"
    using add_liquidity_properties(9) assms(2) assms(4) p'_def pool_ne_def by blast
  moreover
  have "l p \<ge> l p\<^sub>0"
    using AMM_Zhang.inv_def assms(1) by blast
  ultimately show ?thesis using l5
    using assms(1) assms(3) assms(4) order_trans by blast
qed

lemma inv_rem_okay:
  fixes p\<^sub>0 p p' \<Delta>l
  defines "p' \<equiv> remove_liquidity_spec p \<Delta>l"
  assumes "inv p\<^sub>0 p" and "0 \<le> \<Delta>l" and "pool_ne p\<^sub>0" and "pool_ne p" and "l p\<^sub>0 < l p'"
  shows "inv p\<^sub>0 p'"
proof -
  have "x p' / l p' = x p / l p" and "y p' / l p' = y p / l p"
     apply (smt (verit, best) assms(4) assms(6) nonzero_mult_divide_mult_cancel_left p'_def pool_ne_def remove_liquidity_spec_def select_convs(1) select_convs(3) zero_less_mult_iff)
    apply (smt (verit) assms(4) assms(6) divide_divide_eq_left divide_eq_0_iff nonzero_mult_div_cancel_left p'_def pool_ne_def remove_liquidity_spec_def select_convs(2) select_convs(3))
    done
  thus?thesis using l5
    by (metis assms(2) assms(4) assms(5) assms(6) less_le_not_le)
qed

end