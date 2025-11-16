theory HSV_tasks_2025 imports Main begin

section \<open> Task 1: Assessing the efficiency of a logic synthesiser. \<close>

text \<open> A datatype representing simple circuits. \<close>

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open> An optimisation that removes two successive NOT gates. \<close>

fun opt_NOT where
  "opt_NOT (NOT (NOT c)) = opt_NOT c"
| "opt_NOT (NOT c) = NOT (opt_NOT c)"
| "opt_NOT (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT TRUE = TRUE"
| "opt_NOT FALSE = FALSE"
| "opt_NOT (INPUT i) = INPUT i"

text \<open> A function that counts the number of gates in a circuit. \<close>

fun area :: "circuit \<Rightarrow> nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

text \<open> A function that estimates the computational "cost" of the opt_NOT function. \<close>

fun cost_opt_NOT :: "circuit \<Rightarrow> nat" where
  "cost_opt_NOT (NOT (NOT c)) = 1 + cost_opt_NOT c"
| "cost_opt_NOT (NOT c) = 1 + cost_opt_NOT c"
| "cost_opt_NOT (AND c1 c2) = 1 + cost_opt_NOT c1 + cost_opt_NOT c2"
| "cost_opt_NOT (OR c1 c2) = 1 + cost_opt_NOT c1 + cost_opt_NOT c2"
| "cost_opt_NOT TRUE = 1"
| "cost_opt_NOT FALSE = 1"
| "cost_opt_NOT (INPUT _) = 1"

text \<open> opt_NOT has complexity O(n) where n is the input circuit's area. \<close>

theorem opt_NOT_linear: "\<exists> a b ::nat. cost_opt_NOT c \<le> a * area c + b"
  using le_add2 by blast



text \<open> Another optimisation, introduced in the 2021 coursework. This
  optimisation exploits identities like `(a | b) & (a | c) = a | (b & c)` 
  in order to remove some gates. \<close>

fun factorise :: "circuit \<Rightarrow> circuit" where
  "factorise (NOT c) = NOT (factorise c)"
| "factorise (AND (OR c1 c2) (OR c3 c4)) = (
    let c1' = factorise c1; c2' = factorise c2; c3' = factorise c3; c4' = factorise c4 in
    if c1' = c3' then OR c1' (AND c2' c4') 
    else if c1' = c4' then OR c1' (AND c2' c3') 
    else if c2' = c3' then OR c2' (AND c1' c4') 
    else if c2' = c4' then OR c2' (AND c1' c3') 
    else AND (OR c1' c2') (OR c3' c4'))"
| "factorise (AND c1 c2) = AND (factorise c1) (factorise c2)"
| "factorise (OR c1 c2) = OR (factorise c1) (factorise c2)"
| "factorise TRUE = TRUE"
| "factorise FALSE = FALSE"
| "factorise (INPUT i) = INPUT i"

text \<open> A function that estimates the computational "cost" of the factorise function. \<close>

fun cost_factorise :: "circuit \<Rightarrow> nat" where
  "cost_factorise (NOT c) = 1 + cost_factorise c"
| "cost_factorise (AND (OR c1 c2) (OR c3 c4)) = 
   4 + cost_factorise c1 + cost_factorise c2 + cost_factorise c3 + cost_factorise c4"
| "cost_factorise (AND c1 c2) = 1 + cost_factorise c1 + cost_factorise c2"
| "cost_factorise (OR c1 c2) = 1 + cost_factorise c1 + cost_factorise c2"
| "cost_factorise TRUE = 1"
| "cost_factorise FALSE = 1"
| "cost_factorise (INPUT i) = 1"

text \<open> factorise has complexity O(n) where n is the input circuit's area. \<close>

theorem factorise_linear: "\<exists> a b ::nat. cost_factorise c \<le> a * area c + b"
  using le_add2 by blast

section \<open> Task 2: Palindromic numbers. \<close>

fun sum10 :: "nat list \<Rightarrow> nat"
where
  "sum10 [] = 0"
| "sum10 (d # ds) = d + 10 * sum10 ds"

value "sum10 [4,2,3]"

text \<open> Rephrasing the definition of sum10 so that elements 
  are peeled off the _end_ of the list, not the start. \<close>

lemma sum10_snoc:
  "sum10 (ds @ [d]) =  d * (10^ length ds) + sum10 ds "
proof (induction ds)
  case Nil
  show ?case by simp
next 
  case (Cons a ds)
  show ?case
    using local.Cons by force
qed

text \<open> If ds is a palindrome of even length, then the number it represents is divisible by 11. \<close>

lemma pow10_plus1_dvd11:
  fixes n :: nat
  shows "11 dvd (x + x * (10 ^ (2 * n + 1)::nat))"
proof -
have "x + x * (10 ^ (2 * n + 1)::nat) = x * (1 + 10 ^ (2 * n + 1)::nat)"
  by simp
  then show ?thesis
proof (induction n arbitrary: x)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  thm Suc
  term ?case
  have "x + x * (10 ^ (2 * n + 1)::nat) = x * (1 + 10 ^ (2 * n + 1)::nat)"
    by simp
  then have "11 dvd (x + x * 10 ^ (2 * n + 1))" by fact 
  have "(10^(2* Suc n + 1) + 1::nat) = (10^(2*n+3) + 1::nat)" 
    by (metis Suc3_eq_add_3 Suc_eq_plus1 add.commute add_Suc mult_2)
  then have "... = (10 ^ (2 + (2*n+1)) + 1::nat)"
    by (simp add: numeral_3_eq_3)
  then have "... = ((10^2) * (10^(2*n+1)) + 1::nat)"
  by simp
  then have "... = (99) * (10^(2*n+1)::nat) + (10^(2*n+1) + 1::nat)"
    by simp
  then have "11 dvd (99) * (10^(2*n+1)::nat)"
    by simp
  then have "1 + 1 * 10 ^ (2 * n + 1::nat) = 1 * (1 + 10 ^ (2 * n + 1)::nat)" 
    by simp
  then have "11 dvd (1 + 1 * (10 ^ (2 * n + 1)::nat))"
    using Suc.IH \<open>1 + 1 * 10 ^ (2 * n + 1) = 1 * (1 + 10 ^ (2 * n + 1))\<close> by blast
  thus ?case
    by (metis Suc.prems \<open>10 ^ (2 * Suc n + 1) + 1 = 10 ^ (2 * n + 3) + 1\<close> \<open>10 ^ (2 * n + 3) + 1 = 10 ^ (2 + (2 * n + 1)) + 1\<close>
        \<open>10 ^ (2 + (2 * n + 1)) + 1 = 10\<^sup>2 * 10 ^ (2 * n + 1) + 1\<close> \<open>10\<^sup>2 * 10 ^ (2 * n + 1) + 1 = 99 * 10 ^ (2 * n + 1) + (10 ^ (2 * n + 1) + 1)\<close>
        \<open>11 dvd 99 * 10 ^ (2 * n + 1)\<close> add.commute dvd_add dvd_mult lambda_one)
  qed
qed

 

theorem half_proof: 
  shows "11 dvd (sum10 (hs @ rev hs))"
proof (induction hs)
  case Nil
  then show ?case try
    by simp
next
  case (Cons d hs)
  have "sum10 ((d # hs) @ rev (d # hs)) = 10 * sum10 (hs @ (rev hs)) + d * (10 ^ (2* length hs + 1) + 1)" 
  by (smt (z3) ab_semigroup_add_class.add_ac(1) ab_semigroup_mult_class.mult_ac(1)
      add.commute add.left_commute add_mult_distrib append.assoc append_Nil length_append
      length_rev mult.commute mult_2 mult_2_right nat_1_add_1 nat_mult_1 nat_mult_1_right
      numeral_Bit0 numeral_Bit0_eq_double numeral_Bit1_eq_inc_double numerals(1) power_add
      power_one_right rev.simps(1,2) rev_append rev_eq_Cons_iff rev_rev_ident
      sum10.simps(2) sum10_snoc) 
  then show ?case
    by (metis add.commute dvd_add dvd_mult2 local.Cons mult.commute mult_numeral_1 numeral_One pow10_plus1_dvd11)
qed



theorem dvd11: 
  assumes "even (length ds)"
  assumes "ds = rev ds"
  shows "11 dvd (sum10 ds)"
proof -
  obtain hs where "ds = hs @ rev hs" and "length hs = length ds div 2"
  proof -
    let ?hs = "take (length ds div 2) ds"
    have "ds = ?hs @ drop (length ds div 2) ds" by simp
    moreover have "drop (length ds div 2) ds = rev ?hs"
    proof -
      have "length ds = 2 * (length ds div 2)" using assms(1) by simp
      then have "drop (length ds div 2) ds = rev (take (length ds div 2) ds)"
        using assms(2) 
        by (metis add_diff_cancel_left' mult_2 rev_take)
      thus ?thesis by simp
    qed
    moreover have "length ?hs = length ds div 2" by simp
    ultimately show ?thesis using that 
    by simp
  qed
  
  from `ds = hs @ rev hs` and half_proof show ?thesis by simp
qed

  





section \<open> Task 3: 3SAT reduction. \<close>

text \<open> We shall use integers to represent symbols. \<close>
type_synonym symbol = "nat"

text \<open> A literal is either a symbol or a negated symbol. \<close>
type_synonym literal = "symbol * bool"

text \<open> A clause is a disjunction of literals. \<close>
type_synonym clause = "literal list"

text \<open> A SAT query is a conjunction of clauses. \<close>
type_synonym query = "clause list"

text \<open> A valuation is a function from symbols to truth values. \<close>
type_synonym valuation = "symbol \<Rightarrow> bool"

text \<open> Given a valuation, evaluate a literal to its truth value. \<close>
fun evaluate_literal :: "valuation \<Rightarrow> literal \<Rightarrow> bool"
where 
  "evaluate_literal \<rho> (x,b) = (\<rho> x = b)"

text \<open> Given a valuation, evaluate a clause to its truth value. \<close>
definition evaluate_clause :: "valuation \<Rightarrow> clause \<Rightarrow> bool"
where 
  "evaluate_clause \<rho> c \<equiv> \<exists>l \<in> set c. evaluate_literal \<rho> l"

text \<open> Given a valuation, evaluate a query to its truth value. \<close>
definition evaluate :: "query \<Rightarrow> valuation \<Rightarrow> bool"
where 
  "evaluate q \<rho> \<equiv> \<forall>c \<in> set q. evaluate_clause \<rho> c"

text \<open> Checks whether a query is in 3SAT form; i.e. no clause has more than 3 literals. \<close>
definition is_3SAT :: "query \<Rightarrow> bool"
where[simp]:
  "is_3SAT q \<equiv> \<forall>c \<in> set q. length c \<le> 3"

text \<open> Converts a clause into an equivalent sequence of 3SAT clauses. The 
       parameter x is the next symbol number to use whenever a fresh symbol 
       is required. It should be greater than every symbol that appears in c.
       When the function returns, it returns a new value for this parameter
       that may have been increased as a result of adding new symbols; the 
       function guarantees that the new value is still greater than every
       symbol that appears in sequence of reduced clauses. \<close>

fun reduce_clause :: "symbol \<Rightarrow> clause \<Rightarrow> (symbol * query)"
where
  "reduce_clause x (l1 # l2 # l3 # l4 # c) = 
  (let (x',cs) = reduce_clause (x+1) ((x, False) # l3 # l4 # c) in
  (x', [[(x, True), l1, l2]] @ cs))"
| "reduce_clause x c = (x, [c])"

value "reduce_clause 3 [(0, True), (1, False), (2, True)]"
value "reduce_clause 4 [(0, True), (1, False), (2, True), (3, False)]"
value "reduce_clause 5 [(0, True), (1, False), (2, True), (3, False), (4, True)]"

text \<open> Converts a SAT query into a 3SAT query. The parameter x is the next
       symbol number to use whenever a fresh symbol is required. It should
       be greater than every symbol that appears in q. We shall sometimes
       write "reduction of q at x". \<close>
fun reduce :: "symbol \<Rightarrow> query \<Rightarrow> query"
where
  "reduce _ [] = []"
| "reduce x (c # q) = (let (x',cs) = reduce_clause x c in cs @ reduce x' q)"

text \<open> "x \<triangleright> q" holds if all the symbols in q are below x.  \<close>
definition all_below :: "nat \<Rightarrow> query \<Rightarrow> bool" (infix "\<triangleright>" 50)
where [simp]:
  "x \<triangleright> q \<equiv> \<forall>c \<in> set q. \<forall>(y,_) \<in> set c. y<x"

definition "q_example \<equiv> [[(0,True), (1,True), (2,True), (3,False)], [(1,False), (2,True)]]"

value "3 \<triangleright> q_example"
value "4 \<triangleright> q_example"

value "reduce 4 q_example"

text \<open> The constant-False valuation satisfies q_example... \<close>
value "evaluate q_example (\<lambda>_. False)"

text \<open> ...but it doesn't satisfy the reduced version of q_example. \<close>
value "evaluate (reduce 4 q_example) (\<lambda>_. False)"

text \<open> Extract the symbol from a given literal. \<close>
fun symbol_of_literal :: "literal \<Rightarrow> symbol"
where
  "symbol_of_literal (x, _) = x"

text \<open> Extract the set of symbols that appear in a given clause. \<close>
definition symbols_clause :: "clause \<Rightarrow> symbol set"
where 
  "symbols_clause c \<equiv> set (map symbol_of_literal c)"

text \<open> Extract the set of symbols that appear in a given query. \<close>
definition symbols :: "query \<Rightarrow> symbol set"
where
  "symbols q \<equiv> \<Union> (set (map symbols_clause q))"


text \<open> (New) making a query from 3SAT clauses is 3SAT. \<close>
lemma query_3SAT_closed:
  "is_3SAT A \<and> is_3SAT B \<Longrightarrow> is_3SAT (A @ B)"
  by auto

lemma is_3SAT_reduce_clause:
  "is_3SAT (snd (reduce_clause x c))" 
proof (induction c rule: reduce_clause.induct)
  print_cases
  case (1 x l1 l2 l3 l4 c)
  have S:  "snd (reduce_clause x (l1 # l2 # l3 # l4 # c)) =
      (let (x',cs) = reduce_clause (x+1) ((x, False) # l3 # l4 # c) in
  [[(x, True), l1, l2]] @ cs)"
    by (smt (verit) prod.case_distrib reduce_clause.simps(1) snd_conv split_cong)
  then have "is_3SAT [[(x, True), l1, l2]]"
    by simp
  then show ?case using S "1.IH" 
    by (metis (no_types, lifting) case_prod_conv old.prod.exhaust query_3SAT_closed
        snd_eqD)
next
  case ("2_1" x)
  then show ?case
    by simp
next
  case ("2_2" x v)
  then show ?case 
    by simp
next
  case ("2_3" x v vb)
  then show ?case 
    by simp
next
  case ("2_4" x v vb vd)
  then show ?case 
    by simp
qed


text \<open> The reduce function really does return queries in 3SAT form. \<close>
theorem is_3SAT_reduce:
  "is_3SAT (reduce x q)" 
proof (induction q rule: reduce.induct)
  print_cases
  case (1 uu)
  then show ?case 
    by simp
next
  case (2 x c q)
  then show ?case 
    by (metis (no_types, lifting) case_prod_conv is_3SAT_reduce_clause query_3SAT_closed
        reduce.simps(2) snd_eqD surj_pair)
qed

lemma reduce_clause_nonempty:
 "length (snd (reduce_clause x c)) \<ge> 1"
proof (induction c rule: reduce_clause.induct)
  print_cases
  case (1 x l1 l2 l3 l4 c)
  obtain x' cs where RC: "reduce_clause (x+1) ((x, False) # l3 # l4 # c) = (x', cs)"
    by (metis surj_pair)
  have IH: "length (snd (reduce_clause (x+1) ((x, False) # l3 # l4 # c))) \<ge> 1"
    using "1.IH" by try
  then have "length cs \<ge> 1" 
    using RC by simp
  moreover have "snd (reduce_clause x (l1 # l2 # l3 # l4 # c)) = [[(x, True), l1, l2]] @ cs"
    using RC by simp
  ultimately show ?case by simp
next
  case ("2_1" x)
  then show ?case sorry
next
  case ("2_2" x v)
  then show ?case sorry
next
  case ("2_3" x v vb)
  then show ?case sorry
next
  case ("2_4" x v vb vd)
  then show ?case sorry
qed

text \<open> The reduce function never decreases the number of clauses in a query. \<close>
theorem "length q \<le> length (reduce x q)"
proof (induction q rule: reduce.induct)
  case (1 uu)
  then show ?case
    by simp
next
  case (2 x c q)
  then show ?case try
qed

definition "satisfiable q \<equiv> \<exists>\<rho>. evaluate q \<rho>"

text \<open> If reduce x q is satisfiable, then so is q. \<close>
theorem sat_reduce1:
  assumes "satisfiable (reduce x q)"
  shows "satisfiable q"
  sorry

text \<open> If q is satisfiable, and all the symbols in q are below x, 
  then reduce x q is also satisfiable. \<close>
theorem sat_reduce2:
  assumes "satisfiable q" and "x \<triangleright> q"
  shows "satisfiable (reduce x q)"
  sorry

text \<open> If all symbols in q are below x, then q and its reduction at x are equisatisfiable. \<close>
corollary sat_reduce:
  assumes "x \<triangleright> q"
  shows "satisfiable q = satisfiable (reduce x q)"
  using assms sat_reduce1 sat_reduce2 by blast

end